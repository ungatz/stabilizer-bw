import StabilizerBW.Grade.Catalyst.GeneratorBaseline
import StabilizerBW.Grade.Catalyst.CompositeCyclotomic

/-!
# CHKRS S13 — headline

The literal composite-level catalyst inequality `grade₂(Φ₃ w) ≤ grade₃ w` for every
single-qubit composite word `w`, **conditional** on the named carrier
`CompositeS13Discharge`.  We also record:

* `subsumes_Headline_T3_general` — the conditional headline subsumes the unconditional
  T-count bound `Pi3.grade2_toPi2_le_tcount` already carried by the corpus.
* `phi3_composite_grade_le_of_tcount_zero` — an **unconditional** partial discharge on the
  T-free (Clifford) fragment `{tcount w = 0}`, which needs no carrier.
-/

namespace CatalystGrade

open Pi3 SqWord

/-- **HEADLINE (conditional).** Under the carrier `CompositeS13Discharge`, the literal
composite-level inequality `grade₂(Φ₃ w) ≤ grade₃ w` holds for every single-qubit word `w`. -/
theorem phi3_composite_grade_le_discharged (h : CompositeS13Discharge) :
    ∀ w : SqWord, Pi2.grade2 (toPi2 w) ≤ grade2obj (toPi3 w) := by
  intro w
  induction w with
  | xg => exact gen_discharged.1
  | vg => exact gen_discharged.2.1
  | sg => exact gen_discharged.2.2.1
  | tg => exact gen_discharged.2.2.2
  | comp a b iha ihb => exact composite_step h a b iha ihb

/-- The conditional headline subsumes the corpus's unconditional T-count bound: under the
carrier, every word satisfies both `grade₂(Φ₃ w) ≤ grade₃ w` and `grade₂(Φ₃ w) ≤ tcount w`. -/
theorem subsumes_Headline_T3_general (h : CompositeS13Discharge) :
    ∀ w : SqWord, Pi2.grade2 (toPi2 w) ≤ grade2obj (toPi3 w) ∧
                  Pi2.grade2 (toPi2 w) ≤ (SqWord.tcount w : ℕ∞) :=
  fun w => ⟨phi3_composite_grade_le_discharged h w, Pi3.grade2_toPi2_le_tcount w⟩

/-- **Unconditional partial discharge on the T-free (Clifford) fragment.** For every word `w`
with `tcount w = 0` (built only from the Clifford generators `X, V, S`), the literal
inequality `grade₂(Φ₃ w) ≤ grade₃ w` holds with **no** carrier: both sides are forced to `0`
by the corpus's T-count bound `Pi3.grade2_toPi2_le_tcount`. -/
theorem phi3_composite_grade_le_of_tcount_zero (w : SqWord) (hw : SqWord.tcount w = 0) :
    Pi2.grade2 (toPi2 w) ≤ grade2obj (toPi3 w) := by
  have h := Pi3.grade2_toPi2_le_tcount w
  rw [hw, Nat.cast_zero] at h
  exact le_trans h (zero_le _)

end CatalystGrade
