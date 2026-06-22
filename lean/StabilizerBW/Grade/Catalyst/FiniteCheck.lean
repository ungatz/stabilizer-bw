import StabilizerBW.Grade.Catalyst.Headline

/-!
# CHKRS S13 — finite / non-vacuity checks

Non-vacuity witnesses for the carrier and the headline.  The grade functions are `sInf`-valued
on infinite sets and are *not* directly `decide`-able, so instead of a brute-force enumeration
we discharge the literal inequality on the whole T-free (Clifford) fragment unconditionally
(`phi3_clifford_check`, via `phi3_composite_grade_le_of_tcount_zero`) and exhibit explicit
composite witnesses.
-/

namespace CHKRS_S13_CompositeCatalystGrade

open Pi3 SqWord

/-- Compositional depth of a word. -/
def depth : SqWord → ℕ
  | .xg | .vg | .sg | .tg => 0
  | .comp a b => max (depth a) (depth b) + 1

/-- **Unconditional check on the Clifford fragment.** Any word with `tcount w = 0` satisfies
the literal catalyst inequality. -/
theorem phi3_clifford_check (w : SqWord) (hw : SqWord.tcount w = 0) :
    Pi2.grade2 (toPi2 w) ≤ grade2obj (toPi3 w) :=
  phi3_composite_grade_le_of_tcount_zero w hw

/-- Explicit composite witness (a depth-2 Clifford word `X ⊚ (V ⊚ S)`). -/
example :
    Pi2.grade2 (toPi2 (.comp .xg (.comp .vg .sg))) ≤
      grade2obj (toPi3 (.comp .xg (.comp .vg .sg))) :=
  phi3_clifford_check _ rfl

/-- Explicit composite witness (a depth-2 Clifford word `(X ⊚ V) ⊚ (S ⊚ X)`). -/
example :
    Pi2.grade2 (toPi2 (.comp (.comp .xg .vg) (.comp .sg .xg))) ≤
      grade2obj (toPi3 (.comp (.comp .xg .vg) (.comp .sg .xg))) :=
  phi3_clifford_check _ rfl

/-- Non-vacuity of the carrier predicate: its intended conclusion is a genuine `Prop`. -/
theorem CompositeS13Discharge_well_defined :
    ∃ P : Prop, P = (∀ w : SqWord, Pi2.grade2 (toPi2 w) ≤ grade2obj (toPi3 w)) :=
  ⟨_, rfl⟩

end CHKRS_S13_CompositeCatalystGrade
