import StabilizerBW.ReedMuller.GradeCard
import StabilizerBW.Roots.BWModel
import StabilizerBW.Roots.MultimonomialClosedForm

/-!
# ReedMuller — degree-`≤ 2` syntactic T-count enumerator (stretch target 1 & 2)

For phase polynomials of degree `≤ 2` we enumerate the **syntactic per-monomial
T-count** `tCount` (NOT the Barnes–Wall grade `g`; they differ on overlapping
monomials, see `refs/02-grade-vs-tcount-distinction.md`).  The closed form is
```
  ∑_{P : deg ≤ 2} z^{tCount P} = 8 · (4 + 4z)^m · (2 + 2z² + 4z³)^{C(m,2)} .
```
The new per-quadratic-monomial factor `2 + 2z² + 4z³` is the multiplicity vector
of per-monomial T-counts at degree `d = 2`.

We also record the canonical **tCount/g disagreement** at the chapter's overlap
example `x₁x₂ + x₁x₃` on `3` qubits: `tCount = 6` but the Barnes–Wall grade is
`4` (the latter via the project's kernel-computable grade model `BWModel.grade`).
-/

namespace ReedMuller

open scoped Classical
open Finset

/-- Per-monomial grade table for `d ≤ 2`. -/
def perMonomialGrade (c : ZMod 8) (d : ℕ) : ℕ :=
  if d = 0 then 0
  else if d = 1 then (if c.val % 2 = 1 then 1 else 0)
  else if d = 2 then
    (if c.val % 2 = 1 then 3
     else if c.val % 4 = 2 then 2
     else 0)
  else 0

/-- A degree-`≤ degBound` phase polynomial: ANF coefficients on subsets of size
`≤ degBound`. -/
abbrev PhasePoly (m degBound : ℕ) : Type := {S : Finset (Fin m) // S.card ≤ degBound} → ZMod 8

/-- The syntactic total T-count `Σ_S perMonomialGrade(c_S, |S|)`. -/
def tCount {m : ℕ} (P : PhasePoly m 2) : ℕ :=
  ∑ S : {S : Finset (Fin m) // S.card ≤ 2}, perMonomialGrade (P S) S.val.card

/-- The per-monomial generating-function factor at degree `d`. -/
def pmGF (z : ℤ) (d : ℕ) : ℤ := ∑ c : ZMod 8, z ^ (perMonomialGrade c d)

theorem pmGF_zero (z : ℤ) : pmGF z 0 = 8 := by
  convert ReedMuller.constant_GF z

theorem pmGF_one (z : ℤ) : pmGF z 1 = 4 + 4 * z := by
  convert ReedMuller.perLinearMonomial_GF z using 1

theorem pmGF_two (z : ℤ) : pmGF z 2 = 2 + 2 * z ^ 2 + 4 * z ^ 3 := by
  unfold pmGF;
  erw [ Fin.sum_univ_eight ] ; simp +decide [ perMonomialGrade ] ; ring;

/-
The T-count GF as a product over the active monomials.
-/
theorem tCount_GF_prod (m : ℕ) (z : ℤ) :
    (∑ P : PhasePoly m 2, z ^ tCount P)
      = ∏ S : {S : Finset (Fin m) // S.card ≤ 2}, pmGF z S.val.card := by
  unfold tCount; simp +decide [ Fintype.card_pi, pmGF ] ;
  rw [ Finset.prod_sum ];
  refine' Finset.sum_bij ( fun P _ => fun S _ => P S ) _ _ _ _ <;> simp +decide [ Finset.prod_pow_eq_pow_sum ];
  · simp +decide [ funext_iff ];
  · exact fun b => ⟨ fun S => b S ( Finset.mem_univ S ), rfl ⟩

/-
The number of `j`-element subsets of `Fin m` is `C(m, j)`.
-/
theorem card_filter_card_eq (m j : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin m) => S.card = j)).card = Nat.choose m j := by
  simp +decide [ Finset.card_univ ]

/-
**Stretch target 1.** The degree-`≤ 2` T-count enumerator factorisation.
-/
theorem tCount_GF_deg2_factorises (m : ℕ) (z : ℤ) :
    (∑ P : PhasePoly m 2, z ^ tCount P)
      = 8 * (4 + 4 * z) ^ m * (2 + 2 * z ^ 2 + 4 * z ^ 3) ^ Nat.choose m 2 := by
  rw [ ReedMuller.tCount_GF_prod ];
  -- We can split the product into three parts: one for each possible cardinality.
  have h_split : (∏ S : {S : Finset (Fin m) // S.card ≤ 2}, pmGF z S.val.card) =
    (∏ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.card = 0), pmGF z S.card) *
    (∏ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.card = 1), pmGF z S.card) *
    (∏ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.card = 2), pmGF z S.card) := by
      rw [ ← Finset.prod_union, ← Finset.prod_union ];
      · refine' Finset.prod_bij ( fun S _ => S.val ) _ _ _ _ <;> simp +decide;
        · grind;
        · rintro a ( ha | ha ) <;> norm_num [ ha ];
      · exact Finset.disjoint_left.mpr ( by aesop );
      · simp +decide [ Finset.disjoint_left ];
  simp_all +decide [ Finset.card_univ ];
  simp +decide [ Finset.prod_filter, Finset.prod_powersetCard, pmGF_zero, pmGF_one, pmGF_two ]

/-! ## Stretch target 2 — the tCount vs grade disagreement -/

/-- The overlap example `x₁x₂ + x₁x₃` on `3` qubits as a degree-`≤ 2` phase
polynomial (coefficient `1` on `{0,1}` and `{0,2}`, `0` elsewhere). -/
def overlapExample : PhasePoly 3 2 :=
  fun S => if S.val = ({0, 1} : Finset (Fin 3)) ∨ S.val = ({0, 2} : Finset (Fin 3)) then 1 else 0

/-- The same phase polynomial in the `BWModel` deVec encoding. -/
def overlapDeVec : List BWModel.Z8 := BWModel.deVec 3 [(1, [0, 1]), (1, [0, 2])]

set_option maxRecDepth 8000 in
/-- **Stretch target 2.** The canonical disagreement: `tCount(x₁x₂ + x₁x₃) = 6`
but the Barnes–Wall grade is `4`.  (The grade is computed by the project's
kernel-computable grade model `BWModel.grade`, whose conventions match the
canonical lattice; the `deVec` encodes the same phase polynomial as
`overlapExample`.) -/
theorem tCount_ne_grade_overlap_example :
    tCount overlapExample = 6 ∧ BWModel.grade 3 overlapDeVec = 4 :=
  ⟨by decide, Roots.Multimonomial.g_P3⟩

end ReedMuller