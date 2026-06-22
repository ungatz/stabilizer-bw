import StabilizerBW.Grade.EnumeratorBound.CaseN4.CliffordFacet
import StabilizerBW.Roots.BW4

/-!
# MenuBandwidthN4 / GradeEnumeratorBound — T3: the grade-enumerator bound on facet ℓ¹-norm

The diagonal-character lift of a facet of the four-qubit stabilizer polytope
`Stab₄` is a diagonal operator `D : Roots.Vec16` (the Pauli–Markov rotation
correspondence).  Its Barnes–Wall grade `Roots.grade4 D` is the closed-form
enumerator of Layer 5/BW4.  This file packages the **closed-form upper bound on a
facet's coefficient ℓ¹-norm** in terms of that grade:

```
gradeEnumeratorBound n g = 6·n + 2·g.
```

## Main results

* `gradeEnumeratorBound` — the closed-form bound `6n + 2g`.
* `gradeEnumeratorBound_n4_grade0` — at `n = 4, g = 0` it equals `24`, the
  `N(4) = 6·4` ceiling of the all-ones facet.
* `gradeEnumeratorBound_pos` — strict positivity at `n ≥ 1` (so the bandwidth
  denominator never vanishes).
* `GradeEnumeratorBoundFacetCorrespondence` — the carried correspondence Prop:
  `f.S ≤ gradeEnumeratorBound 4 (grade4 D)` for a facet `f` with lift `D`.
* `triv16`, `grade4_triv16` — the trivial (identity) diagonal character, grade 0,
  the lift of the all-ones stabilizer facet.
* `cliffordFacet4_correspondence` — the correspondence holds **unconditionally**
  for the all-ones facet `cliffordFacet4` (lift `triv16`): `S = 12 ≤ 24`.
* `coeff_l1_le_grade_enumerator` — the general bound, discharged from the carried
  correspondence.

Establishing the correspondence unconditionally for an *arbitrary* facet requires
the Hadamard transform between Pauli expectations and diagonal-character
coefficients (not yet in the corpus); per the structural strawman it is carried as a named
`Prop`, and verified directly for the all-ones facet.
-/

open scoped BigOperators

namespace CliffordMenuN4

/-- **T3: the closed-form grade-enumerator bound** on a facet's coefficient
ℓ¹-norm: `6n + 2g`, where `n` is the qubit count and `g` the Barnes–Wall grade of
the facet's diagonal-character lift. -/
def gradeEnumeratorBound (n g : ℕ) : ℝ := 6 * (n : ℝ) + 2 * (g : ℝ)

/-- At `n = 4, g = 0` the bound equals `24 = N(4) = 6·4`. -/
theorem gradeEnumeratorBound_n4_grade0 : gradeEnumeratorBound 4 0 = 24 := by
  unfold gradeEnumeratorBound; norm_num

/-- The bound is strictly positive for `n ≥ 1`. -/
theorem gradeEnumeratorBound_pos {n g : ℕ} (hn : 1 ≤ n) :
    0 < gradeEnumeratorBound n g := by
  unfold gradeEnumeratorBound
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  positivity

/-- **The carried correspondence `GradeEnumeratorBoundFacetCorrespondence`.**  For a
facet `f` of `Stab₄` with diagonal-character lift `D : Vec16` (Pauli–Markov
rotation correspondence), the facet's coefficient ℓ¹-norm is bounded by the grade
enumerator evaluated at the BW grade of `D`. -/
def GradeEnumeratorBoundFacetCorrespondence
    (f : MenuBridge.Facet 12) (D : Roots.Vec16) : Prop :=
  f.S ≤ gradeEnumeratorBound 4 (Roots.grade4 D)

/-! ### The lift of the all-ones stabilizer facet -/

/-- The trivial (identity) diagonal character on `R¹⁶`: all entries `1`.  This is
the diagonal-character lift of the all-ones stabilizer facet `cliffordFacet4`. -/
def triv16 : Roots.Vec16 := (Roots.ones8, Roots.ones8)

/-- The trivial diagonal character has Barnes–Wall grade `0` (it preserves `L₁₆`
on the nose). -/
theorem grade4_triv16 : Roots.grade4 triv16 = 0 := by
  apply Roots.grade4_eq_zero
  unfold Roots.gradeLE4 triv16 Roots.ones8
  apply Roots.mapsToL4_of_gens <;> decide

/-- **T3 (unconditional instance):** the grade-enumerator correspondence holds for
the all-ones facet, with lift `triv16` (grade `0`): `S = 12 ≤ 24`. -/
theorem cliffordFacet4_correspondence :
    GradeEnumeratorBoundFacetCorrespondence cliffordFacet4 triv16 := by
  unfold GradeEnumeratorBoundFacetCorrespondence
  rw [cliffordFacet4_S, grade4_triv16, gradeEnumeratorBound_n4_grade0]
  norm_num

/-- **T3 (general bound):** under the grade-enumerator correspondence, a facet's
coefficient ℓ¹-norm is bounded by the closed-form grade enumerator. -/
theorem coeff_l1_le_grade_enumerator (f : MenuBridge.Facet 12) (D : Roots.Vec16)
    (hcorr : GradeEnumeratorBoundFacetCorrespondence f D) :
    f.S ≤ gradeEnumeratorBound 4 (Roots.grade4 D) := hcorr

end CliffordMenuN4
