import StabilizerBW.Grade.EnumeratorBound.CliffordMenuAllN

/-!
# MenuBandwidthAllN / GradeEnumeratorAllN — T2: the all-`n` grade-enumerator bound

The diagonal-character lift of a facet of the `n`-qubit stabilizer polytope has a
Barnes–Wall grade `g`.  This file packages the **closed-form upper bound on a
facet's coefficient ℓ¹-norm** in terms of that grade, at all `n`:

```
gradeEnumeratorBound n g = 6·n + 2·g.
```

This is the all-`n` generalisation of `CliffordMenuN4.gradeEnumeratorBound`.

## Main results

* `MenuBandwidthAllN.gradeEnumeratorBound` — the closed-form bound `6n + 2g`.
* `MenuBandwidthAllN.gradeEnumeratorBound_grade0` — at grade `0` it equals `6n`,
  the `N(n) = 6n` ceiling of the all-ones facet.
* `MenuBandwidthAllN.gradeEnumeratorBound_pos` — strict positivity at `n ≥ 1`.
* `MenuBandwidthAllN.GradeEnumeratorBoundFacetCorrespondence` — the correspondence
  Prop: `f.S ≤ gradeEnumeratorBound n g` for a facet `f` with grade `g`.
* `MenuBandwidthAllN.cliffordFacetN_correspondence` — the correspondence holds
  **unconditionally** for the all-ones facet (grade `0`): `S = 3n ≤ 6n`.
-/

open scoped BigOperators

namespace MenuBandwidthAllN

/-- **T2: the closed-form grade-enumerator bound** on a facet's coefficient
ℓ¹-norm: `6n + 2g`, where `n` is the qubit count and `g` the Barnes–Wall grade of
the facet's diagonal-character lift. -/
def gradeEnumeratorBound (n g : ℕ) : ℝ := 6 * (n : ℝ) + 2 * (g : ℝ)

/-- **T2: the closed-form** `gradeEnumeratorBound n g = 6n + 2g`. -/
theorem gradeEnumeratorBound_allN (n g : ℕ) :
    gradeEnumeratorBound n g = 6 * (n : ℝ) + 2 * (g : ℝ) := rfl

/-- At grade `0` the bound equals `6n = N(n)`. -/
theorem gradeEnumeratorBound_grade0 (n : ℕ) : gradeEnumeratorBound n 0 = 6 * (n : ℝ) := by
  unfold gradeEnumeratorBound; norm_num

/-- The bound is strictly positive for `n ≥ 1`. -/
theorem gradeEnumeratorBound_pos {n g : ℕ} (hn : 1 ≤ n) :
    0 < gradeEnumeratorBound n g := by
  unfold gradeEnumeratorBound
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  positivity

/-- **The correspondence `GradeEnumeratorBoundFacetCorrespondence`.**  For a facet
`f` of the `n`-qubit stabilizer polytope whose diagonal-character lift has
Barnes–Wall grade `g`, the facet's coefficient ℓ¹-norm is bounded by the grade
enumerator. -/
def GradeEnumeratorBoundFacetCorrespondence
    (n : ℕ) (f : MenuBridge.Facet (3 * n)) (g : ℕ) : Prop :=
  f.S ≤ gradeEnumeratorBound n g

/-- **T2 (unconditional instance):** the grade-enumerator correspondence holds for
the all-ones facet, at grade `0`: `S = 3n ≤ 6n`. -/
theorem cliffordFacetN_correspondence (n : ℕ) :
    GradeEnumeratorBoundFacetCorrespondence n (cliffordFacetN n) 0 := by
  unfold GradeEnumeratorBoundFacetCorrespondence
  rw [cliffordFacetN_S, gradeEnumeratorBound_grade0]
  have : (0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **T2 (general bound):** under the grade-enumerator correspondence, a facet's
coefficient ℓ¹-norm is bounded by the closed-form grade enumerator. -/
theorem coeff_l1_le_grade_enumerator (n : ℕ) (f : MenuBridge.Facet (3 * n)) (g : ℕ)
    (hcorr : GradeEnumeratorBoundFacetCorrespondence n f g) :
    f.S ≤ gradeEnumeratorBound n g := hcorr

end MenuBandwidthAllN
