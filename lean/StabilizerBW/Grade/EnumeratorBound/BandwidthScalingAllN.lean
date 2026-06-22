import StabilizerBW.Grade.EnumeratorBound.GradeEnumeratorAllN

/-!
# MenuBandwidthAllN / BandwidthScalingAllN — T3: closed-form bandwidth scaling at all `n`

Combining the bridge identity `MenuBridge.Facet.gap_eq` (the un-compiled gap
equals `V/N`, `N = 2S`) with the grade-enumerator bound
`S ≤ gradeEnumeratorBound n g` gives the **closed-form lower bound on the bandwidth
gap** at every `n`:

```
gap(ρ) = V(ρ)/N ≥ V(ρ) / (2 · gradeEnumeratorBound n g).
```

For the all-ones facet (grade `0`) this is `gap ≥ V / (12 n)`.

## Main results

* `MenuBandwidthAllN.facetGap` — the un-compiled bandwidth gap
  `quantumValue − classicalValue`.
* `MenuBandwidthAllN.bandwidth_scaling_allN_general` — the closed-form scaling for
  any facet with a valid grade-enumerator correspondence and nonnegative violation.
* `MenuBandwidthAllN.bandwidth_scaling_allN` — the headline unconditional instance
  for the all-ones facet: `gap ≥ V / (12 n)` for all `n ≥ 2`.
-/

open scoped BigOperators

namespace MenuBandwidthAllN

/-- The un-compiled **bandwidth gap** of a facet on a profile:
`quantumValue − classicalValue` (equal to `V/N` by `MenuBridge.Facet.gap_eq`). -/
noncomputable def facetGap {K : ℕ} (f : MenuBridge.Facet K) (E : Fin K → ℝ) : ℝ :=
  f.quantumValue E - f.classicalValue

/-- **T3: closed-form bandwidth scaling at all `n` (general facet).**  Given a
facet `f` of the `n`-qubit stabilizer polytope with grade `g`, a valid
grade-enumerator correspondence, a nondegenerate facet (`0 < S`), and a
nonnegative violation, the bandwidth gap is bounded below by the closed-form grade
enumerator scaling `V / (2 · gradeEnumeratorBound n g)`. -/
theorem bandwidth_scaling_allN_general (n : ℕ) (f : MenuBridge.Facet (3 * n)) (g : ℕ)
    (E : Fin (3 * n) → ℝ)
    (hcorr : GradeEnumeratorBoundFacetCorrespondence n f g)
    (hSpos : 0 < f.S)
    (hV : 0 ≤ f.violation E) :
    f.violation E / (2 * gradeEnumeratorBound n g) ≤ facetGap f E := by
  have hSle : f.S ≤ gradeEnumeratorBound n g := hcorr
  have hNpos : 0 < f.N := f.N_pos hSpos
  have hNeq : f.N = 2 * f.S := rfl
  have h2b : f.N ≤ 2 * gradeEnumeratorBound n g := by rw [hNeq]; linarith
  unfold facetGap
  rw [MenuBridge.Facet.gap_eq]
  exact div_le_div_of_nonneg_left hV hNpos h2b

/-- **T3 (headline, unconditional instance):** for the all-ones facet
`cliffordFacetN n` (grade `0`, `2·gradeEnumeratorBound n 0 = 12n`) any profile with
nonnegative violation satisfies `gap ≥ V / (12 n)`, for every `n ≥ 2`. -/
theorem bandwidth_scaling_allN (n : ℕ) (hn : 2 ≤ n) (E : Fin (3 * n) → ℝ)
    (hV : 0 ≤ (cliffordFacetN n).violation E) :
    (cliffordFacetN n).violation E / (12 * n) ≤ facetGap (cliffordFacetN n) E := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold facetGap
  rw [MenuBridge.Facet.gap_eq, cliffordFacetN_N]
  exact div_le_div_of_nonneg_left hV (by linarith) (by linarith)

end MenuBandwidthAllN
