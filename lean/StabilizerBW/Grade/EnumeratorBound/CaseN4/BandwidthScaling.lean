import StabilizerBW.Grade.EnumeratorBound.CaseN4.GradeEnumeratorBound

/-!
# BandwidthN4 / BandwidthScaling — T4: closed-form bandwidth scaling at `n = 4`

Combining the bridge identity `Facet.gap_eq` (the un-compiled gap equals
`V/N`, `N = 2S`) with the grade-enumerator bound `S ≤ gradeEnumeratorBound 4 g`
gives the **closed-form lower bound on the bandwidth gap** at `n = 4`:

```
gap(ρ) = V(ρ)/N ≥ V(ρ) / (2 · gradeEnumeratorBound 4 g),    g = grade4 (lift).
```

This is the scaling formula that lets a verification-protocol designer estimate
the bandwidth at `n = 4` from the grade enumerator alone, with no per-state
computation.

## Main results

* `facetGap` — the un-compiled bandwidth gap `quantumValue − classicalValue`.
* `bandwidth_scaling_n4` — the closed-form scaling: for any facet with a valid
  grade-enumerator correspondence and nonnegative violation,
  `gap ≥ V / (2·gradeEnumeratorBound 4 g)`.
* `bandwidth_scaling_n4_cliffordFacet` — the unconditional instance for the
  all-ones facet (lift `triv16`, grade `0`): `gap ≥ V / 48`.
-/

open scoped BigOperators

namespace CliffordMenuN4

/-- The un-compiled **bandwidth gap** of a facet on a profile:
`quantumValue − classicalValue` (equal to `V/N` by `MenuBridge.Facet.gap_eq`). -/
noncomputable def facetGap (f : MenuBridge.Facet 12) (E : Fin 12 → ℝ) : ℝ :=
  f.quantumValue E - f.classicalValue

/-- **T4: closed-form bandwidth scaling at `n = 4`.**  Given a facet `f` of
`Stab₄` with diagonal-character lift `D`, a valid grade-enumerator correspondence,
a nondegenerate facet (`0 < S`), and a nonnegative violation, the bandwidth gap is
bounded below by the closed-form grade-enumerator scaling
`V / (2 · gradeEnumeratorBound 4 (grade4 D))`. -/
theorem bandwidth_scaling_n4 (f : MenuBridge.Facet 12) (D : Roots.Vec16)
    (E : Fin 12 → ℝ)
    (hcorr : GradeEnumeratorBoundFacetCorrespondence f D)
    (hSpos : 0 < f.S)
    (hV : 0 ≤ f.violation E) :
    f.violation E / (2 * gradeEnumeratorBound 4 (Roots.grade4 D)) ≤ facetGap f E := by
  have hSle : f.S ≤ gradeEnumeratorBound 4 (Roots.grade4 D) := hcorr
  have hNpos : 0 < f.N := f.N_pos hSpos
  have hNeq : f.N = 2 * f.S := rfl
  have h2b : f.N ≤ 2 * gradeEnumeratorBound 4 (Roots.grade4 D) := by rw [hNeq]; linarith
  unfold facetGap
  rw [MenuBridge.Facet.gap_eq]
  exact div_le_div_of_nonneg_left hV hNpos h2b

/-- **T4 (unconditional instance):** for the all-ones facet `cliffordFacet4`
(lift `triv16`, grade `0`, `gradeEnumeratorBound 4 0 = 24`) any profile with
nonnegative violation satisfies `gap ≥ V / 48`. -/
theorem bandwidth_scaling_n4_cliffordFacet (E : Fin 12 → ℝ)
    (hV : 0 ≤ cliffordFacet4.violation E) :
    cliffordFacet4.violation E / 48 ≤ facetGap cliffordFacet4 E := by
  have h := bandwidth_scaling_n4 cliffordFacet4 triv16 E
    cliffordFacet4_correspondence cliffordFacet4_S_pos hV
  rw [grade4_triv16, gradeEnumeratorBound_n4_grade0] at h
  norm_num at h
  convert h using 2

end CliffordMenuN4
