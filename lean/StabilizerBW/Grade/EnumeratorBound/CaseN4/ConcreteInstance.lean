import StabilizerBW.Grade.EnumeratorBound.CaseN4.BandwidthScaling

/-!
# BandwidthN4 / ConcreteInstance — T6: the concrete `n = 4` magic-state gap

We instantiate the bandwidth scaling on the four-qubit magic state `|H⟩^{⊗4}`
(the tensor of single-qubit magic states with Bloch vector `(1/√3,1/√3,1/√3)`):
every single-qubit Pauli expectation is `1/√3`.

## Main results

* `magicProfile4` — the all-`1/√3` four-qubit Pauli expectation profile.
* `magicProfile4_facetValue` — `W(|H⟩^{⊗4}) = 12/√3 = 4√3`.
* `magicProfile4_violation` — facet violation `4√3 − 4`.
* `concrete_gap_n4` — **the explicit n=4 bandwidth gap**:
  `gap = (4√3 − 4)/24 = (√3 − 1)/6`.
* `concrete_gap_n4_lower` — the gap satisfies the grade-enumerator scaling bound
  `gap ≥ V / 48`.
-/

open scoped BigOperators

namespace CliffordMenuN4

/-- The four-qubit magic profile `|H⟩^{⊗4}`: every Pauli expectation is `1/√3`. -/
noncomputable def magicProfile4 : Idx4 → ℝ := fun _ => 1 / Real.sqrt 3

/-- The lifted magic profile on the twelve facet observables. -/
noncomputable def magicLift4 : Fin 12 → ℝ := fun k => magicProfile4 (idx12.symm k)

/-- **T6: `W(|H⟩^{⊗4}) = 12/√3 = 4√3`.** -/
theorem magicProfile4_facetValue :
    facetValue coeffOne magicProfile4 = 4 * Real.sqrt 3 := by
  unfold facetValue coeffOne magicProfile4
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  push_cast
  field_simp
  nlinarith [hsq]

/-- **T6: the facet violation of `|H⟩^{⊗4}` is `4√3 − 4`.** -/
theorem magicProfile4_violation :
    cliffordFacet4.violation magicLift4 = 4 * Real.sqrt 3 - 4 := by
  unfold magicLift4
  rw [cliffordFacet4_violation_eq, magicProfile4_facetValue]
  simp [menuC]

/-- **T6: the explicit n=4 bandwidth gap** of the magic state:
`gap = (4√3 − 4)/24 = (√3 − 1)/6`.  This is the same constant as the n=3
9-Pauli Clifford-menu gap, confirming the closed-form scaling. -/
theorem concrete_gap_n4 :
    facetGap cliffordFacet4 magicLift4 = (Real.sqrt 3 - 1) / 6 := by
  unfold facetGap
  rw [MenuBridge.Facet.gap_eq, magicProfile4_violation, cliffordFacet4_N]
  ring

/-- The magic-state violation is nonnegative (since `√3 ≥ 1`). -/
theorem magicProfile4_violation_nonneg :
    0 ≤ cliffordFacet4.violation magicLift4 := by
  rw [magicProfile4_violation]
  have : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **T6: the concrete instance satisfies the grade-enumerator scaling bound**
`gap ≥ V / 48`. -/
theorem concrete_gap_n4_lower :
    cliffordFacet4.violation magicLift4 / 48 ≤ facetGap cliffordFacet4 magicLift4 :=
  bandwidth_scaling_n4_cliffordFacet magicLift4 magicProfile4_violation_nonneg

end CliffordMenuN4
