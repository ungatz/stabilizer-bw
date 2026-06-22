import StabilizerBW.Grade.EnumeratorBound.BandwidthScalingAllN

/-!
# BandwidthScaling / MagicConserved — T4: the per-qubit-conserved magic-state gap

We instantiate the bandwidth scaling on the `n`-qubit magic state `|H⟩^{⊗n}` (the
tensor of single-qubit magic states with Bloch vector `(1/√3, 1/√3, 1/√3)`): every
single-qubit Pauli expectation is `1/√3`.

The striking structural fact is that the resulting bandwidth gap is **independent
of `n`**:

```
W = n√3,   V = n(√3 − 1),   N = 6n,   gap = V/N = (√3 − 1)/6.
```

## Main results

* `BandwidthScaling.magicProfileN` — the all-`1/√3` `n`-qubit Pauli profile.
* `BandwidthScaling.magicProfileN_L` — `W(|H⟩^{⊗n}) = n√3`.
* `BandwidthScaling.magicProfileN_violation` — facet violation `n√3 − n`.
* `BandwidthScaling.magicProfileN_violation_nonneg` — the violation is nonnegative.
* `BandwidthScaling.magic_gap_conserved_allN` — **the per-qubit-conserved gap**:
  `gap = (√3 − 1)/6` for every `n ≥ 2`.
* `BandwidthScaling.magic_gap_conserved_lower` — the conserved gap also satisfies
  the grade-enumerator scaling bound `gap ≥ V / (12 n)`.
-/

open scoped BigOperators

namespace BandwidthScaling

/-- The `n`-qubit magic profile `|H⟩^{⊗n}`: every Pauli expectation is `1/√3`. -/
noncomputable def magicProfileN (n : ℕ) : Fin (3 * n) → ℝ := fun _ => 1 / Real.sqrt 3

/-- **T4: `W(|H⟩^{⊗n}) = (3n)/√3 = n√3`.** -/
theorem magicProfileN_L (n : ℕ) :
    (cliffordFacetN n).L (magicProfileN n) = (n : ℝ) * Real.sqrt 3 := by
  unfold MenuBridge.Facet.L cliffordFacetN magicProfileN
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  simp only [one_mul]
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  nlinarith [hsq]

/-- **T4: the facet violation of `|H⟩^{⊗n}` is `n√3 − n`.** -/
theorem magicProfileN_violation (n : ℕ) :
    (cliffordFacetN n).violation (magicProfileN n) = (n : ℝ) * Real.sqrt 3 - n := by
  unfold MenuBridge.Facet.violation
  rw [magicProfileN_L]; rfl

/-- The magic-state violation is nonnegative (since `√3 ≥ 1`). -/
theorem magicProfileN_violation_nonneg (n : ℕ) :
    0 ≤ (cliffordFacetN n).violation (magicProfileN n) := by
  rw [magicProfileN_violation]
  have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [hn, h1]

/-- **T4: the per-qubit-conserved bandwidth gap.**  On the `n`-qubit Bloch magic
state the bandwidth gap is `(√3 − 1)/6`, **independent of `n`**, for every
`n ≥ 2`.  This is the central operational scaling result: the bandwidth at the
Clifford menu is a per-qubit-conserved quantity. -/
theorem magic_gap_conserved_allN (n : ℕ) (hn : 2 ≤ n) :
    facetGap (cliffordFacetN n) (magicProfileN n) = (Real.sqrt 3 - 1) / 6 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 0 < n := by omega
    positivity
  unfold facetGap
  rw [MenuBridge.Facet.gap_eq, magicProfileN_violation, cliffordFacetN_N]
  field_simp

/-- **T4: the conserved gap satisfies the grade-enumerator scaling bound**
`gap ≥ V / (12 n)`. -/
theorem magic_gap_conserved_lower (n : ℕ) (hn : 2 ≤ n) :
    (cliffordFacetN n).violation (magicProfileN n) / (12 * n)
      ≤ facetGap (cliffordFacetN n) (magicProfileN n) :=
  bandwidth_scaling_allN n hn (magicProfileN n) (magicProfileN_violation_nonneg n)

end BandwidthScaling
