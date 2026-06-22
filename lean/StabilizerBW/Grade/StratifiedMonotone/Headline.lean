import StabilizerBW.Grade.StratifiedMonotone.UpperBound

/-!
# T5 — the headline closed-form Pauli-weight-stratified upper bound

For every physical density operator `ρ` on `m` qubits whose Pauli-weight support is `≤ g`, the
Dutta–Tushar magic functional is bounded by the corrected closed form:
```
  C(ρ)  ≤  cUB_pw m g  =  (#{P : wt(P) ≤ g}) − 1  =  (∑_{j≤g} C(m,j)·3^j) − 1 .
```

The conditional form `C_ub_PauliWeight_via_HW` takes the Heisenberg–Weyl carrier
`DensityPauliCoefficientBound` as a hypothesis (matching the structural strawman's §2 signature shape); the
unconditional form `C_ub_PauliWeight` discharges that carrier via
`densityPauliCoefficientBound_holds`.
-/

namespace BWGradeStratifiedMonotoneR2

open Finset

/-- The cumulative-stratum cardinality minus one counts the **non-identity** weight-`≤ g` Paulis. -/
theorem cUB_pw_eq_card_nonId (m g : ℕ) :
    cUB_pw m g
      = ((Finset.univ.filter
          (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g ∧ P ≠ pauliId m)).card : ℝ) := by
  unfold cUB_pw pauliWeightLECard
  have hsplit :
      (Finset.univ.filter (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g)).card
        = (Finset.univ.filter
            (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g ∧ P ≠ pauliId m)).card + 1 := by
    rw [← Finset.filter_filter]
    have hid : pauliId m ∈ Finset.univ.filter (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g) := by
      simp [BWGradeOfPauli, pauliId]
    rw [Finset.filter_ne']
    rw [Finset.card_erase_of_mem hid]
    have hpos : 1 ≤ (Finset.univ.filter (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g)).card := by
      exact Finset.card_pos.2 ⟨pauliId m, hid⟩
    omega
  rw [hsplit]
  push_cast
  ring

/-- **Conditional headline** (carrier form).  Given the Heisenberg–Weyl per-coefficient bound, every
weight-`≤ g` stratified physical density operator satisfies the closed-form bound. -/
theorem C_ub_PauliWeight_via_HW (h : DensityPauliCoefficientBound) :
    ∀ (m g : ℕ) (ρ : PhysicalDensity m),
      PauliWeightSupportLE m g ρ → duttaTusharC ρ ≤ cUB_pw m g := by
  intro m g ρ hs
  rw [duttaTusharC_eq_sum_nonId, cUB_pw_eq_card_nonId]
  -- Restrict the support: outside the weight-`≤ g` stratum the coefficient vanishes.
  have hzero : ∀ P ∈ Finset.univ.filter (fun P : PauliIdx m => P ≠ pauliId m),
      P ∉ Finset.univ.filter (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g ∧ P ≠ pauliId m) →
      |ρ.1 P| = 0 := by
    intro P hP hPnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP hPnot
    have : ¬ BWGradeOfPauli m P ≤ g := by
      intro hle; exact hPnot ⟨hle, hP⟩
    have : ρ.1 P = 0 := by
      by_contra hne
      exact this (hs P hne)
    simp [this]
  have hsub :
      Finset.univ.filter (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g ∧ P ≠ pauliId m)
        ⊆ Finset.univ.filter (fun P : PauliIdx m => P ≠ pauliId m) := by
    intro P hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
    exact hP.2
  rw [← Finset.sum_subset hsub hzero]
  calc ∑ P ∈ Finset.univ.filter (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g ∧ P ≠ pauliId m),
          |ρ.1 P|
      ≤ ∑ _P ∈ Finset.univ.filter
          (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g ∧ P ≠ pauliId m), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro P _
        exact h m ρ P
    _ = ((Finset.univ.filter
          (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g ∧ P ≠ pauliId m)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Unconditional headline.**  Every weight-`≤ g` stratified physical density operator satisfies
the corrected closed-form Pauli-weight upper bound. -/
theorem C_ub_PauliWeight (m g : ℕ) (ρ : PhysicalDensity m)
    (hs : PauliWeightSupportLE m g ρ) : duttaTusharC ρ ≤ cUB_pw m g :=
  C_ub_PauliWeight_via_HW densityPauliCoefficientBound_holds m g ρ hs

end BWGradeStratifiedMonotoneR2
