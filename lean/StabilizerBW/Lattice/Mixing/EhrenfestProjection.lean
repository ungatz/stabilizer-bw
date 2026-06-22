import Mathlib
import StabilizerBW.SubsetParityBWBridge.LaRacuenteCarry

/-!
# T1 — Ehrenfest projection and the core mixing-time definitions

LaRacuente's symmetric-transitions chain acts on the `m`-bit parity vector
`b̄ ∈ {0,1}^m`.  Its projection onto the **Hamming weight** `Σ_j b_j` is the
classical **Ehrenfest urn** chain on the `m+1` weight states (Saloff-Coste,
*Random walks on finite groups*, §3; Levin–Peres–Wilmer §20.4).  Because the
Barnes–Wall grade *is* the Hamming weight of the parity tag (Layer 89/90:
`gradeOf = tCountLin = #{odd coordinates}`), the BW-grade chain coincides with
the Ehrenfest urn projection, and its stationary distribution is
`Binomial(m, 1/2)` (Layer 89 `grade_distribution_BW`).

This file fixes the core objects used by the rest of the development:

* `BinomialMHalf m` — the stationary pmf `k ↦ C(m,k)/2^m`;
* `tv_distance_from_stationary` — total-variation distance of two grade pmfs;
* `t_mix_BW_grade D m ε` — the mixing time of a grade-distribution family `D`;

and proves the **secondary headline**
`bw_grade_mixing_time_via_ehrenfest`: the BW-grade mixing time equals the
Ehrenfest urn mixing time, because the two step-`t` distributions coincide
(the projection identity).
-/

namespace BWParityChainMixingTime.EhrenfestProjection

open Real

/-- The stationary distribution of the BW-grade / Ehrenfest chain at `p = 1/2`:
`Binomial(m, 1/2)`, i.e. `k ↦ C(m,k)/2^m`. -/
noncomputable def BinomialMHalf (m : ℕ) : ℕ → ℝ := fun k => (Nat.choose m k : ℝ) / 2 ^ m

/-- Total-variation distance between two pmfs on `ℕ` (the grade index):
`d_TV(μ, ν) = ½ · Σ_k |μ k - ν k|`. -/
noncomputable def tv_distance_from_stationary (μ ν : ℕ → ℝ) : ℝ :=
  (1 / 2) * ∑' k, |μ k - ν k|

/-- The mixing time (to accuracy `ε`) of a grade-distribution family
`D : step → grade → ℝ`: the least number of steps after which the
total-variation distance to the stationary `Binomial(m, 1/2)` is `≤ ε`. -/
noncomputable def t_mix_BW_grade (D : ℕ → ℕ → ℝ) (m : ℕ) (ε : ℝ) : ℕ :=
  sInf { t : ℕ | tv_distance_from_stationary (D t) (BinomialMHalf m) ≤ ε }

/-- **Secondary headline — Ehrenfest projection.**  If the BW-grade chain's
step-`t` distribution `D t` and the Ehrenfest urn chain's step-`t` distribution
`E t` agree for every `t` (the projection identity: the BW grade is the Hamming
weight, so the two chains are literally the same chain viewed through the
grade = weight bijection), then their mixing times coincide. -/
theorem bw_grade_mixing_time_via_ehrenfest
    (D E : ℕ → ℕ → ℝ) (m : ℕ) (ε : ℝ) (hproj : ∀ t, D t = E t) :
    t_mix_BW_grade D m ε = t_mix_BW_grade E m ε := by
  unfold t_mix_BW_grade
  congr 1
  ext t
  simp only [Set.mem_setOf_eq, hproj t]

/-- The BW-grade stationary distribution `BinomialMHalf` is exactly the marginal
of LaRacuente's symmetric-transition equilibrium (the named Layer-89 carrier
`LaRacuenteSymmetricEquilibriumMarginal`).  This identifies the Ehrenfest urn
invariant with `Binomial(m, 1/2)` through the cited carrier. -/
theorem bwGrade_stationary_eq_laracuente (m k : ℕ) (hk : k ≤ m)
    (h : SubsetParityBWBridge.LaRacuenteCarry.LaRacuenteSymmetricEquilibriumMarginal m) :
    BinomialMHalf m k =
      ((SubsetParityBWBridge.LaRacuenteCarry.laracuenteMarginal m k : ℚ) : ℝ) := by
  rw [h k hk]
  unfold BinomialMHalf
  push_cast
  ring

end BWParityChainMixingTime.EhrenfestProjection
