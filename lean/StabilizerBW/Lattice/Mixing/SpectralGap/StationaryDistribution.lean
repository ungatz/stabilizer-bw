import StabilizerBW.Lattice.Mixing.SpectralGap.ParityChain

/-!
# T2 — The stationary distribution of the parity-conditioned chain

From `refs/laracuente/noise-2designs-markov-chain.tex`, **lines 209–242**, the
stationary distribution on a parity class is `π_r(k) ∝ C(m,k)·θ^k` with
`θ = √((1-p)/p)`.  At `p = 1/2`, `θ = 1` and the distribution is uniform on the
parity class (equivalently `Binomial(m, 1/2)` conditioned on parity).

We prove the local **detailed-balance** identity for `π`, and then the global
**stationarity** identity `∑_k π(k)·P(k, j) = π(j)`.
-/

namespace ParityChainBWGradeMixing.StationaryDistribution

open Finset ParityChainBWGradeMixing.ParityChain

/-- `θ = √((1-p)/p)`. -/
noncomputable def theta (p : ℝ) : ℝ := Real.sqrt ((1 - p) / p)

/-- The (unnormalised) stationary weight `π(k) = C(m,k)·θ^k`. -/
noncomputable def stat (p : ℝ) (m k : ℕ) : ℝ := (Nat.choose m k : ℝ) * (theta p) ^ k

/-- `θ² = (1-p)/p` on `0 < p < 1`. -/
theorem theta_sq (p : ℝ) (hp : 0 < p ∧ p < 1) : (theta p) ^ 2 = (1 - p) / p := by
  unfold theta
  rw [Real.sq_sqrt]
  apply div_nonneg <;> [linarith [hp.2]; linarith [hp.1]]

/-
The binomial identity underlying detailed balance:
`C(m,k)·C(m-k,2) = C(m,k+2)·C(k+2,2)`, valid for all `m, k`.
-/
theorem choose_balance_id (m k : ℕ) :
    Nat.choose m k * Nat.choose (m - k) 2 = Nat.choose m (k + 2) * Nat.choose (k + 2) 2 := by
  by_cases hm : k + 2 ≤ m;
  · rw [ ← Nat.choose_symm_of_eq_add ];
    rw [ Nat.choose_mul ];
    · rw [ Nat.sub_sub, Nat.choose_mul ];
      · rw [ show m - ( k + 2 ) = ( m - 2 ) - k by omega, Nat.choose_symm ( by omega ) ];
        norm_num;
      · grind;
    · omega;
    · rw [ Nat.sub_add_cancel ( by linarith ) ];
  · simp_all +decide [ Nat.choose_eq_zero_of_lt ];
    exact Or.inr ( Nat.choose_eq_zero_of_lt ( by omega ) )

/-
**Detailed balance.**  `π(k)·P(k, k+2) = π(k+2)·P(k+2, k)`.
-/
theorem parityChain_detailed_balance (p : ℝ) (hp : 0 < p ∧ p < 1) (m k : ℕ) :
    stat p m k * pUp p m k = stat p m (k + 2) * pDown p m (k + 2) := by
  unfold stat pUp pDown; ring ;
  rw [ show 2 + k = k + 2 by ring ] ; rw [ theta_sq p hp ] ; by_cases h : p = 0 <;> simp_all +decide [ add_comm, Nat.choose_succ_succ, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ; ring;
  convert congr_arg ( fun x : ℕ => ( x : ℝ ) * theta p ^ k * ( ( m.choose 2 : ℝ ) ⁻¹ ) * ( 1 - p ) ) ( choose_balance_id m k ) using 1 <;> ring; all_goals push_cast; ring;

/-
**T2 headline (stationarity).**  `π` is stationary: `∑_k π(k)·P(k, j) = π(j)`.
-/
theorem parityChain_stationary (p : ℝ) (hp : 0 < p ∧ p < 1) (m j : ℕ) (hj : j ≤ m) :
    ∑ k ∈ Finset.range (m + 1), stat p m k * parityChain p m k j = stat p m j := by
  by_cases hj2 : 2 ≤ j <;> by_cases hjm : j + 2 ≤ m <;> simp_all +decide [ Finset.sum_ite, parityChain ];
  · rw [ Finset.sum_eq_single ( j - 2 ), Finset.sum_eq_single ( j + 2 ) ] <;> norm_num;
    · grind +suggestions;
    · intros; omega;
    · grind;
    · intros; omega;
    · grind;
  · rw [ Finset.sum_eq_single ( j - 2 ), Finset.sum_eq_zero ] <;> norm_num;
    · rcases j with ( _ | _ | j ) <;> simp_all +decide [ parityChain_detailed_balance ];
      rw [ pUp_boundary ] <;> norm_num ; linarith;
      linarith;
    · intros; omega;
    · intros; omega;
    · exact fun h => False.elim <| h ( by linarith ) <| by omega;
  · interval_cases j <;> simp_all +decide [ Finset.sum_filter, parityChain ];
    · unfold stat pUp pDown;
      rw [ theta_sq ] <;> ring_nf <;> norm_num [ hp.1.ne', hp.2.ne' ];
      · simp +decide [ sq, mul_assoc, mul_comm p, hp.1.ne', hp.2.ne', ne_of_gt ( Nat.choose_pos hjm ) ];
      · tauto;
    · have := parityChain_detailed_balance p hp m 1; simp_all +decide [ pUp, pDown, stat ] ; ring;
      grind +splitImp;
  · interval_cases j <;> simp_all +decide [ Finset.sum_filter ];
    · interval_cases m <;> norm_num [ pUp, pDown ];
    · interval_cases m <;> norm_num [ pUp, pDown, stat ]

end ParityChainBWGradeMixing.StationaryDistribution