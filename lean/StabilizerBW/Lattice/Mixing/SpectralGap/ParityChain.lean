import Mathlib

/-!
# The parity-conditioned birth–death chain

We define the parity-conditioned birth–death Markov chain on the count statistic
`K_t = #{1's at time t}` over `m` parity bits, with bipartite transition
probability `p`, from

> the Krawtchouk diagonalisation,
> the standard Krawtchouk diagonalisation
> `P(k, k+2) = (1-p)·C(m-k,2)/C(m,2)`,  `P(k, k-2) = p·C(k,2)/C(m,2)`,
> with the diagonal absorbing the remaining mass.

The headline is row-stochasticity: every row sums to `1`.
-/

namespace ParityChainBWGrade.ParityChain

open Finset

/-- The up-rate `P(k, k+2) = (1-p)·C(m-k,2)/C(m,2)`. -/
noncomputable def pUp (p : ℝ) (m k : ℕ) : ℝ :=
  (1 - p) * (Nat.choose (m - k) 2 : ℝ) / (Nat.choose m 2 : ℝ)

/-- The down-rate `P(k, k-2) = p·C(k,2)/C(m,2)`. -/
noncomputable def pDown (p : ℝ) (m k : ℕ) : ℝ :=
  p * (Nat.choose k 2 : ℝ) / (Nat.choose m 2 : ℝ)

/-- The parity-conditioned birth–death transition kernel; the diagonal absorbs
the leftover probability mass. -/
noncomputable def parityChain (p : ℝ) (m k k' : ℕ) : ℝ :=
  if k' = k + 2 then pUp p m k
  else if k' + 2 = k then pDown p m k
  else if k' = k then 1 - pUp p m k - pDown p m k
  else 0

/-- At the top boundary (`m < k + 2`) the up-rate vanishes (`C(m-k,2) = 0`). -/
theorem pUp_boundary (p : ℝ) (m k : ℕ) (h : m < k + 2) : pUp p m k = 0 := by
  unfold pUp
  have : Nat.choose (m - k) 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [this]; simp

/-- At the bottom boundary (`k < 2`) the down-rate vanishes (`C(k,2) = 0`). -/
theorem pDown_boundary (p : ℝ) (m k : ℕ) (h : k < 2) : pDown p m k = 0 := by
  unfold pDown
  have : Nat.choose k 2 = 0 := Nat.choose_eq_zero_of_lt h
  rw [this]; simp

/-
**T1 headline (row-stochasticity).**  Each row of the parity-conditioned
birth–death chain sums to `1`.
-/
theorem parityChain_transition_sums_one (p : ℝ) (m k : ℕ) (hk : k ≤ m) :
    ∑ k' ∈ Finset.range (m + 1), parityChain p m k k' = 1 := by
  unfold parityChain;
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.sum_ite ];
  · unfold pUp pDown; split_ifs <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ] ;
  · rcases m with ( _ | _ | _ | m ) <;> simp_all +decide [ pUp, pDown ];
  · split_ifs <;> simp_all +decide [ Finset.filter_eq', Finset.filter_ne' ];
    · linarith;
    · rw [ if_pos ⟨ by linarith, by linarith ⟩ ] ; norm_num;
    · linarith;
    · unfold pUp pDown; split_ifs <;> simp_all +decide [ Nat.choose ] ;
      · exact Or.inl <| Or.inr <| Nat.choose_eq_zero_of_lt <| by omega;
      · -- v4.29 patch (was `grobner` at v4.28; removed in v4.29):
        -- the remaining goal is a polynomial identity in the rational expressions
        -- `(1-p)·C(m-k,2)/C(m,2)`, `p·C(k,2)/C(m,2)`, and `1 - pUp - pDown`,
        -- asserting the three add to 1.  We first handle the unreachable
        -- branch (the inner case split produces `m < k` which contradicts the
        -- outer `hk : k ≤ m`) and then clear denominators in the reachable case.
        first
        | (exfalso; omega)
        | (field_simp; ring)
        | (have hm : (Nat.choose m 2 : ℝ) ≠ 0 := by
             have := Nat.choose_pos (by omega : 2 ≤ m)
             exact_mod_cast Nat.pos_iff_ne_zero.mp this
           field_simp
           ring)

end ParityChainBWGrade.ParityChain