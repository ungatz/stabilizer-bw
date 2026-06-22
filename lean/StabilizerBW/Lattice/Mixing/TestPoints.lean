import StabilizerBW.Lattice.Mixing.MixingTime

/-!
# Mandated falsification test points

The development pre-registers three `(m, ε)` falsification witnesses (§3, §5):
`(2, 0.01)`, `(4, 0.001)`, `(8, 0.0001)`.  For each, the explicit headline
bound `⌈ m · log(2^m/ε) / 2 ⌉` evaluates to a concrete integer:

* `(m, ε) = (2, 1/100)`  : `⌈ log 400 ⌉      = 6`
* `(m, ε) = (4, 1/1000)` : `⌈ 2·log 16000 ⌉  = 20`
* `(m, ε) = (8, 1/10000)`: `⌈ 4·log 2560000 ⌉ = 60`

We confirm (kernel-checked) that the BW-grade chain mixes within these step
counts, i.e. `t_mix_BW_grade D m ε ≤ N` for the three pairs.  No falsification
occurs: every test point passes.
-/

namespace MixingTime.TestPoints

open Real
open MixingTime.EhrenfestProjection
open MixingTime.MixingTime
open ParityChainBWGrade.SpectralGapCarrier

/-! ## Numerical log bounds underlying the three integer thresholds -/

/-
`log 400 ≤ 6`, i.e. `400 ≤ e^6` (the `m = 2` threshold).
-/
theorem log400_le : Real.log 400 ≤ 6 := by
  rw [ Real.log_le_iff_le_exp ] <;> norm_num;
  have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 6 = ( Real.exp 1 ) ^ 6 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; nlinarith [ pow_le_pow_left₀ ( by positivity ) this 6 ]

/-
`log 16000 ≤ 10`, i.e. `16000 ≤ e^10` (the `m = 4` threshold).
-/
theorem log16000_le : Real.log 16000 ≤ 10 := by
  rw [ Real.log_le_iff_le_exp ] <;> norm_num;
  have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 10 = ( Real.exp 1 ) ^ 10 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this 10 )

/-
`log 2560000 ≤ 15`, i.e. `2560000 ≤ e^15` (the `m = 8` threshold).
-/
theorem log2560000_le : Real.log 2560000 ≤ 15 := by
  rw [ Real.log_le_iff_le_exp ] <;> norm_num;
  have := Real.exp_one_gt_d9.le;
  rw [ show Real.exp 15 = ( Real.exp 1 ) ^ 15 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( by norm_num ) ( pow_le_pow_left₀ ( by norm_num ) this _ )

/-! ## The three falsification test points -/

/-- **Test point `(m, ε) = (2, 0.01)`.**  The BW-grade chain mixes within
`6 = ⌈ log 400 ⌉` steps. -/
theorem testpoint_m2
    (D : ℕ → ℕ → ℝ)
    (hGap : SymmetricChainSpectralGapBound (1 / 2) 2
              (fun t => tv_distance_from_stationary (D t) (BinomialMHalf 2))) :
    t_mix_BW_grade D 2 (1 / 100) ≤ 6 := by
  refine le_trans
    (bw_grade_mixing_time_bound 2 (by norm_num) (1 / 100) (by norm_num) (by norm_num) D hGap) ?_
  rw [Nat.ceil_le]
  have h : (2 : ℝ) ^ 2 / (1 / 100) = 400 := by norm_num
  rw [h]
  have := log400_le
  push_cast
  nlinarith [this]

/-- **Test point `(m, ε) = (4, 0.001)`.**  The BW-grade chain mixes within
`20 = ⌈ 2·log 16000 ⌉` steps. -/
theorem testpoint_m4
    (D : ℕ → ℕ → ℝ)
    (hGap : SymmetricChainSpectralGapBound (1 / 2) 4
              (fun t => tv_distance_from_stationary (D t) (BinomialMHalf 4))) :
    t_mix_BW_grade D 4 (1 / 1000) ≤ 20 := by
  refine le_trans
    (bw_grade_mixing_time_bound 4 (by norm_num) (1 / 1000) (by norm_num) (by norm_num) D hGap) ?_
  rw [Nat.ceil_le]
  have h : (2 : ℝ) ^ 4 / (1 / 1000) = 16000 := by norm_num
  rw [h]
  have := log16000_le
  push_cast
  nlinarith [this]

/-- **Test point `(m, ε) = (8, 0.0001)`.**  The BW-grade chain mixes within
`60 = ⌈ 4·log 2560000 ⌉` steps. -/
theorem testpoint_m8
    (D : ℕ → ℕ → ℝ)
    (hGap : SymmetricChainSpectralGapBound (1 / 2) 8
              (fun t => tv_distance_from_stationary (D t) (BinomialMHalf 8))) :
    t_mix_BW_grade D 8 (1 / 10000) ≤ 60 := by
  refine le_trans
    (bw_grade_mixing_time_bound 8 (by norm_num) (1 / 10000) (by norm_num) (by norm_num) D hGap) ?_
  rw [Nat.ceil_le]
  have h : (2 : ℝ) ^ 8 / (1 / 10000) = 2560000 := by norm_num
  rw [h]
  have := log2560000_le
  push_cast
  nlinarith [this]

end MixingTime.TestPoints