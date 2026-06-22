import StabilizerBW.Lattice.Mixing.MixingTime

/-!
# Asymptotic (non-rounded) refinement

The headline `bw_grade_mixing_time_bound` carries an integer ceiling `⌈·⌉`.
For asymptotic / Big-O statements we strip the rounding: since `⌈x⌉ < x + 1`
for `x ≥ 0`, the BW-grade mixing time obeys the non-rounded estimate

`t_mix_BW_grade D m ε ≤ m · log(2^m/ε) / 2 + 1`,

i.e. `t_mix(ε) = O(m · log(2^m/ε))`, the form used for theoretical citation.
-/

namespace MixingTime.Asymptotic

open Real
open MixingTime.EhrenfestProjection
open ParityChainBWGrade.SpectralGapCarrier

/-- **Secondary headline — `bw_grade_mixing_explicit_constant`.**
The non-integer-rounded asymptotic form of the mixing-time bound:
`t_mix_BW_grade D m ε ≤ m · log(2^m/ε) / 2 + 1` (as reals). -/
theorem bw_grade_mixing_explicit_constant
    (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) (hε_lt : ε < 1)
    (D : ℕ → ℕ → ℝ)
    (hGap : SymmetricChainSpectralGapBound (1 / 2) m
              (fun t => tv_distance_from_stationary (D t) (BinomialMHalf m))) :
    (t_mix_BW_grade D m ε : ℝ)
      ≤ (m : ℝ) * Real.log ((2 : ℝ) ^ m / ε) / 2 + 1 := by
  set X : ℝ := (m : ℝ) * Real.log ((2 : ℝ) ^ m / ε) / 2 with hX
  have hbound := MixingTime.MixingTime.bw_grade_mixing_time_bound
    m hm ε hε hε_lt D hGap
  rw [← hX] at hbound
  -- `X ≥ 0` since `2^m/ε > 1` (as `ε < 1 ≤ 2^m`), so `log(2^m/ε) > 0`.
  have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hgt1 : (1 : ℝ) < (2 : ℝ) ^ m / ε := by
    rw [lt_div_iff₀ hε]
    calc (1 : ℝ) * ε = ε := by ring
      _ < 1 := hε_lt
      _ ≤ (2 : ℝ) ^ m := h2m
  have hlog_pos : 0 < Real.log ((2 : ℝ) ^ m / ε) := Real.log_pos hgt1
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hXpos : 0 ≤ X := by rw [hX]; positivity
  have hceil_lt : (Nat.ceil X : ℝ) < X + 1 := Nat.ceil_lt_add_one hXpos
  have hcast : (t_mix_BW_grade D m ε : ℝ) ≤ (Nat.ceil X : ℝ) := by exact_mod_cast hbound
  linarith [hcast, hceil_lt]

end MixingTime.Asymptotic
