import StabilizerBW.Lattice.Mixing.EhrenfestProjection
import StabilizerBW.Lattice.Mixing.SpectralGapReuse
import StabilizerBW.Lattice.Mixing.LevinPeresWilmer

/-!
# HEADLINE: the explicit BW-grade mixing-time bound

Composing

* (`EhrenfestProjection`) — the mixing-time / TV-distance definitions,
* (`SpectralGapReuse`) — the spectral gap `gap = 2/m` at `p = 1/2`
  (the development carrier `SymmetricChainSpectralGapBound`), and
* (`LevinPeresWilmer`) — the textbook spectral-gap mixing-time bound,

we obtain the **primary headline**: the BW linear-stratum grade distribution
under the symmetric Ehrenfest urn chain mixes in at most
`⌈ m · log(2^m / ε) / 2 ⌉` steps to total-variation distance `≤ ε` from the
stationary `Binomial(m, 1/2)`.

The Levin–Peres–Wilmer minimum stationary probability for `Binomial(m, 1/2)` is
`π_min = C(m,0)/2^m = 1/2^m`, so LPW Eq. 12.12 gives
`t_mix(ε) ≤ ⌈ gap⁻¹ · log(1/(π_min·ε)) ⌉ = ⌈ (m/2) · log(2^m/ε) ⌉`, exactly the
original bound.  The genuine Markov input enters only through the named
the development carrier `SymmetricChainSpectralGapBound` (hypothesis `hGap`); the headline
is therefore **unconditional modulo that carrier**.

The hypothesis `ε < 1` is pre-registered; it is not needed for
this bound (it is used by the asymptotic refinement T5), so it is kept here only
to match the pre-registered signature.
-/

namespace MixingTime.MixingTime

open Real
open MixingTime.EhrenfestProjection
open ParityChainBWGrade.SpectralGapCarrier

/-- **PRIMARY HEADLINE — `bw_grade_mixing_time_bound`.**
For every `m ≥ 1` and `ε ∈ (0,1)`, the BW-grade chain (with step-`t`
grade distribution `D t`) whose total-variation distance to the stationary
`Binomial(m, 1/2)` obeys the development spectral-gap carrier
`SymmetricChainSpectralGapBound (1/2) m` mixes within
`⌈ m · log(2^m / ε) / 2 ⌉` steps:

`t_mix_BW_grade D m ε ≤ ⌈ m · log(2^m / ε) / 2 ⌉`. -/
theorem bw_grade_mixing_time_bound
    (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) (hε_lt : ε < 1)
    (D : ℕ → ℕ → ℝ)
    (hGap : SymmetricChainSpectralGapBound (1 / 2) m
              (fun t => tv_distance_from_stationary (D t) (BinomialMHalf m))) :
    t_mix_BW_grade D m ε ≤ Nat.ceil ((m : ℝ) * Real.log ((2 : ℝ) ^ m / ε) / 2) := by
  set dist : ℕ → ℝ := fun t => tv_distance_from_stationary (D t) (BinomialMHalf m) with hdist
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmle : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    have hlt := Nat.lt_two_pow_self (n := m)
    calc (m : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast le_of_lt hlt
      _ = (2 : ℝ) ^ m := by push_cast; ring
  -- The LPW separation decay with `π_min = 1/2^m` and `gap = 2/m`.
  have hgap_eq : symmetricChainGap (1 / 2) m = 2 / (m : ℝ) :=
    ParityChainBWGrade.SpectralGapCarrier.bwGrade_spectral_gap_at_pHalf m
  have hdecay : ∀ t : ℕ,
      dist t ≤ (1 / (1 / (2 : ℝ) ^ m)) * Real.exp (- (2 / (m : ℝ)) * (t : ℝ)) := by
    intro t
    have h1 := hGap t
    rw [hgap_eq] at h1
    have hexp_pos : (0 : ℝ) < Real.exp (- (2 / (m : ℝ)) * (t : ℝ)) := Real.exp_pos _
    have hmul : (m : ℝ) * Real.exp (- (2 / (m : ℝ)) * (t : ℝ))
        ≤ (2 : ℝ) ^ m * Real.exp (- (2 / (m : ℝ)) * (t : ℝ)) :=
      mul_le_mul_of_nonneg_right hmle (le_of_lt hexp_pos)
    have hpi : (1 : ℝ) / (1 / (2 : ℝ) ^ m) = (2 : ℝ) ^ m := by
      rw [one_div_one_div]
    rw [hpi]
    exact le_trans h1 hmul
  have hgap_pos : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hpi_pos : (0 : ℝ) < 1 / (2 : ℝ) ^ m := by positivity
  have hbound := MixingTime.LevinPeresWilmer.mixing_time_le_of_spectral_decay
    dist (2 / (m : ℝ)) (1 / (2 : ℝ) ^ m) ε hgap_pos hpi_pos hε hdecay
  -- Rewrite the LPW ceiling argument into the structural strawman's exact form.
  have harg : (2 / (m : ℝ))⁻¹ * Real.log (1 / ((1 / (2 : ℝ) ^ m) * ε))
      = (m : ℝ) * Real.log ((2 : ℝ) ^ m / ε) / 2 := by
    have hinv : (2 / (m : ℝ))⁻¹ = (m : ℝ) / 2 := by rw [inv_div]
    have hfrac : (1 : ℝ) / ((1 / (2 : ℝ) ^ m) * ε) = (2 : ℝ) ^ m / ε := by field_simp
    rw [hinv, hfrac]; ring
  rw [harg] at hbound
  exact hbound

end MixingTime.MixingTime
