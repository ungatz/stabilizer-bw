import Mathlib

/-!
# The Levin–Peres–Wilmer eigenvalue / spectral-gap mixing-time bound

This file states and **kernel-proves** the textbook spectral-gap mixing-time
bound

> Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, AMS 2nd ed. (2017),
> §12, Theorem 12.3 / Eq. 12.11–12.12:
> for a reversible chain with stationary distribution `π`, minimum stationary
> probability `π_min > 0` and absolute spectral gap `gap > 0`, the mixing time
> obeys `t_mix(ε) ≤ ⌈ gap⁻¹ · log(1/(π_min·ε)) ⌉`.

The genuine Markov-chain content (existence of a reversible chain with the
quoted gap and the relaxation bound `dist t ≤ (1/π_min)·exp(-gap·t)`) is fed in
as the hypothesis `hdecay`; LPW's Eq. 12.11 derives exactly this exponential
separation-distance decay from the spectral gap.  Everything below it — solving
`(1/π_min)·exp(-gap·t) ≤ ε` for the smallest integer `t` — is elementary real
analysis, proved here from scratch (no Mathlib Markov-chain theory is required,
matching the Tier-C fallback of the development).
-/

namespace MixingTime.LevinPeresWilmer

open Real

/-- **Levin–Peres–Wilmer Theorem 12.3 / Eq. 12.11–12.12.**
Let `dist : ℕ → ℝ` be the distance-to-stationarity of a reversible chain whose
spectral gap `gap > 0` and minimum stationary probability `π_min > 0` give the
separation-distance decay `dist t ≤ (1/π_min)·exp(-gap·t)`.  Then the mixing
time `sInf {t | dist t ≤ ε}` is bounded by `⌈ gap⁻¹ · log(1/(π_min·ε)) ⌉`. -/
theorem mixing_time_le_of_spectral_decay
    (dist : ℕ → ℝ) (gap πmin ε : ℝ)
    (hgap : 0 < gap) (hpi : 0 < πmin) (hε : 0 < ε)
    (hdecay : ∀ t : ℕ, dist t ≤ (1 / πmin) * Real.exp (- gap * (t : ℝ))) :
    sInf { t : ℕ | dist t ≤ ε } ≤ Nat.ceil (gap⁻¹ * Real.log (1 / (πmin * ε))) := by
  set X : ℝ := gap⁻¹ * Real.log (1 / (πmin * ε)) with hX
  -- It suffices to show that `⌈X⌉` lies in the mixing set.
  have hmem : (Nat.ceil X) ∈ { t : ℕ | dist t ≤ ε } := by
    show dist (Nat.ceil X) ≤ ε
    refine le_trans (hdecay (Nat.ceil X)) ?_
    -- `(1/πmin)·exp(-gap·⌈X⌉) ≤ (1/πmin)·exp(-gap·X) = (1/πmin)·(πmin·ε) = ε`.
    have hceil : X ≤ (Nat.ceil X : ℝ) := Nat.le_ceil X
    have hexp_arg : - gap * (Nat.ceil X : ℝ) ≤ - gap * X := by nlinarith [hgap, hceil]
    have hmono : Real.exp (- gap * (Nat.ceil X : ℝ)) ≤ Real.exp (- gap * X) :=
      Real.exp_le_exp.mpr hexp_arg
    have hgapX : - gap * X = Real.log (πmin * ε) := by
      have hgne : gap ≠ 0 := ne_of_gt hgap
      have hpe : (0 : ℝ) < πmin * ε := mul_pos hpi hε
      rw [hX]
      have : Real.log (1 / (πmin * ε)) = - Real.log (πmin * ε) := by
        rw [one_div, Real.log_inv]
      rw [this]; field_simp
    have hexpX : Real.exp (- gap * X) = πmin * ε := by
      rw [hgapX, Real.exp_log (mul_pos hpi hε)]
    have hπpos : (0 : ℝ) < 1 / πmin := by positivity
    calc (1 / πmin) * Real.exp (- gap * (Nat.ceil X : ℝ))
        ≤ (1 / πmin) * Real.exp (- gap * X) := by
          exact mul_le_mul_of_nonneg_left hmono (le_of_lt hπpos)
      _ = (1 / πmin) * (πmin * ε) := by rw [hexpX]
      _ = ε := by field_simp
  exact Nat.sInf_le hmem

end MixingTime.LevinPeresWilmer
