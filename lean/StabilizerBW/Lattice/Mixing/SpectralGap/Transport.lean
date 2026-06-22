import StabilizerBW.Lattice.Mixing.SpectralGap.MixingTimeCarrier
import StabilizerBW.Lattice.Mixing.SpectralGap.BWGradeBijection

/-!
# T6 — Transport: the BW grade distribution mixes at LaRacuente's parity-chain rate

This file combines:

* the spectral-gap carrier `LaRacuenteSpectralGapBound` (T4), and
* the BW-grade ↔ `Binomial(m, 1/2)` identity (T3)

to obtain the **headline** mixing-time bound on the BW grade side, and it
*derives* the mixing-time carrier `LaRacuenteMixingTimeBound` (T5) from the
spectral-gap carrier by elementary real analysis.

The genuinely Markov-theoretic input — the spectral gap `λ₁ ≤ 1 - 4(1-p)/m`
(LaRacuente, `noise-2designs-markov-chain.tex` lines 344–372) — enters only as
the named hypothesis `hGap`; everything else is kernel-proved.
-/

namespace ParityChainBWGradeMixing.Transport

open ParityChainBWGradeMixing.SpectralGapCarrier
open ParityChainBWGradeMixing.MixingTimeCarrier
open Real

/-- **Spectral gap ⟹ mixing time.**  From the LaRacuente spectral-gap carrier
(`dist ℓ ≤ m·exp(-(4(1-p)/m)·ℓ)`) we derive the LaRacuente separation
mixing-time bound `t_sep(η) ≤ (m/(4(1-p)))·(log m + log(2/η))`.  This is the
analytic core of the transport: solving `m·exp(-gap·ℓ) ≤ η` for `ℓ`. -/
theorem spectralGap_imp_mixingTime {m : ℕ} {p : ℝ} (hp : 0 < p ∧ p < 1)
    (hm : 1 ≤ m) {dist : ℕ → ℝ} (hGap : LaRacuenteSpectralGapBound p m dist) :
    LaRacuenteMixingTimeBound p m dist := by
  intro η hηpos
  have hpm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h1p : 0 < 1 - p := by linarith [hp.2]
  have hg : 0 < laracuenteGap p m := laracuenteGap_pos hp.2 hm
  have hinv : ((m : ℝ) / (4 * (1 - p))) = 1 / laracuenteGap p m := by
    unfold laracuenteGap; field_simp
  refine ⟨((m : ℝ) / (4 * (1 - p))) * (Real.log m + Real.log (1 / η)), ?_, ?_⟩
  · have hmono : Real.log (1 / η) ≤ Real.log (2 / η) :=
      Real.log_le_log (by positivity) (by rw [div_le_div_iff_of_pos_right hηpos]; linarith)
    have hfac : (0 : ℝ) ≤ (m : ℝ) / (4 * (1 - p)) := by positivity
    nlinarith [hmono, hfac]
  · intro ℓ hℓ
    refine le_trans (hGap ℓ) ?_
    rw [hinv] at hℓ
    have hℓ2 : Real.log m + Real.log (1 / η) ≤ laracuenteGap p m * ℓ := by
      rw [one_div, inv_mul_eq_div, div_le_iff₀ hg] at hℓ; linarith [hℓ]
    have hlogη : Real.log (1 / η) = - Real.log η := by rw [one_div, Real.log_inv]
    have key : Real.log m - Real.log η ≤ laracuenteGap p m * ℓ := by
      rw [hlogη] at hℓ2; linarith
    rw [← Real.exp_log hpm, ← Real.exp_log hηpos, ← Real.exp_add, Real.exp_le_exp]
    linarith [key]

/-- **PRIMARY headline.**  The BW linear-stratum grade distribution mixes at
LaRacuente's parity-chain rate: given the spectral-gap carrier (LaRacuente
`noise-2designs-markov-chain.tex` lines 344–372), there is a mixing time `T`
no larger than `(m/(4(1-p)))·(log m + log(2/η))` after which the separation
distance `dist ℓ` stays below `η`. -/
theorem bwGrade_mixing_time_from_LaRacuente (m : ℕ) (p : ℝ)
    (hp : 0 < p ∧ p < 1) (hm : 1 ≤ m) (η : ℝ) (hη : 0 < η ∧ η < 1)
    (dist : ℕ → ℝ) (hGap : LaRacuenteSpectralGapBound p m dist) :
    ∃ T : ℝ, T ≤ ((m : ℝ) / (4 * (1 - p))) * (Real.log m + Real.log (2 / η)) ∧
      ∀ ℓ : ℕ, T ≤ (ℓ : ℝ) → dist ℓ ≤ η :=
  spectralGap_imp_mixingTime hp hm hGap η hη.1

/-- **Concrete-model corollary.**  Instantiated at LaRacuente's spectral
upper-bound model `laracuenteMixingDistance`, the headline gives the mixing-time
bound for the explicit separation-distance proxy. -/
theorem bwGrade_mixing_time_concrete (m : ℕ) (p : ℝ)
    (hp : 0 < p ∧ p < 1) (hm : 1 ≤ m) (η : ℝ) (hη : 0 < η ∧ η < 1) :
    ∃ T : ℝ, T ≤ ((m : ℝ) / (4 * (1 - p))) * (Real.log m + Real.log (2 / η)) ∧
      ∀ ℓ : ℕ, T ≤ (ℓ : ℝ) → laracuenteMixingDistance p m ℓ ≤ η :=
  bwGrade_mixing_time_from_LaRacuente m p hp hm η hη _
    (laracuenteMixingDistance_spectralGapBound p m)

/-- **SECONDARY headline (equilibrium = binomial), re-exported in `Transport`.**
The `p = 1/2` symmetric-transition equilibrium marginal of the parity chain on
the BW grade side is `Binomial(m, 1/2)`: `P(grade = k) = C(m,k)/2^m`. -/
theorem bwGrade_equilibrium_eq_binomial (m k : ℕ) :
    ((Finset.univ.filter (fun P : T1A.LinPhase m => T1A.gradeOf P = k)).card : ℝ)
        / (Fintype.card (T1A.LinPhase m) : ℝ)
      = (Nat.choose m k : ℝ) / 2 ^ m :=
  ParityChainBWGradeMixing.BWGradeBijection.bwGrade_equilibrium_eq_binomial m k

/-- **SECONDARY headline (spectral gap at `p = 1/2`), re-exported in `Transport`.**
At symmetric transitions the gap specialises to `2/m`, i.e. `λ₁ ≤ 1 - 2/m`. -/
theorem bwGrade_spectral_gap_at_pHalf (m : ℕ) :
    laracuenteGap (1 / 2) m = 2 / (m : ℝ) :=
  ParityChainBWGradeMixing.SpectralGapCarrier.bwGrade_spectral_gap_at_pHalf m

end ParityChainBWGradeMixing.Transport
