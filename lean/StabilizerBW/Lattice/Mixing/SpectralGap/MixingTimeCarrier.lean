import StabilizerBW.Lattice.Mixing.SpectralGap.SpectralGapCarrier

/-!
# The the symmetric Ehrenfest urn mixing-time carrier

This file declares the **separation mixing-time carrier** for the
parity-conditioned birth–death chain.

The numerical content is taken **verbatim** from

> the Krawtchouk diagonalisation,
> the standard Krawtchouk diagonalisation (unpublished working note,
> IU CS, 2026)
> the separation mixing time obeys
> `t_sep(η) ≤ (n/(4(1-p)))·(log n + log(2/η)) = O(n log n)`.

Unlike the spectral-gap carrier , this mixing-time bound is **derived** in
the transport file from the spectral-gap carrier by elementary real
analysis (`spectralGap_imp_mixingTime`); we record it here as a named `Prop` so
that the literature attribution and the exact bound shape are documented in one
place.
-/

namespace ParityChainBWGrade.MixingTimeCarrier

open ParityChainBWGrade.SpectralGapCarrier
open Real

/-- **Mixing-time carrier.**  the symmetric chain's separation-time bound
`t_sep(η) ≤ (m/(4(1-p)))·(log m + log(2/η))`
(Saloff-Coste 1997 §3): for every accuracy `η > 0`
there is a mixing time `T` no larger than the the symmetric Ehrenfest urn bound after which the
separation distance `dist ℓ` stays below `η`. -/
def SymmetricChainMixingTimeBound (p : ℝ) (m : ℕ) (dist : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ T : ℝ, T ≤ ((m : ℝ) / (4 * (1 - p))) * (Real.log m + Real.log (2 / η)) ∧
      ∀ ℓ : ℕ, T ≤ (ℓ : ℝ) → dist ℓ ≤ η

end ParityChainBWGrade.MixingTimeCarrier
