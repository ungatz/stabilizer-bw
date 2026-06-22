import StabilizerBW.Lattice.Mixing.SpectralGap.SpectralGapCarrier

/-!
# Spectral-gap reuse (Levin–Peres–Wilmer convention)

This file re-exports the development spectral-gap carrier
`ParityChainBWGrade.SpectralGapCarrier.SymmetricChainSpectralGapBound`
and records its specialisation at the symmetric-transition point `p = 1/2`,
where the symmetric-chain gap `4(1-p)/m` becomes `2/m`.

In the Levin–Peres–Wilmer convention (Levin–Peres–Wilmer, *Markov Chains and
Mixing Times*, 2nd ed., §12, Eq. 12.2) the **spectral gap** of a reversible
chain is `gap = 1 - λ₂`, and for the Ehrenfest urn on `m` bits one has
`λ₂ = 1 - 2/m`, i.e. `gap = 2/m`.  This matches `symmetricChainGap (1/2) m`
exactly, so no new carrier is introduced: the BW-grade chain's gap is the
the development carrier evaluated at `p = 1/2`.

**NO carrier is defined here** — this file only re-exports and specialises.
-/

namespace MixingTime.SpectralGapReuse

open ParityChainBWGrade.SpectralGapCarrier

/-- The Levin–Peres–Wilmer spectral gap of the BW-grade / Ehrenfest chain at
`p = 1/2`: `gap = 2/m`.  (Re-export of `bwGrade_spectral_gap_at_pHalf`.) -/
theorem lpw_gap_at_pHalf (m : ℕ) : symmetricChainGap (1 / 2) m = 2 / (m : ℝ) :=
  ParityChainBWGrade.SpectralGapCarrier.bwGrade_spectral_gap_at_pHalf m

/-- Positivity of the LPW gap on the physical range `1 ≤ m`. -/
theorem lpw_gap_pos {m : ℕ} (hm : 1 ≤ m) : 0 < symmetricChainGap (1 / 2) m :=
  symmetricChainGap_pos (by norm_num) hm

end MixingTime.SpectralGapReuse
