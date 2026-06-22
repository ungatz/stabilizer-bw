import StabilizerBW.Lattice.Mixing.SpectralGap.ParityChain
import StabilizerBW.Lattice.Mixing.SpectralGap.StationaryDistribution
import StabilizerBW.Lattice.Mixing.SpectralGap.BWGradeBijection
import StabilizerBW.Lattice.Mixing.SpectralGap.SpectralGapCarrier
import StabilizerBW.Lattice.Mixing.SpectralGap.MixingTimeCarrier
import StabilizerBW.Lattice.Mixing.SpectralGap.Transport
import StabilizerBW.Lattice.Mixing.SpectralGap.AxiomProbe

/-!
# ParityChainBWGrade — aggregator

The BW linear-stratum grade distribution mixes at the symmetric parity-chain rate.

* `ParityChain` — the parity-conditioned birth–death chain (row-stochastic).
* `StationaryDistribution` — `π(k) ∝ C(m,k)·θ^k` (detailed balance + stationarity).
* `BWGradeBijection` — the BW grade distribution is `Binomial(m, 1/2)`.
* `SpectralGapCarrier` — `λ₁ ≤ 1 - 4(1-p)/m` (named carrier).
* `MixingTimeCarrier` — `t_sep(η) ≤ (m/(4(1-p)))·(log m + log(2/η))` (named carrier).
* `Transport` — the headline mixing-time bound on the BW grade side.
* `AxiomProbe` — kernel-axiom audit.
-/
