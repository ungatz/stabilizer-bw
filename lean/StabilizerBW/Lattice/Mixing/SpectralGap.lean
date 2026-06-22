import StabilizerBW.Lattice.Mixing.SpectralGap.ParityChain
import StabilizerBW.Lattice.Mixing.SpectralGap.StationaryDistribution
import StabilizerBW.Lattice.Mixing.SpectralGap.BWGradeBijection
import StabilizerBW.Lattice.Mixing.SpectralGap.SpectralGapCarrier
import StabilizerBW.Lattice.Mixing.SpectralGap.MixingTimeCarrier
import StabilizerBW.Lattice.Mixing.SpectralGap.Transport
import StabilizerBW.Lattice.Mixing.SpectralGap.AxiomProbe

/-!
# ParityChainBWGradeMixing — aggregator

The BW linear-stratum grade distribution mixes at LaRacuente's parity-chain rate.

* T1 `ParityChain` — the parity-conditioned birth–death chain (row-stochastic).
* T2 `StationaryDistribution` — `π(k) ∝ C(m,k)·θ^k` (detailed balance + stationarity).
* T3 `BWGradeBijection` — the BW grade distribution is `Binomial(m, 1/2)`.
* T4 `SpectralGapCarrier` — `λ₁ ≤ 1 - 4(1-p)/m` (named carrier).
* T5 `MixingTimeCarrier` — `t_sep(η) ≤ (m/(4(1-p)))·(log m + log(2/η))` (named carrier).
* T6 `Transport` — the headline mixing-time bound on the BW grade side.
* T7 `AxiomProbe` — kernel-axiom audit.
-/
