import StabilizerBW.Lattice.Mixing.EhrenfestProjection
import StabilizerBW.Lattice.Mixing.SpectralGapReuse
import StabilizerBW.Lattice.Mixing.LevinPeresWilmer
import StabilizerBW.Lattice.Mixing.MixingTime
import StabilizerBW.Lattice.Mixing.Asymptotic
import StabilizerBW.Lattice.Mixing.TestPoints
import StabilizerBW.Lattice.Mixing.AxiomProbe

/-!
# BWParityChainMixingTime — aggregator

Explicit mixing-time bound `t_mix(ε) ≤ ⌈ m·log(2^m/ε)/2 ⌉` for the Barnes–Wall
grade distribution under LaRacuente's symmetric-transitions Markov chain, via
the Ehrenfest urn / hypercube projection.

* T1 `EhrenfestProjection` — TV-distance / mixing-time definitions and the
  Ehrenfest projection identity `bw_grade_mixing_time_via_ehrenfest`.
* T2 `SpectralGapReuse` — re-export of the Layer-92 spectral gap `gap = 2/m`.
* T3 `LevinPeresWilmer` — the textbook spectral-gap mixing-time bound
  (Levin–Peres–Wilmer Thm 12.3 / Eq. 12.11–12.12), kernel-proved.
* T4 `MixingTime` (HEADLINE) — `bw_grade_mixing_time_bound`.
* T5 `Asymptotic` — non-rounded `bw_grade_mixing_explicit_constant`.
* T6 `TestPoints` — the three mandated falsification test points.
* T7 `AxiomProbe` — kernel-axiom audit.

Carriers reused (named, literature-attributed; not axioms):
`LaRacuenteSpectralGapBound` (Layer 92), `LaRacuenteSymmetricEquilibriumMarginal`
(Layer 89).  No new carriers are introduced.
-/
