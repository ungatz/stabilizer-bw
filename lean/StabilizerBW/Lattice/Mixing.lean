import StabilizerBW.Lattice.Mixing.EhrenfestProjection
import StabilizerBW.Lattice.Mixing.SpectralGapReuse
import StabilizerBW.Lattice.Mixing.LevinPeresWilmer
import StabilizerBW.Lattice.Mixing.MixingTime
import StabilizerBW.Lattice.Mixing.Asymptotic
import StabilizerBW.Lattice.Mixing.TestPoints
import StabilizerBW.Lattice.Mixing.AxiomProbe

/-!
# MixingTime — aggregator

Explicit mixing-time bound `t_mix(ε) ≤ ⌈ m·log(2^m/ε)/2 ⌉` for the Barnes–Wall
grade distribution under the symmetric Ehrenfest urn Markov chain, via
the Ehrenfest urn / hypercube projection.

* `EhrenfestProjection` — TV-distance / mixing-time definitions and the
  Ehrenfest projection identity `bw_grade_mixing_time_via_ehrenfest`.
* `SpectralGapReuse` — re-export of the development spectral gap `gap = 2/m`.
* `LevinPeresWilmer` — the textbook spectral-gap mixing-time bound
  (Levin–Peres–Wilmer Thm 12.3 / Eq. 12.11–12.12), kernel-proved.
* `MixingTime` (HEADLINE) — `bw_grade_mixing_time_bound`.
* `Asymptotic` — non-rounded `bw_grade_mixing_explicit_constant`.
* `TestPoints` — the three mandated falsification test points.
* `AxiomProbe` — kernel-axiom audit.

Carriers reused (named, literature-attributed; not axioms):
`SymmetricChainSpectralGapBound` (the development), `SymmetricEquilibriumMarginal`
(the development).  No new carriers are introduced.
-/
