import StabilizerBW.Lattice.Mixing.MixingTime
import StabilizerBW.Lattice.Mixing.Asymptotic
import StabilizerBW.Lattice.Mixing.EhrenfestProjection
import StabilizerBW.Lattice.Mixing.LevinPeresWilmer
import StabilizerBW.Lattice.Mixing.SpectralGapReuse
import StabilizerBW.Lattice.Mixing.TestPoints

/-!
# T7 — Axiom probe

`#print axioms` on every headline.  Each must reduce to the standard kernel
axioms `{propext, Classical.choice, Quot.sound}`.  The two literature-attributed
carriers — `LaRacuenteSpectralGapBound` (Layer 92) and
`LaRacuenteSymmetricEquilibriumMarginal` (Layer 89) — are named `Prop`s /
hypotheses, **not** axioms, so they do not appear below.
-/

namespace BWParityChainMixingTime.AxiomProbe

#print axioms BWParityChainMixingTime.MixingTime.bw_grade_mixing_time_bound
#print axioms BWParityChainMixingTime.Asymptotic.bw_grade_mixing_explicit_constant
#print axioms BWParityChainMixingTime.EhrenfestProjection.bw_grade_mixing_time_via_ehrenfest
#print axioms BWParityChainMixingTime.EhrenfestProjection.bwGrade_stationary_eq_laracuente
#print axioms BWParityChainMixingTime.LevinPeresWilmer.mixing_time_le_of_spectral_decay
#print axioms BWParityChainMixingTime.SpectralGapReuse.lpw_gap_at_pHalf
#print axioms BWParityChainMixingTime.TestPoints.testpoint_m2
#print axioms BWParityChainMixingTime.TestPoints.testpoint_m4
#print axioms BWParityChainMixingTime.TestPoints.testpoint_m8

end BWParityChainMixingTime.AxiomProbe
