import StabilizerBW.Lattice.Mixing.MixingTime
import StabilizerBW.Lattice.Mixing.Asymptotic
import StabilizerBW.Lattice.Mixing.EhrenfestProjection
import StabilizerBW.Lattice.Mixing.LevinPeresWilmer
import StabilizerBW.Lattice.Mixing.SpectralGapReuse
import StabilizerBW.Lattice.Mixing.TestPoints

/-!
# Axiom probe

`#print axioms` on every headline.  Each must reduce to the standard kernel
axioms `{propext, Classical.choice, Quot.sound}`.  The two literature-attributed
carriers — `SymmetricChainSpectralGapBound` (the development) and
`SymmetricEquilibriumMarginal` (the development) — are named `Prop`s /
hypotheses, **not** axioms, so they do not appear below.
-/

namespace MixingTime.AxiomProbe

#print axioms MixingTime.MixingTime.bw_grade_mixing_time_bound
#print axioms MixingTime.Asymptotic.bw_grade_mixing_explicit_constant
#print axioms MixingTime.EhrenfestProjection.bw_grade_mixing_time_via_ehrenfest
#print axioms MixingTime.EhrenfestProjection.bwGrade_stationary_eq_symmetric_equilibrium
#print axioms MixingTime.LevinPeresWilmer.mixing_time_le_of_spectral_decay
#print axioms MixingTime.SpectralGapReuse.lpw_gap_at_pHalf
#print axioms MixingTime.TestPoints.testpoint_m2
#print axioms MixingTime.TestPoints.testpoint_m4
#print axioms MixingTime.TestPoints.testpoint_m8

end MixingTime.AxiomProbe
