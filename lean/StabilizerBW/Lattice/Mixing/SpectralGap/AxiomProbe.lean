import StabilizerBW.Lattice.Mixing.SpectralGap.Transport
import StabilizerBW.Lattice.Mixing.SpectralGap.StationaryDistribution

/-!
# Axiom probe

`#print axioms` on every headline.  Each must reduce to the standard kernel
axioms `{propext, Classical.choice, Quot.sound}`; the two carried predicates
(`SymmetricChainSpectralGapBound`, `SymmetricChainMixingTimeBound`) are named `Prop`s /
hypotheses, **not** axioms, so they do not appear here.
-/

namespace ParityChainBWGrade.AxiomProbe

open ParityChainBWGrade

#print axioms ParityChain.parityChain_transition_sums_one
#print axioms StationaryDistribution.parityChain_stationary
#print axioms BWGradeBijection.bwGrade_eq_binomial
#print axioms Transport.bwGrade_mixing_time_from_symmetric_chain
#print axioms Transport.bwGrade_equilibrium_eq_binomial
#print axioms Transport.bwGrade_spectral_gap_at_pHalf

end ParityChainBWGrade.AxiomProbe
