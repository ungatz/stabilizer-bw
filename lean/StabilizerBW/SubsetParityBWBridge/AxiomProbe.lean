import StabilizerBW.SubsetParityBWBridge.Bridge

/-!
# SubsetParityBWBridge — T9: axiom probe

Kernel-axiom audit of every headline.  Each should reduce to the standard
foundational axioms `{propext, Classical.choice, Quot.sound}`.  No `sorry`, no
custom `axiom`, no `native_decide`.

The named carrier `SymmetricEquilibriumMarginal` is a `def` (a `Prop`),
discharged by the theorem `symmetric_chain_carrier`; it is therefore *not* an axiom and
does not appear below.
-/

namespace SubsetParityBWBridge.AxiomProbe

#print axioms SubsetParityBWBridge.ParityBit.parityBit_count_eq
#print axioms SubsetParityBWBridge.TauMap.tau_fiber_card
#print axioms SubsetParityBWBridge.GradeIsParityCount.gradeOf_eq_tau_countOnes
#print axioms SubsetParityBWBridge.BinomialEnum.parityVec_grade_count
#print axioms SubsetParityBWBridge.Pushforward.grade_fiber_card
#print axioms SubsetParityBWBridge.Distribution.grade_distribution_BW
#print axioms SubsetParityBWBridge.SymmetricEquilibrium.symmetric_chain_carrier
#print axioms SubsetParityBWBridge.Bridge.grade_distribution_eq_symmetric_equilibrium_marginal
#print axioms SubsetParityBWBridge.Bridge.grade_distribution_eq_symmetric_equilibrium_marginal_unconditional
#print axioms SubsetParityBWBridge.Bridge.walshHadamard_grade_inversion

end SubsetParityBWBridge.AxiomProbe
