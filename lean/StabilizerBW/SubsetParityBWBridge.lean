import StabilizerBW.SubsetParityBWBridge.ParityBit
import StabilizerBW.SubsetParityBWBridge.TauMap
import StabilizerBW.SubsetParityBWBridge.BinomialEnum
import StabilizerBW.SubsetParityBWBridge.GradeIsParityCount
import StabilizerBW.SubsetParityBWBridge.Pushforward
import StabilizerBW.SubsetParityBWBridge.Distribution
import StabilizerBW.SubsetParityBWBridge.SymmetricEquilibrium
import StabilizerBW.SubsetParityBWBridge.Bridge
import StabilizerBW.SubsetParityBWBridge.TestPoints
import StabilizerBW.SubsetParityBWBridge.AxiomProbe

/-!
# SubsetParityBWBridge — aggregator

The Barnes–Wall linear-stratum grade enumerator is the symmetric-transition
equilibrium parity-count marginal of the symmetric subset-parity Markov chain.

Headlines:
* `SubsetParityBWBridge.ParityBit.parityBit_count_eq`
* `SubsetParityBWBridge.TauMap.tau_fiber_card`
* `SubsetParityBWBridge.GradeIsParityCount.gradeOf_eq_tau_countOnes`
* `SubsetParityBWBridge.BinomialEnum.parityVec_grade_count`
* `SubsetParityBWBridge.Pushforward.grade_fiber_card`
* `SubsetParityBWBridge.Distribution.grade_distribution_BW`
* `SubsetParityBWBridge.SymmetricEquilibrium.symmetric_chain_carrier`
* `SubsetParityBWBridge.Bridge.grade_distribution_eq_symmetric_equilibrium_marginal`
* `SubsetParityBWBridge.Bridge.walshHadamard_grade_inversion`
-/
