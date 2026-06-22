import StabilizerBW.Grade.StratifiedMonotone.Headline
import StabilizerBW.Grade.StratifiedMonotone.ComparisonBCHK
import StabilizerBW.Grade.StratifiedMonotone.FalsifiedBranch
import StabilizerBW.Grade.StratifiedMonotone.MagicStateCheck

/-!
# axiom probe

`#print axioms` on the headline and supporting results.  Target: every headline rests only on the
standard `{propext, Classical.choice, Quot.sound}` base (no `sorry`, no custom `axiom`, no
`native_decide`).
-/

namespace StratifiedMonotone

#print axioms C_ub_PauliWeight
#print axioms C_ub_PauliWeight_via_HW
#print axioms duttaTusharC_nonneg
#print axioms pauliWeightEnumerator_factorises
#print axioms pauliWeightStratumCardinality
#print axioms pauliWeightLECard_closed_form
#print axioms densityPauliCoefficientBound_holds
#print axioms densityPauliCoefficientBoundHW_holds
#print axioms cUB_pw_sharper_than_BCHK
#print axioms C_ub_PauliWeight_refuted_of_witness
#print axioms tState_satisfies_bound
#print axioms ghzState_satisfies_bound
#print axioms wState_satisfies_bound
#print axioms stratState_satisfies_bound

end StratifiedMonotone
