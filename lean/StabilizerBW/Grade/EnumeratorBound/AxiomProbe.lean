import StabilizerBW.Grade.EnumeratorBound.Summary

/-!
# MenuBandwidthAllN / AxiomProbe — T7: axiom audit

We confirm that the all-`n` bandwidth headlines depend only on the standard
foundational axioms `{propext, Classical.choice, Quot.sound}` (no `native_decide`,
no `sorry`, no custom axioms).
-/

namespace MenuBandwidthAllN

-- T1: the n-qubit menu and stabilizer bound
#print axioms octahedron_facet_stab_boundN
#print axioms cliffordFacetN_S
#print axioms cliffordFacetN_N

-- T2: the all-n grade enumerator bound
#print axioms gradeEnumeratorBound_grade0
#print axioms cliffordFacetN_correspondence

-- T3: the bandwidth scaling
#print axioms bandwidth_scaling_allN
#print axioms bandwidth_scaling_allN_general

-- T4: the per-qubit-conserved magic-state gap
#print axioms magic_gap_conserved_allN
#print axioms magic_gap_conserved_lower

-- T5: cross-validation
#print axioms cross_n3_contextgame
#print axioms cross_n4_layer68

-- T6: the combined summary
#print axioms bandwidth_allN_summary

end MenuBandwidthAllN
