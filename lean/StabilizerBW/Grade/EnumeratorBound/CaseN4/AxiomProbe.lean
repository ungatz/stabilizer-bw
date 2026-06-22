import StabilizerBW.Grade.EnumeratorBound.CaseN4.CrossValidation

/-!
# BandwidthN4 / AxiomProbe — T7: axiom audit

Confirms that every headline of the n=4 bandwidth-scaling development depends only
on the standard kernel axioms `{propext, Classical.choice, Quot.sound}` — no
`sorry`, no `native_decide`, no `@[implemented_by]`.  The only mathematical
"carry" is the explicit named hypothesis
`GradeEnumeratorBoundFacetCorrespondence`, which is a hypothesis (not an axiom)
and is discharged unconditionally for the all-ones facet
(`cliffordFacet4_correspondence`).
-/

namespace CliffordMenuN4

-- T1: the proved n=4 stabilizer facet bound (`CliffordFacetClassicalBound4`).
#print axioms octahedron_facet_stab_bound4
#print axioms allZPlus_facet_value

-- T2: the all-ones facet's ℓ¹-norm and normalisation.
#print axioms cliffordFacet4_S
#print axioms cliffordFacet4_N
#print axioms cliffordFacet4_violation_le_zero_of_stab

-- T3: the grade-enumerator bound and its unconditional all-ones instance.
#print axioms grade4_triv16
#print axioms cliffordFacet4_correspondence
#print axioms coeff_l1_le_grade_enumerator

-- T4: the closed-form bandwidth scaling.
#print axioms bandwidth_scaling_n4
#print axioms bandwidth_scaling_n4_cliffordFacet

-- T5: cross-validation against n=2 (CHSH) and n=3 (9-Pauli).
#print axioms cross_chsh_gap
#print axioms n3_gap
#print axioms cross_n3_contextgame
#print axioms n4_matches_n3

-- T6: the concrete n=4 magic-state gap.
#print axioms concrete_gap_n4
#print axioms concrete_gap_n4_lower

end CliffordMenuN4
