import StabilizerBW.Qutrit.EisensteinToy.Summary

/-!
# Axiom probe

`#print axioms` for the headline results.  Each must depend only on the standard kernel axioms
`{propext, Classical.choice, Quot.sound}` — no `sorry`, no `axiom`, and no `native_decide`
(which would introduce `Lean.ofReduceBool`).
-/

namespace QutritEis

-- T1: Eisenstein arithmetic + ramification correction
#print axioms Eis.instIsDomain
#print axioms Eis.lam_sq_assoc
#print axioms Eis.one_add_two_omega_not_unit
#print axioms Eis.sqrtNeg3_lam_sq_ne
#print axioms Eis.lam_pow_dvd_lam_pow_mul_iff
#print axioms Eis.toF3

-- T2: Möbius backbone
#print axioms mobT_zetaT
#print axioms zetaT_mobT

-- T3: BW3 lattice and grades
#print axioms gradeEMat_diag_omega
#print axioms gradeEMat_diag_negOne

-- T4: strict-subset closed form (refuted)
#print axioms strict_subset_naive_refuted

-- T5: Möbius closed form (machinery generalises)
#print axioms mobius_machinery_generalises

-- T6: T-count (structural failure)
#print axioms no_isPrimitiveRoot_nine
#print axioms ninth_root_is_cube_root

-- T7: incomparability (fails to reproduce)
#print axioms diagnostic_gates_unrepresentable
#print axioms clifford_phase_has_nonzero_grade

-- T8: headline classification
#print axioms chapter_is_partially_general_at_d3
#print axioms integrality_corrections

end QutritEis
