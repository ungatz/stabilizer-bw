import StabilizerBW.Grade.Kernel.LiteralKernel
import StabilizerBW.Grade.Kernel.ClosedForm
import StabilizerBW.Grade.Kernel.StratumEquivalence
import StabilizerBW.Grade.Kernel.CrossLinkLayer65Layer76
import StabilizerBW.Grade.Kernel.SelingerAttributionCorrection

/-!
# T6 — Axiom probe

`#print axioms` for every headline result of the development.  Each must depend only on the
standard kernel axioms `{propext, Classical.choice, Quot.sound}` (or a subset) — no
`sorry`, no `native_decide` (which would introduce `Lean.ofReduceBool`), no custom axioms.
-/

namespace BWGradeKernelClassification

-- T1: core characterization
#print axioms mem_bwGradeKernel_iff
#print axioms mem_bwLatticeStabilizer_iff

-- T2: literal kernel = lattice stabilizer (Clifford-type sector)
#print axioms LiteralKernel.bwGradeKernel_eq_latticeStabilizer
#print axioms LiteralKernel.bwGradeKernel_eq_Clifford_n1
#print axioms LiteralKernel.bwGradeKernel_eq_Clifford_n2
#print axioms LiteralKernel.bwId_mem_kernel
#print axioms LiteralKernel.bwT_not_mem_kernel
#print axioms LiteralKernel.bwGradeKernel_proper
#print axioms LiteralKernel.S_mem_mat2GradeKernel
#print axioms LiteralKernel.T_not_mem_mat2GradeKernel

-- T3: closed-form / finite presentation
#print axioms ClosedForm.bwMul_mem_kernel
#print axioms ClosedForm.bwGradeKernel_finitelyPresented
#print axioms ClosedForm.bwGradeKernel_closed_form_n1
#print axioms ClosedForm.mat2_mul_mem_kernel

-- T4: stratum equivalence
#print axioms StratumEquivalence.bwGrade_stratum_equivalence_nontrivial
#print axioms StratumEquivalence.stratum_witness_explicit

-- T5: cross-link
#print axioms CrossLinkLayer65Layer76.CZ_in_both_kernels
#print axioms CrossLinkLayer65Layer76.cT_in_neither_kernel
#print axioms CrossLinkLayer65Layer76.CS_CCZ_outside_bwKernel

-- T6: corrigendum
#print axioms SelingerAttributionCorrection.selinger_attribution_corrigendum

end BWGradeKernelClassification
