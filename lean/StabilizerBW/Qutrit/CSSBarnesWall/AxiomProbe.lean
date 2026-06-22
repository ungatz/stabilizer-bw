import StabilizerBW.Qutrit.CSSBarnesWall.FullyGeneralHeadline

/-!
# Axiom probe

`#print axioms` for the round's headline results.  Each must depend only on the
standard kernel axioms `{propext, Classical.choice, Quot.sound}` — no `sorry`, no
`axiom`, and no `native_decide` (which would introduce `Lean.ofReduceBool`).
-/

namespace QutritCSSBW

-- T1: qutrit Reed–Muller codes
#print axioms QRM_params
#print axioms QRM_dual_inclusion
#print axioms qmono_linearIndependent

-- T2: the qutrit-CSS Barnes–Wall lattice
#print axioms BWCssQutrit_params
#print axioms BWCssQutrit_3_1_0

-- T3: the genuine grade and its Clifford invariance
#print axioms gradeQ_diagNegOne
#print axioms gradeQ_clockZ
#print axioms gradeQ_invariant_under_qutrit_clifford

-- T4: TEST 1 corrected (coefficient 2 = ν_{λ₃}(3))
#print axioms qutrit_strict_subset_coefficient_eq_2

-- T5: the extended ring ℤ[ζ₉] and the T-gate
#print axioms qutrit_T_gate_representable

-- T6: TEST 4 corrected (cT vs CCZ incomparability)
#print axioms qutrit_cT_CCZ_incomparability

-- T7: headline
#print axioms qutrit_arithmetic_view_fully_general
#print axioms toy_partial_vs_genuine_full

end QutritCSSBW
