import StabilizerBW.Grade.Comparisons.Incomparability.Incomparability
import StabilizerBW.Grade.Comparisons.Incomparability.BridgeToAudit

/-!
# T7 — Axiom probe

`#print axioms` for the headline results.  Each must depend only on the standard kernel
axioms `{propext, Classical.choice, Quot.sound}` (or a subset) — no `sorry`, no
`native_decide` (which would introduce `Lean.ofReduceBool`), no custom axioms.
-/

namespace GradeAuditIncomparable

#print axioms cT_commutantCard
#print axioms CCZ_commutantCard
#print axioms cT_nullity
#print axioms CCZ_nullity
#print axioms chapter_strictly_dominates_jiangWang_cT
#print axioms jiangWang_strictly_dominates_chapter_CCZ
#print axioms grade_and_nullity_incomparable
#print axioms cT_JiangWangCarry
#print axioms CCZ_JiangWangCarry

end GradeAuditIncomparable
