import StabilizerBW.Grade.AlgorithmAudit.AQC.Summary

/-!
# T7 — Axiom probe

`#print axioms` for the AQC audit headlines.  Each must depend only on the standard
kernel axioms `{propext, Classical.choice, Quot.sound}` (or a subset) — no `sorry`,
no `native_decide` (which would introduce `Lean.ofReduceBool`), no custom axioms.
-/

namespace GradeAudit

-- Headline closed-form grades
#print axioms qpe_grade
#print axioms aa_grade
#print axioms hhl_grade
#print axioms vqe_grade

-- Comparison theorems
#print axioms qpe_grade_dominates_jiangWang
#print axioms aa_grade_dominates_jiangWang
#print axioms hhl_grade_dominates_jiangWang
#print axioms vqe_grade_dominates_jiangWang

-- Concrete carries and their nullities
#print axioms qpeCarry
#print axioms aaCarry
#print axioms hhlCarry
#print axioms vqeCarry
#print axioms aqc_carries_substantive

-- Summary table
#print axioms gradeAudit_summary_AQC

end GradeAudit
