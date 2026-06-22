import StabilizerBW.Grade.TightWitnesses.TightGradeCarrier
import StabilizerBW.Grade.TightWitnesses.NonTautology

/-!
# T7 — Axiom probe

`#print axioms` for every headline result of the development.  Each must depend only on the
standard kernel axioms `{propext, Classical.choice, Quot.sound}` (or a subset) — no
`sorry`, no `native_decide` (which would introduce `Lean.ofReduceBool`), no custom axioms.
-/

namespace BWGradeTightWitnesses

-- T2: tightness theorems
#print axioms grade_T_tight
#print axioms grade_CS_tight
#print axioms grade_cT_tight

-- T3: looseness theorems
#print axioms grade_CCZ_loose
#print axioms grade_CCS_loose
#print axioms grade_ccT_loose

-- T4: summary table
#print axioms bw_grade_selinger_roster
#print axioms bw_grade_selinger_tight

-- T5: tight-grade carrier
#print axioms tight_certificates_correct

-- T6: non-tautology certificate
#print axioms tight_tOpt_pos
#print axioms selingerTOpt_values
#print axioms selingerTOpt_independent_of_grade

end BWGradeTightWitnesses
