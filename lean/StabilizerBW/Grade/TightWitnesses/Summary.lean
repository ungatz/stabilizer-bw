import StabilizerBW.Grade.TightWitnesses.Tight
import StabilizerBW.Grade.TightWitnesses.Loose

/-!
# T4 — The summary table

A single statement collecting the entire roster: the three tight equalities
(`g = T_opt`) and the three strict-looseness inequalities (`g < T_opt`), all against the
literature-attested ancilla-free T-counts encoded in `selingerTOpt`.
-/

namespace BWGradeTightWitnesses

open Roots

/-- **The full BW-grade / Selinger-T-count roster table.**

Tight rows (`g = T_opt`, Selinger 2013): `T`, `CS`, `cT`.
Loose rows (`g < T_opt`, AMMM 2013): `CCZ`, `CCS`, `ccT`. -/
theorem bw_grade_selinger_roster :
    -- tight rows
    (Roots.grade Roots.Mat2.T = selingerTOpt SmallGate.T) ∧
    (Roots.grade2 Roots.CS = selingerTOpt SmallGate.CS) ∧
    (Roots.grade2 Roots.cT = selingerTOpt SmallGate.cT) ∧
    -- loose rows
    (Roots.grade3 Roots.CCZ < selingerTOpt SmallGate.CCZ) ∧
    (Roots.grade3 Roots.CCS < selingerTOpt SmallGate.CCS) ∧
    (Roots.grade3 Roots.ccT < selingerTOpt SmallGate.ccT) :=
  ⟨grade_T_tight, grade_CS_tight, grade_cT_tight,
   grade_CCZ_loose, grade_CCS_loose, grade_ccT_loose⟩

/-- **The tight roster as explicit numeric equalities.**
`g(T) = 1`, `g(CS) = 2`, `g(cT) = 3`, matching the Selinger-optimal ancilla-free
T-counts. -/
theorem bw_grade_selinger_tight :
    (Roots.grade Roots.Mat2.T = 1) ∧
    (Roots.grade2 Roots.CS = 2) ∧
    (Roots.grade2 Roots.cT = 3) :=
  ⟨Roots.grade_T, Roots.grade2_CS, Roots.grade2_cT⟩

end BWGradeTightWitnesses
