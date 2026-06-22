import StabilizerBW.Grade.TightWitnesses.Roster

/-!
# The looseness theorems

For the three-qubit doubly-controlled gates the BW grade is a *strict* lower bound on the
published ancilla-free T-count: the grade undershoots the literature value.  This records
the honest gap that the chapter's later remarks (Remark `rem:av-grade-incomparable`)
already discuss — the BW grade certifies a lower bound but does not always meet the
synthesis cost.

| Gate  | BW grade | published T-count | gap |
|-------|----------|-------------------|-----|
| `CCZ` | `2`      | `7` (AMMM 2013)   | `5` |
| `CCS` | `4`      | `7` (AMMM 2013)   | `3` |
| `ccT` | `5`      | `7` (AMMM 2013)   | `2` |

The grade values are imported kernel-checked facts (`Roots.grade3_CCZ`,
`Roots.grade3_CCS`, `Roots.grade3_ccT`); the T-counts are the AMMM 2013 Table I
Toffoli-class constants from `Roster.lean`.
-/

namespace TightWitnessRoster

open Roots

/-- **`g(CCZ) = 2 < 7 = T_opt(CCZ)`** (AMMM 2013, Table I).  The BW grade strictly
undershoots the optimal ancilla-free T-count of `CCZ`. -/
theorem grade_CCZ_loose : Roots.grade3 Roots.CCZ < selingerTOpt SmallGate.CCZ := by
  rw [Roots.grade3_CCZ]; decide

/-- **`g(CCS) = 4 < 7`** (AMMM 2013, Table I, Toffoli class).  The BW grade strictly
undershoots the published ancilla-free T-count of `CCS`. -/
theorem grade_CCS_loose : Roots.grade3 Roots.CCS < selingerTOpt SmallGate.CCS := by
  rw [Roots.grade3_CCS]; decide

/-- **`g(ccT) = 5 < 7`** (AMMM 2013, Table I, Toffoli class).  The looseness for `ccT` is
confirmed: the grade `5` is strictly below the published ancilla-free T-count `7`. -/
theorem grade_ccT_loose : Roots.grade3 Roots.ccT < selingerTOpt SmallGate.ccT := by
  rw [Roots.grade3_ccT]; decide

end TightWitnessRoster
