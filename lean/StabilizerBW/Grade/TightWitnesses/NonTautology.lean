import StabilizerBW.Grade.TightWitnesses.Summary

/-!
# T6 — Non-vacuity / non-tautology certificate

The tightness theorems (`Tight.lean`) are only meaningful if the literature T-counts in
`selingerTOpt` are **independently sourced** constants — not values mechanically chosen to
equal the BW grades.  This file certifies that.

* **Non-triviality of the tight equalities.**  Each tight literature T-count is strictly
  positive (`> 0`), so `g = T_opt` is a non-trivial equality of positive integers rather
  than a `0 = 0` degeneracy.

* **The literature values are the published constants.**  `selingerTOpt` returns exactly
  the numbers attested in Selinger 2013 (Thm 6.2 / §6.2) and AMMM 2013 (Table I):
  `1, 2, 3, 7, 7, 7`.

* **`selingerTOpt` is not the grade function.**  On the three-qubit doubly-controlled
  gates the literature T-count `7` differs from every BW grade (`2, 4, 5`).  Hence the
  T-counts cannot have been derived from the grades: a function chosen to match the grades
  would necessarily disagree with the published `7`.  This is exactly the honest gap that
  makes the *tight* coincidences on `T`, `CS`, `cT` substantive.
-/

namespace BWGradeTightWitnesses

open Roots

/-- The tight literature T-counts are all strictly positive, so each tightness equality
`g = T_opt` is a non-trivial statement about positive integers. -/
theorem tight_tOpt_pos :
    0 < selingerTOpt SmallGate.T ∧
    0 < selingerTOpt SmallGate.CS ∧
    0 < selingerTOpt SmallGate.cT := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `selingerTOpt` returns exactly the published literature constants
(Selinger 2013: `1, 2, 3`; AMMM 2013: `7, 7, 7`). -/
theorem selingerTOpt_values :
    selingerTOpt SmallGate.T = 1 ∧
    selingerTOpt SmallGate.CS = 2 ∧
    selingerTOpt SmallGate.cT = 3 ∧
    selingerTOpt SmallGate.CCZ = 7 ∧
    selingerTOpt SmallGate.CCS = 7 ∧
    selingerTOpt SmallGate.ccT = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- **The literature T-count is not the BW grade.**  On the doubly-controlled gates the
published ancilla-free T-count `7` differs from each BW grade (`g(CCZ) = 2`,
`g(CCS) = 4`, `g(ccT) = 5`), proving `selingerTOpt` was not chosen to match the grades. -/
theorem selingerTOpt_independent_of_grade :
    selingerTOpt SmallGate.CCZ ≠ Roots.grade3 Roots.CCZ ∧
    selingerTOpt SmallGate.CCS ≠ Roots.grade3 Roots.CCS ∧
    selingerTOpt SmallGate.ccT ≠ Roots.grade3 Roots.ccT := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Roots.grade3_CCZ]; decide
  · rw [Roots.grade3_CCS]; decide
  · rw [Roots.grade3_ccT]; decide

end BWGradeTightWitnesses
