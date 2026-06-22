import StabilizerBW.Grade.TightWitnesses.Roster

/-!
# T2 — The tightness theorems

For the three roster gates whose published ancilla-free T-count is *provably optimal*
(Selinger 2013), the BW grade equals that optimal T-count exactly.  Each is a
kernel-checked equality of natural numbers: the grade side is imported from the corpus
(`Roots.grade_T`, `Roots.grade2_CS`, `Roots.grade2_cT`) and the T-count side is the
literature constant `selingerTOpt` from `Roster.lean`.

These are the chapter's "where the grade is tight" instances: on `T`, `CS`, `cT` the BW
grade is not merely a lower bound on the T-count but matches the Selinger-optimal value.
-/

namespace BWGradeTightWitnesses

open Roots

/-- **`g(T) = T_opt(T) = 1`** (Selinger 2013, Thm 6.2).  The BW grade of the single-qubit
`T` gate equals its optimal ancilla-free T-count. -/
theorem grade_T_tight : Roots.grade Roots.Mat2.T = selingerTOpt SmallGate.T := by
  rw [Roots.grade_T]; rfl

/-- **`g(CS) = T_opt(CS) = 2`** (Selinger 2013, §6.2).  The BW grade of controlled-`S`
equals its optimal ancilla-free T-count. -/
theorem grade_CS_tight : Roots.grade2 Roots.CS = selingerTOpt SmallGate.CS := by
  rw [Roots.grade2_CS]; rfl

/-- **`g(cT) = T_opt(cT) = 3`** (Selinger 2013, §6.2).  The BW grade of controlled-`T`
equals its optimal ancilla-free T-count. -/
theorem grade_cT_tight : Roots.grade2 Roots.cT = selingerTOpt SmallGate.cT := by
  rw [Roots.grade2_cT]; rfl

end BWGradeTightWitnesses
