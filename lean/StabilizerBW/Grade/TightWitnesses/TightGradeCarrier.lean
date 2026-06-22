import StabilizerBW.Grade.TightWitnesses.Tight

/-!
# The `TightGrade` carrier

A structure analogous to `GradeAudit.JiangWangCarry` that bundles, for a concrete gate, the
kernel-checked BW grade together with the independently-sourced literature T-count and the
witnessed equality between them.

The roster gates live at different levels (`n = 1, 2, 3`) and the corpus represents diagonal
operators by different carrier types at each level (`Roots.Mat2`, `Roots.Vec4`,
`Roots.Vec8`) with different grade functions (`Roots.grade`, `Roots.grade2`,
`Roots.grade3`).  We therefore parametrise the carrier over the diagonal type `α` and the
grade function `gradeFn : α → ℕ`, so each concrete instance records the *actual* corpus
grade together with the literature attribution.

Each instance is **unconditional**: there are no carried hypotheses.
-/

namespace TightWitnessRoster

open Roots

/-- A tight-grade certificate for a diagonal operator of type `α` graded by `gradeFn`.

It records the operator `D`, its kernel-checked grade `gradeVal` (via `grade_correct`),
the literature-attested ancilla-free T-count `tOptLiterature` together with a citation
string `tOptRef`, and the `tightness` equality witnessing that the grade meets the
optimal T-count. -/
structure TightGrade (α : Type) (gradeFn : α → ℕ) where
  /-- the diagonal operator -/
  D : α
  /-- the kernel-checked BW grade value -/
  gradeVal : ℕ
  /-- proof that `gradeVal` is genuinely the BW grade of `D` -/
  grade_correct : gradeFn D = gradeVal
  /-- the independently sourced literature ancilla-free T-count -/
  tOptLiterature : ℕ
  /-- the literature citation backing `tOptLiterature` -/
  tOptRef : String
  /-- the kernel-checked tightness equality `g(D) = T_opt(D)` -/
  tightness : gradeVal = tOptLiterature

/-- The grade recorded by a tight-grade certificate equals the literature T-count. -/
theorem TightGrade.grade_eq_tOpt {α : Type} {gradeFn : α → ℕ} (c : TightGrade α gradeFn) :
    gradeFn c.D = c.tOptLiterature := c.grade_correct.trans c.tightness

/-- **Tight-grade certificate for the single-qubit `T` gate** (`n = 1`):
`g(T) = 1 = T_opt(T)`, Selinger 2013 Thm 6.2. -/
def T_TightGrade : TightGrade Roots.Mat2 Roots.grade where
  D := Roots.Mat2.T
  gradeVal := 1
  grade_correct := Roots.grade_T
  tOptLiterature := selingerTOpt SmallGate.T
  tOptRef := selingerTOptRef SmallGate.T
  tightness := rfl

/-- **Tight-grade certificate for controlled-`S`** (`n = 2`):
`g(CS) = 2 = T_opt(CS)`, Selinger 2013 §6.2. -/
def CS_TightGrade : TightGrade Roots.Vec4 Roots.grade2 where
  D := Roots.CS
  gradeVal := 2
  grade_correct := Roots.grade2_CS
  tOptLiterature := selingerTOpt SmallGate.CS
  tOptRef := selingerTOptRef SmallGate.CS
  tightness := rfl

/-- **Tight-grade certificate for controlled-`T`** (`n = 2`):
`g(cT) = 3 = T_opt(cT)`, Selinger 2013 §6.2. -/
def cT_TightGrade : TightGrade Roots.Vec4 Roots.grade2 where
  D := Roots.cT
  gradeVal := 3
  grade_correct := Roots.grade2_cT
  tOptLiterature := selingerTOpt SmallGate.cT
  tOptRef := selingerTOptRef SmallGate.cT
  tightness := rfl

/-- The three tight certificates indeed witness grade-equals-T-count equalities. -/
theorem tight_certificates_correct :
    Roots.grade T_TightGrade.D = T_TightGrade.tOptLiterature ∧
    Roots.grade2 CS_TightGrade.D = CS_TightGrade.tOptLiterature ∧
    Roots.grade2 cT_TightGrade.D = cT_TightGrade.tOptLiterature :=
  ⟨T_TightGrade.grade_eq_tOpt, CS_TightGrade.grade_eq_tOpt, cT_TightGrade.grade_eq_tOpt⟩

end TightWitnessRoster
