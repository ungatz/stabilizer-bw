import StabilizerBW.Grade.Kernel.ClosedForm
import StabilizerBW.Roots.BW2
import StabilizerBW.Roots.BW3
import StabilizerBW.Grade.TightWitnesses.Roster

/-!
# T4 — The grade-`g` stratum is **not** a single `T`-count class (Layer 88 follow-on)

Reading (b) of the development: at a fixed non-zero grade `g`, do all operators share a
`T`-count?  The Layer 88 regression witness `(CS, CCZ)` already answers **no**, and we
certify it here as the headline `BWGradeStratumEquivalence`:

* `CS = diag(1,1,1,i)` at `n = 2` has BW grade `2` (`Roots.grade2_CS`) and published
  ancilla-free `T`-count `2` (Selinger 2013, `selingerTOpt CS`);
* `CCZ = diag(1,…,1,−1)` at `n = 3` has BW grade `2` (`Roots.grade3_CCZ`) and published
  ancilla-free `T`-count `7` (Amy–Maslov–Mosca–Roetteler 2013, `selingerTOpt CCZ`).

So `g(CS) = g(CCZ) = 2` while `T(CS) = 2 ≠ 7 = T(CCZ)`: the grade-`2` stratum carries
operators of distinct `T`-count.  The grade does **not** determine the `T`-count on a
fixed stratum — the stratum equivalence is non-trivial.  This is the Branch-B-flavoured
outcome **for the stratum reading**: a fixed-grade stratum is not a single `T`-count class
(while the literal kernel, reading (a), is positively classified in Branch A).

Both `CS` and `CCZ` have grade `2 ≠ 0`, so neither lies in the literal kernel
(consistent with T2): the stratum phenomenon is genuinely about non-zero grades.

All grade values are imported and kernel-checked in the corpus; the `T`-counts are the
independently sourced literature constants of `BWGradeTightWitnesses.Roster`.
-/

namespace BWGradeKernelClassification.StratumEquivalence

open Roots BWGradeTightWitnesses

/-! ## The two grade-`2` witnesses with distinct `T`-counts -/

/-- `CS` and `CCZ` share BW grade `2`. -/
theorem grade_CS_eq_grade_CCZ : Roots.grade2 Roots.CS = Roots.grade3 Roots.CCZ := by
  rw [Roots.grade2_CS, Roots.grade3_CCZ]

/-- Their published ancilla-free `T`-counts differ (`2 ≠ 7`). -/
theorem tcount_CS_ne_tcount_CCZ : selingerTOpt .CS ≠ selingerTOpt .CCZ := by decide

/-- **`BWGradeStratumEquivalence` (headline).** The grade-`2` stratum is not a single
`T`-count class: `CS` and `CCZ` have equal BW grade `2` but distinct published
`T`-counts (`2` vs `7`). -/
def BWGradeStratumEquivalence : Prop :=
  Roots.grade2 Roots.CS = Roots.grade3 Roots.CCZ ∧
  selingerTOpt .CS ≠ selingerTOpt .CCZ

/-- **The stratum-equivalence headline holds.** -/
theorem bwGrade_stratum_equivalence_nontrivial : BWGradeStratumEquivalence :=
  ⟨grade_CS_eq_grade_CCZ, tcount_CS_ne_tcount_CCZ⟩

/-- Explicit, fully quantitative form: grade `2 = 2` while `T`-count `2 ≠ 7`. -/
theorem stratum_witness_explicit :
    Roots.grade2 Roots.CS = 2 ∧ Roots.grade3 Roots.CCZ = 2 ∧
    selingerTOpt .CS = 2 ∧ selingerTOpt .CCZ = 7 ∧
    selingerTOpt .CS ≠ selingerTOpt .CCZ :=
  ⟨Roots.grade2_CS, Roots.grade3_CCZ, rfl, rfl, by decide⟩

/-! ## Both witnesses are outside the literal kernel -/

/-- `CS` has non-zero grade, hence is outside the literal kernel. -/
theorem grade2_CS_ne_zero : Roots.grade2 Roots.CS ≠ 0 := by rw [Roots.grade2_CS]; omega

/-- `CCZ` has non-zero grade, hence is outside the literal kernel. -/
theorem grade3_CCZ_ne_zero : Roots.grade3 Roots.CCZ ≠ 0 := by rw [Roots.grade3_CCZ]; omega

end BWGradeKernelClassification.StratumEquivalence
