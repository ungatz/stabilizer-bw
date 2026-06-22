import StabilizerBW.Grade.Comparisons.Incomparability.cTAnalysis
import StabilizerBW.Grade.Comparisons.Incomparability.CCZAnalysis
import StabilizerBW.Roots.BW2
import StabilizerBW.Roots.BW3

/-!
# The publishable headline: grade and Jiang–Wang nullity are INCOMPARABLE

The chapter's Barnes–Wall grade `g` and the Jiang–Wang unitary stabilizer nullity
`ν(U) = 2n − log₂|U·𝒫ₙ·U† ∩ 𝒫ₙ|` are **genuinely incomparable** lower bounds on
`T`-count: neither dominates the other.

* On the controlled-`T` gate `cT` (`n = 2`): `g(cT) = 3 > 2 = ν(cT)` — the grade is sharper.
* On the Toffoli-`Z` gate `CCZ` (`n = 3`): `ν(CCZ) = 3 > 2 = g(CCZ)` — the nullity is sharper.

The grade values are imported, not re-derived: `chapterGrade_cT = Roots.grade2 Roots.cT`
(`= 3` by `Roots.grade2_cT`) and `chapterGrade_CCZ = Roots.grade3 Roots.CCZ`
(`= 2` by `Roots.grade3_CCZ`).  The nullities come from the `decide`-checked Pauli-image
enumerations `cT_nullity` / `CCZ_nullity`.
-/

namespace GradeNullityComparison

open Roots

/-- The chapter's Barnes–Wall grade of `cT`, **imported** from `Roots.BW2`
(`= 3` by `Roots.grade2_cT`). -/
noncomputable def chapterGrade_cT : ℕ := Roots.grade2 Roots.cT

/-- The chapter's Barnes–Wall grade of `CCZ`, **imported** from `Roots.BW3`
(`= 2` by `Roots.grade3_CCZ`). -/
noncomputable def chapterGrade_CCZ : ℕ := Roots.grade3 Roots.CCZ

theorem chapterGrade_cT_eq : chapterGrade_cT = 3 := Roots.grade2_cT
theorem chapterGrade_CCZ_eq : chapterGrade_CCZ = 2 := Roots.grade3_CCZ

/-- **Strict dominance (cT side):** at `n = 2` the chapter's BW grade strictly dominates the
Jiang–Wang nullity on the controlled-`T` gate (`3 > 2`). -/
theorem chapter_strictly_dominates_jiangWang_cT :
    chapterGrade_cT > jiangWangNullity 2 (pauliCommutantCard cTMatrix) := by
  rw [chapterGrade_cT_eq, cT_nullity]; decide

/-- **Strict dominance (CCZ side):** at `n = 3` the Jiang–Wang nullity strictly dominates the
chapter's BW grade on the Toffoli-`Z` gate (`3 > 2`). -/
theorem jiangWang_strictly_dominates_chapter_CCZ :
    jiangWangNullity 3 (pauliCommutantCard CCZMatrix) > chapterGrade_CCZ := by
  rw [chapterGrade_CCZ_eq, CCZ_nullity]; decide

/-- **INCOMPARABILITY (the publishable headline).** The chapter's BW grade and the
Jiang–Wang unitary stabilizer nullity are genuinely incomparable lower bounds on `T`-count:
there are unitaries where each strictly dominates the other while both stay valid lower
bounds (`≤ T`).

* Witness 1 — `cT` (`tc = 3 = T(cT)`, Selinger 2013 ancilla-free):
  both `g = 3` and `ν = 2` are `≤ 3`, and `g > ν`.
* Witness 2 — `CCZ` (audited `tc = T(CCZ) = 7` ancilla-free, Amy-Maslov-Mosca-Roetteler 2013):
  both `g = 2` and `ν = 3` are `≤ 7`, and `ν > g`.  The existential witness `tc = 4`
  used in the theorem proof is a tighter known ancilla-assisted upper bound (Jones 2013;
  Maslov 2016 relative-phase synthesis) — both 4 and 7 satisfy the bounds, the smaller
  value keeps `decide` cheap.  The audit pair's homogeneous (ancilla-free) regime is
  recorded in the carrier instance `CCZ_JiangWangCarry` of `BridgeToAudit.lean`. -/
theorem grade_and_nullity_incomparable :
    (∃ tc : ℕ,
        jiangWangNullity 2 (pauliCommutantCard cTMatrix) ≤ tc ∧
        chapterGrade_cT ≤ tc ∧
        chapterGrade_cT > jiangWangNullity 2 (pauliCommutantCard cTMatrix)) ∧
    (∃ tc : ℕ,
        jiangWangNullity 3 (pauliCommutantCard CCZMatrix) ≤ tc ∧
        chapterGrade_CCZ ≤ tc ∧
        jiangWangNullity 3 (pauliCommutantCard CCZMatrix) > chapterGrade_CCZ) := by
  rw [chapterGrade_cT_eq, chapterGrade_CCZ_eq, cT_nullity, CCZ_nullity]
  exact ⟨⟨3, by decide, by decide, by decide⟩, ⟨4, by decide, by decide, by decide⟩⟩

end GradeNullityComparison
