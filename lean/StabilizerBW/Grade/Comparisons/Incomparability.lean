import StabilizerBW.Grade.Comparisons.Incomparability.PauliMatrices
import StabilizerBW.Grade.Comparisons.Incomparability.PauliCommutant
import StabilizerBW.Grade.Comparisons.Incomparability.cTAnalysis
import StabilizerBW.Grade.Comparisons.Incomparability.CCZAnalysis
import StabilizerBW.Grade.Comparisons.Incomparability.Incomparability
import StabilizerBW.Grade.Comparisons.Incomparability.BridgeToAudit
import StabilizerBW.Grade.Comparisons.Incomparability.AxiomProbe

/-!
# GradeAuditIncomparable — concrete Pauli-image witnesses that the Barnes–Wall grade and
the Jiang–Wang stabilizer nullity are GENUINELY INCOMPARABLE lower bounds on `T`-count

This directory operationalises the companion narrative chapter's claim that the chapter's BW grade `g`
and the Jiang–Wang unitary stabilizer nullity `ν(U) = 2n − log₂|U·𝒫ₙ·U† ∩ 𝒫ₙ|` "genuinely
differ": neither dominates the other as a lower bound on `T`-count.

## The two witnesses

| Unitary | n | BW grade `g` (chapter) | Jiang–Wang `ν` | Sharper | Gap |
|---------|---|------------------------|----------------|---------|-----|
| `cT`    | 2 | **3** (`chapterGrade_cT`, `Roots.grade2_cT`) | **2** (`cT_nullity`)  | grade | 1 |
| `CCZ`   | 3 | **2** (`chapterGrade_CCZ`, `Roots.grade3_CCZ`) | **3** (`CCZ_nullity`) | nullity | 1 |

## What is unconditional vs. carried

* **Unconditional (kernel-checked over `ℤ[ζ₈]`, no `native_decide`):** the Pauli-image
  cardinalities `pauliCommutantCard cTMatrix = 4` (`cT_commutantCard`) and
  `pauliCommutantCard CCZMatrix = 8` (`CCZ_commutantCard`), each derived by one-by-one
  conjugation of all `16` (resp. `64`) projective Paulis; the nullities `ν(cT) = 2`,
  `ν(CCZ) = 3`; the unitarity of the complex `cT`/`CCZ` gates; and the incomparability
  headline `grade_and_nullity_incomparable`.
* **Imported (kernel-checked elsewhere in the corpus):** the grade values
  `g(cT) = 3` (`Roots.grade2_cT`) and `g(CCZ) = 2` (`Roots.grade3_CCZ`).
* **Carried (cited literature bounds, bundled honestly in `GradeAudit.JiangWangCarry`):**
  the `T`-counts `T(cT) = 3`, `T(CCZ) = 4` and the Jiang–Wang inequality `ν(U) ≤ T(U)`;
  see `cT_JiangWangCarry`, `CCZ_JiangWangCarry`, which set `commutantCard` to the genuinely
  enumerated values, so the carried bound is discharged from verified data.

## Faithfulness of the `ℤ[ζ₈]` model

The Pauli-image enumeration is performed over the computable ring `ℤ[ζ₈]` (`Roots.Z8`),
which makes the matrix conjugations `decide`-checkable in the kernel.  Every relevant entry
(`0, ±1, ±i`, `ζ₈`, `±1`, the phases `±1, ±i`) lives in `ℤ[ζ₈]`, and the inclusion
`ℤ[ζ₈] ↪ ℂ` is an injective ring homomorphism, so the computed cardinalities are exactly the
genuine complex Pauli-image cardinalities.  See `conjDiag_eq` for the proof that the
entrywise diagonal conjugation used in the enumeration is the genuine matrix triple product.

All headline results depend only on `{propext, Classical.choice, Quot.sound}` (see
`AxiomProbe`).
-/
