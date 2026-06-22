import StabilizerBW.Grade.Kernel.StratumEquivalence
import StabilizerBW.Grade.Comparisons.Incomparability.Incomparability

/-!
# T5 — Cross-link to Layer 65 (Jiang–Wang nullity) and Layer 76 (tight roster)

Layer 65 (`GradeAuditIncomparable`) established that the BW grade `g` and the Jiang–Wang
unitary stabilizer nullity `ν` are **incomparable** lower bounds on `T`-count.  Their two
kernels are nonetheless not disjoint; this file identifies operators in **both** kernels
and operators in **neither**.

* **In both kernels** — the controlled-`Z` gate `CZ = diag(1,1,1,−1)` at `n = 2`:
  - BW grade `g(CZ) = 0` (`Roots.grade2_CZ`), so `CZ` is in the BW-grade kernel;
  - Jiang–Wang nullity `ν(CZ) = 0` (every projective Pauli conjugates to a projective
    Pauli — `CZ` is Clifford), so `CZ` is in the nullity kernel.
  Hence `CZ` lies in the overlap of the two kernels.

* **In neither kernel** — the controlled-`T` gate `cT = diag(1,1,1,ζ₈)` at `n = 2`:
  - `g(cT) = 3 ≠ 0` (`Roots.grade2_cT`);
  - `ν(cT) = 2 ≠ 0` (`GradeAuditIncomparable.cT_nullity`).

The commutant cardinality of `CZ` is `decide`-checked over `ℤ[ζ₈]` (no `native_decide`),
mirroring the `cT`/`CCZ` enumerations of Layer 65.

## Layer 76 cross-link

The Layer 76 tight roster (`BWGradeTightWitnesses`) records that on the `(CS, CCZ)` pair
the grade and the published `T`-count diverge (`T(CCZ) − T(CS) = 7 − 2 = 5`); see
`StratumEquivalence.stratum_witness_explicit`.  Both `CS` and `CCZ` sit *outside* the BW
kernel (grade `2 ≠ 0`), consistent with the kernel being exactly the grade-`0` sector.
-/

namespace BWGradeKernelClassification.CrossLinkLayer65Layer76

open Roots GradeAuditIncomparable

/-- The diagonal of the controlled-`Z` gate on `2` qubits: `(1, 1, 1, −1)`. -/
def dCZ : Fin 4 → Z8 := fun i => if i = 3 then (-1) else 1

/-- The controlled-`Z` unitary `CZ = diag(1, 1, 1, −1)` on `2` qubits, over `ℤ[ζ₈]`. -/
def CZMatrix : Matrix (Fin 4) (Fin 4) Z8 := Matrix.diagonal dCZ

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The commutant cardinality of `CZ` is exactly `16`** (all `16` projective Paulis at
`n = 2` conjugate to projective Paulis — `CZ` is Clifford). -/
theorem CZ_commutantCard : pauliCommutantCard CZMatrix = 16 := by
  decide

/-- **Jiang–Wang nullity of `CZ` equals `0`**: `CZ` is in the nullity kernel. -/
theorem CZ_nullity : jiangWangNullity 2 (pauliCommutantCard CZMatrix) = 0 := by
  rw [CZ_commutantCard]; decide

/-- **`CZ` lies in BOTH kernels** — BW grade `0` and Jiang–Wang nullity `0`. -/
theorem CZ_in_both_kernels :
    Roots.grade2 Roots.CZ = 0 ∧
    jiangWangNullity 2 (pauliCommutantCard CZMatrix) = 0 :=
  ⟨Roots.grade2_CZ, CZ_nullity⟩

/-- **`cT` lies in NEITHER kernel** — BW grade `3 ≠ 0` and Jiang–Wang nullity `2 ≠ 0`. -/
theorem cT_in_neither_kernel :
    Roots.grade2 Roots.cT ≠ 0 ∧
    jiangWangNullity 2 (pauliCommutantCard cTMatrix) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [Roots.grade2_cT]; omega
  · rw [cT_nullity]; omega

/-! ## Layer 76 cross-link: the tight roster `(CS, CCZ)` sit outside the BW kernel -/

/-- The Layer 76 `(CS, CCZ)` pair is outside the BW-grade kernel (both have grade `2`). -/
theorem CS_CCZ_outside_bwKernel :
    Roots.grade2 Roots.CS ≠ 0 ∧ Roots.grade3 Roots.CCZ ≠ 0 :=
  ⟨StratumEquivalence.grade2_CS_ne_zero, StratumEquivalence.grade3_CCZ_ne_zero⟩

end BWGradeKernelClassification.CrossLinkLayer65Layer76
