import StabilizerBW.Grade.Comparisons.Incomparability.cTAnalysis
import StabilizerBW.Grade.Comparisons.Incomparability.CCZAnalysis
import StabilizerBW.GradeAudit.Comparison

/-!
# T6 — Concrete instances of the audit's `JiangWangCarry` structure

We plug the `decide`-checked Pauli-image cardinalities (`cT_commutantCard = 4`,
`CCZ_commutantCard = 8`) into Layer 60's `GradeAudit.JiangWangCarry` structure, producing
**concrete numerical instances** of the audit's carried Jiang–Wang data.

The carrier requires a genuine `n`-qubit complex unitary (`U` together with a unitarity
proof), so here we supply the honest **complex** controlled-`T` and `CCZ` gates and prove
they lie in `Matrix.unitaryGroup`.  The `commutantCard` field is set to the genuinely
enumerated value `pauliCommutantCard cTMatrix` / `pauliCommutantCard CCZMatrix` (computed
over `ℤ[ζ₈]` in T3/T4), so the carried bound `ν(U) ≤ T(U)` is discharged from the verified
cardinality rather than from an asserted number.

* `cT`:  `ν = stabilizerNullity 2 4 = 2 ≤ 3 = T(cT)` (Selinger 2013, "Quantum circuits of T-depth one
  and T-count three", ancilla-free; cT is in the third level of the Clifford hierarchy and admits
  an exact ancilla-free Clifford+T synthesis with 3 T gates).
* `CCZ`: `ν = stabilizerNullity 3 8 = 3 ≤ 7 = T(CCZ)` (Amy-Maslov-Mosca-Roetteler 2013, "A meet-in-the-middle
  algorithm for fast synthesis of depth-optimal quantum circuits", Table I; the standard ancilla-free
  T-count of CCZ matches that of Toffoli via CCZ = (I⊗I⊗H)·CCNOT·(I⊗I⊗H)).  An ancilla-assisted
  optimum is T = 4 (Jones 2013; Maslov 2016 relative-phase synthesis), which also satisfies the
  carrier's `jw_bound` and would yield a tighter audit, but the ancilla-free value is used here
  to match the ancilla-free regime of `cT_JiangWangCarry`.
-/

namespace GradeAuditIncomparable

open Matrix Complex

/-- A primitive `8`-th root of unity `ζ₈ = exp(iπ/4)`, the off-diagonal phase of `cT`. -/
noncomputable def zeta8 : ℂ := Complex.exp (↑(Real.pi / 4) * Complex.I)

theorem zeta8_unit : zeta8 * (starRingEnd ℂ) zeta8 = 1 := by
  rw [Complex.mul_conj]
  have h : ‖zeta8‖ = 1 := by rw [zeta8, Complex.norm_exp]; simp
  rw [Complex.normSq_eq_norm_sq, h]; norm_num

/-- A diagonal matrix with unit-modulus entries is unitary. -/
theorem diag_mem_unitaryGroup {m : Type*} [DecidableEq m] [Fintype m] (d : m → ℂ)
    (h : ∀ i, d i * star (d i) = 1) :
    Matrix.diagonal d ∈ Matrix.unitaryGroup m ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; exact h i

/-! ### The complex controlled-`T` gate -/

/-- Diagonal of the complex `cT = diag(1,1,1,ζ₈)` on `2` qubits. -/
noncomputable def dCTc : Fin (2 ^ 2) → ℂ := fun i => if i = 3 then zeta8 else 1

/-- The complex controlled-`T` unitary. -/
noncomputable def cTMatrixC : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ := Matrix.diagonal dCTc

theorem cTMatrixC_unitary : cTMatrixC ∈ Matrix.unitaryGroup (Fin (2 ^ 2)) ℂ := by
  apply diag_mem_unitaryGroup
  intro i
  fin_cases i <;> simp [dCTc, zeta8_unit]

/-! ### The complex `CCZ` gate -/

/-- Diagonal of the complex `CCZ = diag(1,…,1,-1)` on `3` qubits. -/
def dCCZc : Fin (2 ^ 3) → ℂ := fun i => if i = 7 then (-1) else 1

/-- The complex `CCZ` unitary. -/
noncomputable def CCZMatrixC : Matrix (Fin (2 ^ 3)) (Fin (2 ^ 3)) ℂ := Matrix.diagonal dCCZc

theorem CCZMatrixC_unitary : CCZMatrixC ∈ Matrix.unitaryGroup (Fin (2 ^ 3)) ℂ := by
  apply diag_mem_unitaryGroup
  intro i
  fin_cases i <;> simp [dCCZc]

/-! ### The concrete carries -/

/-- A concrete `GradeAudit.JiangWangCarry 2` instance for `cT`, with the verified
`commutantCard = pauliCommutantCard cTMatrix (= 4)` and worked `tCount = 3`. -/
noncomputable def cT_JiangWangCarry : GradeAudit.JiangWangCarry 2 where
  U := cTMatrixC
  unitary := cTMatrixC_unitary
  commutantCard := pauliCommutantCard cTMatrix
  tCount := 3
  jw_bound := by rw [cT_commutantCard]; decide

/-- A concrete `GradeAudit.JiangWangCarry 3` instance for `CCZ`, with the verified
`commutantCard = pauliCommutantCard CCZMatrix (= 8)` and worked `tCount = 7`
(Amy-Maslov-Mosca-Roetteler 2013, ancilla-free; CCZ = (I⊗I⊗H)·CCNOT·(I⊗I⊗H) inherits
the Toffoli T-count = 7).  The ancilla-assisted optimum is `T = 4` (Jones 2013;
Maslov 2016 relative-phase synthesis), which also satisfies `jw_bound`, but the
ancilla-free value is used here to keep the audit pair homogeneous in synthesis
regime (`cT_JiangWangCarry` is also ancilla-free). -/
noncomputable def CCZ_JiangWangCarry : GradeAudit.JiangWangCarry 3 where
  U := CCZMatrixC
  unitary := CCZMatrixC_unitary
  commutantCard := pauliCommutantCard CCZMatrix
  tCount := 7
  jw_bound := by rw [CCZ_commutantCard]; decide

/-- The Jiang–Wang nullity recorded by `cT_JiangWangCarry` is `2`. -/
theorem cT_JiangWangCarry_nullity : cT_JiangWangCarry.nullity = 2 := by
  rw [GradeAudit.JiangWangCarry.nullity]
  show GradeAudit.stabilizerNullity 2 (pauliCommutantCard cTMatrix) = 2
  rw [cT_commutantCard]; decide

/-- The Jiang–Wang nullity recorded by `CCZ_JiangWangCarry` is `3`. -/
theorem CCZ_JiangWangCarry_nullity : CCZ_JiangWangCarry.nullity = 3 := by
  rw [GradeAudit.JiangWangCarry.nullity]
  show GradeAudit.stabilizerNullity 3 (pauliCommutantCard CCZMatrix) = 3
  rw [CCZ_commutantCard]; decide

end GradeAuditIncomparable
