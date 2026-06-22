import StabilizerBW.Grade.Kernel.AmbiguityResolution
import StabilizerBW.Roots.LowerBoundAllN
import StabilizerBW.Roots.Tcount
import StabilizerBW.Roots.Filtration

/-!
# The literal kernel is the grade-`0` lattice stabilizer (Clifford-type sector)

** (positive).**  The literal BW-grade kernel at every `n` has a finitely
described, algebraic form: it is exactly the set of diagonal operators that preserve the
Barnes–Wall lattice `BW_n` (no `λ`-adic depth).  This is the all-`n` statement

  `bwGradeKernel n = bwLatticeStabilizer n`,

proved from the core characterization `mem_bwGradeKernel_iff`.  We record the `n = 1` and
`n = 2` instances as the structural strawman headlines `bwGradeKernel_eq_Clifford_n1` /
`bwGradeKernel_eq_Clifford_n2` (here "Clifford" denotes the grade-`0`
lattice-automorphism sector, which on the diagonal `Cliff+T` sector is the standard
Clifford subgroup).

We also pin down the **non-triviality** of the classification:

* the identity diagonal `bwId n` lies in the kernel (`bwId_mem_kernel`);
* the maximal `T`-type monomial `bwT (n+1)` does **not** (`bwT_not_mem_kernel`), since
  `graden (n+1) (bwT (n+1)) = 2(n+1) − 1 ≥ 1` (`Roots.graden_bwT_eq`).

So the kernel is a proper, non-empty subset — the grade genuinely separates Clifford-type
operators (grade `0`) from `T`-bearing operators (grade `> 0`).

## Single-qubit (`Mat2`) corroboration

For the full single-qubit operator model `Roots.Mat2` (not just the diagonal sector) we
record the kernel `mat2GradeKernel = {M : Roots.grade M = 0}` and verify that the Clifford
generators `S`, `X` and the identity `II` lie in it, while the non-Clifford `T` does not —
exactly the `g(T) = 1` separation of `Roots.grade_T`.
-/

namespace KernelClassification.LiteralKernel

open Roots KernelClassification

/-! ## the all-`n` closed form -/

/-- **, all `n`.** The literal BW-grade kernel equals the grade-`0` lattice
stabilizer (the Clifford-type, lattice-automorphism sector). -/
theorem bwGradeKernel_eq_latticeStabilizer (n : ℕ) :
    bwGradeKernel n = bwLatticeStabilizer n := by
  ext D
  rw [mem_bwGradeKernel_iff, mem_bwLatticeStabilizer]

/-- **Dispatch headline (`n = 1`).** The kernel at one qubit is the grade-`0` lattice
stabilizer (Clifford-type sector). -/
theorem bwGradeKernel_eq_Clifford_n1 :
    bwGradeKernel 1 = bwLatticeStabilizer 1 := bwGradeKernel_eq_latticeStabilizer 1

/-- **Dispatch headline (`n = 2`).** The kernel at two qubits is the grade-`0` lattice
stabilizer (Clifford-type sector). -/
theorem bwGradeKernel_eq_Clifford_n2 :
    bwGradeKernel 2 = bwLatticeStabilizer 2 := bwGradeKernel_eq_latticeStabilizer 2

/-! ## Non-triviality: identity is in, the maximal `T`-monomial is out -/

/-- The identity diagonal lies in the kernel at every `n`. -/
theorem bwId_mem_kernel (n : ℕ) : bwId n ∈ bwGradeKernel n := by
  rw [mem_bwGradeKernel_iff]
  intro v hv
  show inBW n (bwMul n (bwSmul n (Z8.lam ^ 0) (bwId n)) v)
  rw [pow_zero, bwSmul_one, bwId_mul]
  exact hv

/-- The maximal-degree `T`-type monomial `bwT (n+1)` is **not** in the kernel: its grade is
`2(n+1) − 1 ≥ 1`.  This is the witness that the kernel is a proper subset. -/
theorem bwT_not_mem_kernel (n : ℕ) : bwT (n + 1) ∉ bwGradeKernel (n + 1) := by
  rw [mem_bwGradeKernel]
  rw [graden_bwT_eq n]
  omega

/-- Consequently the kernel is a **proper** subset of all diagonal operators (it omits
`bwT (n+1)`). -/
theorem bwGradeKernel_proper (n : ℕ) : bwGradeKernel (n + 1) ≠ Set.univ := by
  intro h
  exact bwT_not_mem_kernel n (by rw [h]; trivial)

/-! ## Single-qubit `Mat2` corroboration -/

/-- The single-qubit grade kernel on the full `Mat2` operator model. -/
def mat2GradeKernel : Set Mat2 := {M | Roots.grade M = 0}

@[simp] theorem mem_mat2GradeKernel (M : Mat2) :
    M ∈ mat2GradeKernel ↔ Roots.grade M = 0 := Iff.rfl

/-- On `Mat2`, kernel membership is equivalent to `λ^0·M = M` preserving `L₃`. -/
theorem mem_mat2GradeKernel_iff (M : Mat2) :
    M ∈ mat2GradeKernel ↔ gradeLE M 0 := by
  constructor
  · intro h
    have hmem : grade M ∈ {k | gradeLE M k} := Nat.sInf_mem (gradeLE_nonempty M)
    rw [show grade M = 0 from h] at hmem
    exact hmem
  · intro h
    exact Nat.le_zero.mp (Nat.sInf_le h)

/-- The Clifford generator `S` lies in the single-qubit kernel. -/
theorem S_mem_mat2GradeKernel : Mat2.S ∈ mat2GradeKernel := grade_S

/-- The Clifford generator `X` lies in the single-qubit kernel. -/
theorem X_mem_mat2GradeKernel : Mat2.X ∈ mat2GradeKernel := grade_X

/-- The identity lies in the single-qubit kernel. -/
theorem II_mem_mat2GradeKernel : Mat2.II ∈ mat2GradeKernel := grade_II

/-- The non-Clifford `T` does **not** lie in the single-qubit kernel (`g(T) = 1`). -/
theorem T_not_mem_mat2GradeKernel : Mat2.T ∉ mat2GradeKernel := by
  rw [mem_mat2GradeKernel, grade_T]
  omega

end KernelClassification.LiteralKernel
