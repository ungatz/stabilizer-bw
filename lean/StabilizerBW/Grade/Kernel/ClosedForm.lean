import StabilizerBW.Grade.Kernel.LiteralKernel

/-!
# The closed-form (algebraic) description of the literal kernel

** confirmation.**  The literal BW-grade kernel is finitely/algebraically
described as the grade-`0` lattice stabilizer, and it is closed under the algebraic
operations of the diagonal `Cliff+T` sector:

* it contains the identity diagonal `bwId n` (`bwId_mem_kernel`);
* it is closed under composition `bwMul` (`bwMul_mem_kernel`), by the all-`n`
  sub-additivity `Roots.graden_bwMul_le` (`g(D·E) ≤ g(D) + g(E)`).

Hence the kernel is a **submonoid** of the diagonal-operator monoid under composition —
the algebraic closed-form description promised by .  On the full single-qubit
`Mat2` model the same closure holds via the grade sub-multiplicativity `Roots.grade_mul`.

The development headline `bwGradeKernel_closed_form_n1` records the `n = 1` instance: the
one-qubit kernel equals the grade-`0` lattice stabilizer and is closed under composition
and contains the identity (the standard one-qubit Clifford generators `H, S` are
lattice automorphisms of grade `0`, so they lie in this set — see the `Mat2` corroboration
in `LiteralKernel.lean`).

`BWGradeKernelFinitelyPresented n` packages the claim that the kernel admits this finite
algebraic description (identity-containing, composition-closed, equal to the lattice
stabilizer); it is **confirmed** for every `n` by `bwGradeKernel_finitelyPresented`.
-/

namespace KernelClassification.ClosedForm

open Roots KernelClassification

/-! ## Closure of the diagonal kernel under composition -/

/-- The kernel contains the identity diagonal. -/
theorem bwId_mem_kernel (n : ℕ) : bwId n ∈ bwGradeKernel n :=
  LiteralKernel.bwId_mem_kernel n

/-- **The kernel is closed under composition** `bwMul` (grade sub-additivity). -/
theorem bwMul_mem_kernel (n : ℕ) {D E : BWVec n}
    (hD : D ∈ bwGradeKernel n) (hE : E ∈ bwGradeKernel n) :
    bwMul n D E ∈ bwGradeKernel n := by
  have h := graden_bwMul_le n D E
  have hD' : graden n D = 0 := hD
  have hE' : graden n E = 0 := hE
  show graden n (bwMul n D E) = 0
  omega

/-! ## The closed-form proposition -/

/-- **'s carried proposition.** The kernel at `n` admits a finite algebraic
description: it equals the grade-`0` lattice stabilizer, contains the identity, and is
closed under composition. -/
def BWGradeKernelFinitelyPresented (n : ℕ) : Prop :=
  bwGradeKernel n = bwLatticeStabilizer n ∧
  bwId n ∈ bwGradeKernel n ∧
  (∀ D E : BWVec n, D ∈ bwGradeKernel n → E ∈ bwGradeKernel n →
      bwMul n D E ∈ bwGradeKernel n)

/-- ** confirmed (all `n`).** The kernel is finitely/algebraically presented. -/
theorem bwGradeKernel_finitelyPresented (n : ℕ) : BWGradeKernelFinitelyPresented n :=
  ⟨LiteralKernel.bwGradeKernel_eq_latticeStabilizer n, bwId_mem_kernel n,
    fun _ _ hD hE => bwMul_mem_kernel n hD hE⟩

/-- **Dispatch headline (`n = 1`).** The one-qubit kernel is finitely/algebraically
presented (equals the lattice stabilizer, identity-containing, composition-closed). -/
theorem bwGradeKernel_closed_form_n1 : BWGradeKernelFinitelyPresented 1 :=
  bwGradeKernel_finitelyPresented 1

/-! ## Single-qubit `Mat2` closure (full operator model) -/

/-- The single-qubit `Mat2` kernel contains the identity. -/
theorem II_mem_mat2GradeKernel : Mat2.II ∈ LiteralKernel.mat2GradeKernel :=
  LiteralKernel.II_mem_mat2GradeKernel

/-- **The single-qubit `Mat2` kernel is closed under composition** (grade
sub-multiplicativity `Roots.grade_mul`). -/
theorem mat2_mul_mem_kernel {M N : Mat2}
    (hM : M ∈ LiteralKernel.mat2GradeKernel) (hN : N ∈ LiteralKernel.mat2GradeKernel) :
    M * N ∈ LiteralKernel.mat2GradeKernel := by
  have h := grade_mul M N
  have hM' : grade M = 0 := hM
  have hN' : grade N = 0 := hN
  show grade (M * N) = 0
  omega

end KernelClassification.ClosedForm
