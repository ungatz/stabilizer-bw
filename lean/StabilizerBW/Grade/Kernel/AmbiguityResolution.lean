import StabilizerBW.Roots.UpperBoundAllN

/-!
# T1 — Resolving the kernel-vs-stratum ambiguity, and the core kernel object

The development asks for an algebraic characterization of the kernel of the Barnes–Wall
grade homomorphism `g_n : Cliff+T_n → ℕ`.  Per the Phase 0.5 audit the codomain is `ℕ`
(the `λ`-adic valuation of the down-set Möbius transform, `Roots.graden`), **not** `ℤ/8`.

There are two readings of "the kernel":

* **(a) Literal kernel** — `ker(g_n) = {U : g_n(U) = 0}`.  This is the subset of operators
  with no `λ`-adic depth.  It is handled in `LiteralKernel.lean` (T2) and `ClosedForm.lean`
  (T3).
* **(b) Grade-`g` stratum equivalence** — the equivalence classes of operators sharing a
  fixed non-zero grade `g`, up to `T`-count.  This is where the Layer 88 `(CS, CCZ)`
  phenomenon lives and is handled in `StratumEquivalence.lean` (T4).

This file fixes the **core object** for reading (a): the grade-`0` kernel
`bwGradeKernel n` of the all-`n` diagonal grade `Roots.graden`, together with its basic
characterization `D ∈ bwGradeKernel n ↔ gradeLEn n D 0`, i.e. membership is equivalent to
`λ^0·D = D` already preserving the lattice `BW_n` (no `λ`-adic depth).

The grade model is the **diagonal sector** `Roots.BWVec n` with the lattice `inBW`,
the diagonal action `bwMul`, and the grade `graden n D = sInf {k | gradeLEn n D k}`
developed in `Roots/BWn.lean` and `Roots/UpperBoundAllN.lean`.  Every diagonal operator
has finite grade (`gradeLEn_top`), so the defining set is always non-empty.
-/

namespace BWGradeKernelClassification

open Roots

/-- Scaling a `BW_n`-vector by the unit `1` is the identity. -/
theorem bwSmul_one (n : ℕ) (D : BWVec n) : bwSmul n 1 D = D := by
  induction n with
  | zero => show (1 : Z8) * (show Z8 from D) = D; exact one_mul _
  | succ m ih => obtain ⟨a, b⟩ := D; simp only [bwSmul_succ, ih]

/-- **The literal BW-grade kernel at `n`**: the diagonal operators of grade `0`. -/
def bwGradeKernel (n : ℕ) : Set (BWVec n) := {D | graden n D = 0}

/-- **The grade-`0` lattice stabilizer (Clifford-type sector)**: the diagonal operators
that already preserve `BW_n` with no `λ`-adic scaling (`gradeLEn n D 0`, i.e. `λ^0·D = D`
maps `BW_n` into `BW_n`).  This is the candidate finite/algebraic description of the
kernel; `LiteralKernel.bwGradeKernel_eq_latticeStabilizer` proves it equals the kernel. -/
def bwLatticeStabilizer (n : ℕ) : Set (BWVec n) := {D | gradeLEn n D 0}

@[simp] theorem mem_bwGradeKernel (n : ℕ) (D : BWVec n) :
    D ∈ bwGradeKernel n ↔ graden n D = 0 := Iff.rfl

@[simp] theorem mem_bwLatticeStabilizer (n : ℕ) (D : BWVec n) :
    D ∈ bwLatticeStabilizer n ↔ gradeLEn n D 0 := Iff.rfl

/-- **Core characterization (T1).** A diagonal operator lies in the grade kernel iff its
grade is `0` iff `λ^0·D = D` already preserves the lattice `BW_n`.  Equivalently the
kernel is the grade-`0` lattice-stabilizer (Clifford-type) sector. -/
theorem mem_bwGradeKernel_iff (n : ℕ) (D : BWVec n) :
    D ∈ bwGradeKernel n ↔ gradeLEn n D 0 := by
  constructor
  · intro h
    have hmem : graden n D ∈ {k | gradeLEn n D k} := Nat.sInf_mem (gradeLEn_nonempty n D)
    rw [show graden n D = 0 from h] at hmem
    exact hmem
  · intro h
    exact Nat.le_zero.mp (Nat.sInf_le h)

/-- Membership in the lattice stabilizer is exactly the lattice-preservation condition
`MapsToBW n D` (since `λ^0·D = 1·D = D`). -/
theorem mem_bwLatticeStabilizer_iff (n : ℕ) (D : BWVec n) :
    D ∈ bwLatticeStabilizer n ↔ MapsToBW n D := by
  unfold bwLatticeStabilizer gradeLEn
  rw [Set.mem_setOf_eq, pow_zero, bwSmul_one]

end BWGradeKernelClassification
