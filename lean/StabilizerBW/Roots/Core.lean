import Mathlib

/-!
# The arithmetic of square roots: the ring R = ℤ[ζ₈]

This file builds a concrete, computable model of the ring of integers

 `R = ℤ[ζ₈] = ℤ[x]/(x⁴+1)`,

written `a + b·ζ + c·ζ² + d·ζ³` with `ζ = ζ₈` a primitive 8th root of unity, so that
`ζ⁴ = -1`. We give `R` a `CommRing` structure, define complex conjugation, the
relevant elements (`ζ`, `i = ζ²`, `λ = 1-ζ`, `1+i`, `√2`, the fundamental unit
`u = 1-ζ+ζ³`), and characterise divisibility by `1+i` by an explicit decidable
parity criterion which is proved equivalent to honest ring divisibility.

These are the level-3 Barnes–Wall conventions of the accompanying research note:
`λ = 1-ζ₈`, `(2) = (λ)⁴`, `(1+i) = (λ)²·unit`.
-/

namespace Roots

/-- An element of `R = ℤ[ζ₈] = ℤ[x]/(x⁴+1)`, written `a + b·ζ + c·ζ² + d·ζ³`. -/
structure Z8 where
 a : ℤ
 b : ℤ
 c : ℤ
 d : ℤ
deriving DecidableEq, Repr

namespace Z8

@[ext] theorem ext' {x y : Z8} (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c)
 (hd : x.d = y.d) : x = y := by
 cases x; cases y; simp_all

instance : Zero Z8 := ⟨⟨0,0,0,0⟩⟩
instance : One Z8 := ⟨⟨1,0,0,0⟩⟩
instance : Add Z8 := ⟨fun x y => ⟨x.a+y.a, x.b+y.b, x.c+y.c, x.d+y.d⟩⟩
instance : Neg Z8 := ⟨fun x => ⟨-x.a, -x.b, -x.c, -x.d⟩⟩
instance : Sub Z8 := ⟨fun x y => ⟨x.a-y.a, x.b-y.b, x.c-y.c, x.d-y.d⟩⟩
/-- Multiplication modulo `x⁴ + 1` (so `ζ⁴ = -1`). -/
instance : Mul Z8 := ⟨fun x y =>
 ⟨x.a*y.a - (x.b*y.d + x.c*y.c + x.d*y.b),
 x.a*y.b + x.b*y.a - (x.c*y.d + x.d*y.c),
 x.a*y.c + x.b*y.b + x.c*y.a - x.d*y.d,
 x.a*y.d + x.b*y.c + x.c*y.b + x.d*y.a⟩⟩

@[simp] theorem zero_a : (0:Z8).a = 0 := rfl
@[simp] theorem zero_b : (0:Z8).b = 0 := rfl
@[simp] theorem zero_c : (0:Z8).c = 0 := rfl
@[simp] theorem zero_d : (0:Z8).d = 0 := rfl
@[simp] theorem one_a : (1:Z8).a = 1 := rfl
@[simp] theorem one_b : (1:Z8).b = 0 := rfl
@[simp] theorem one_c : (1:Z8).c = 0 := rfl
@[simp] theorem one_d : (1:Z8).d = 0 := rfl
@[simp] theorem add_a (x y:Z8) : (x+y).a = x.a+y.a := rfl
@[simp] theorem add_b (x y:Z8) : (x+y).b = x.b+y.b := rfl
@[simp] theorem add_c (x y:Z8) : (x+y).c = x.c+y.c := rfl
@[simp] theorem add_d (x y:Z8) : (x+y).d = x.d+y.d := rfl
@[simp] theorem neg_a (x:Z8) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x:Z8) : (-x).b = -x.b := rfl
@[simp] theorem neg_c (x:Z8) : (-x).c = -x.c := rfl
@[simp] theorem neg_d (x:Z8) : (-x).d = -x.d := rfl
@[simp] theorem sub_a (x y:Z8) : (x-y).a = x.a-y.a := rfl
@[simp] theorem sub_b (x y:Z8) : (x-y).b = x.b-y.b := rfl
@[simp] theorem sub_c (x y:Z8) : (x-y).c = x.c-y.c := rfl
@[simp] theorem sub_d (x y:Z8) : (x-y).d = x.d-y.d := rfl
@[simp] theorem mul_a (x y:Z8) :
 (x*y).a = x.a*y.a - (x.b*y.d + x.c*y.c + x.d*y.b) := rfl
@[simp] theorem mul_b (x y:Z8) :
 (x*y).b = x.a*y.b + x.b*y.a - (x.c*y.d + x.d*y.c) := rfl
@[simp] theorem mul_c (x y:Z8) :
 (x*y).c = x.a*y.c + x.b*y.b + x.c*y.a - x.d*y.d := rfl
@[simp] theorem mul_d (x y:Z8) :
 (x*y).d = x.a*y.d + x.b*y.c + x.c*y.b + x.d*y.a := rfl

instance commRing : CommRing Z8 where
 add_assoc := by intros; ext <;> simp <;> ring
 zero_add := by intros; ext <;> simp
 add_zero := by intros; ext <;> simp
 add_comm := by intros; ext <;> simp <;> ring
 neg_add_cancel := by intros; ext <;> simp
 mul_assoc := by intros; ext <;> simp <;> ring
 one_mul := by intros; ext <;> simp
 mul_one := by intros; ext <;> simp
 left_distrib := by intros; ext <;> simp <;> ring
 right_distrib := by intros; ext <;> simp <;> ring
 mul_comm := by intros; ext <;> simp <;> ring
 sub_eq_add_neg := by intros; ext <;> simp <;> ring
 zero_mul := by intros; ext <;> simp
 mul_zero := by intros; ext <;> simp
 nsmul := nsmulRec
 zsmul := zsmulRec

/-! ## Named elements -/

/-- `ζ = ζ₈`, a primitive 8th root of unity. -/
def zeta : Z8 := ⟨0,1,0,0⟩
/-- `i = ζ²`. -/
def iu : Z8 := ⟨0,0,1,0⟩
/-- `λ = 1 - ζ`, the ramified prime. -/
def lam : Z8 := ⟨1,-1,0,0⟩
/-- `1 + i = 1 + ζ²`. -/
def oneI : Z8 := ⟨1,0,1,0⟩
/-- `√2 = ζ + ζ⁻¹ = ζ - ζ³`. -/
def sqrt2 : Z8 := ⟨0,1,0,-1⟩
/-- The fundamental unit `u = 1 - ζ + ζ³ = 1 - √2`. -/
def uu : Z8 := ⟨1,-1,0,1⟩
/-- Its inverse `u⁻¹ = -1 - √2 = -1 - ζ + ζ³`. -/
def uuInv : Z8 := ⟨-1,-1,0,1⟩

@[simp] theorem zeta_def : zeta = ⟨0,1,0,0⟩ := rfl
@[simp] theorem iu_def : iu = ⟨0,0,1,0⟩ := rfl
@[simp] theorem lam_def : lam = ⟨1,-1,0,0⟩ := rfl
@[simp] theorem oneI_def : oneI = ⟨1,0,1,0⟩ := rfl
@[simp] theorem sqrt2_def : sqrt2 = ⟨0,1,0,-1⟩ := rfl
@[simp] theorem uu_def : uu = ⟨1,-1,0,1⟩ := rfl
@[simp] theorem uuInv_def : uuInv = ⟨-1,-1,0,1⟩ := rfl

theorem zeta_pow_four : zeta^4 = -1 := by decide
theorem iu_eq_zeta_sq : iu = zeta^2 := by decide
theorem iu_sq : iu^2 = -1 := by decide
theorem oneI_eq : oneI = 1 + iu := by decide
theorem lam_eq : lam = 1 - zeta := by decide
theorem sqrt2_sq : sqrt2^2 = 2 := by decide

/-- `√2 = -(ζ³ - ζ) = ζ - ζ³`. -/
theorem sqrt2_eq : sqrt2 = zeta - zeta^3 := by decide

/-- `ζ·√2 = 1 + i`: this is `ζ₈ = (1+i)/√2`. -/
theorem zeta_mul_sqrt2 : zeta * sqrt2 = oneI := by decide

/-! ## Priority 1.3 — the ramified square: `(1-ζ)² = (1+i)·u`, and `u` is a unit. -/

/-- `(1-ζ)² = (1+i)·u` with `u = 1-ζ+ζ³`. This is the level-3 ramification identity. -/
theorem lam_sq : lam^2 = oneI * uu := by decide

/-- The fundamental unit `u` is invertible, with inverse `-1-√2`. -/
theorem uu_mul_uuInv : uu * uuInv = 1 := by decide

theorem isUnit_uu : IsUnit uu := ⟨⟨uu, uuInv, uu_mul_uuInv, by rw [mul_comm]; exact uu_mul_uuInv⟩, rfl⟩

/-- Restatement: `λ² = (1+i)·u` with `u` a unit, exhibiting `(1+i) ∼ λ²`. -/
theorem lam_sq_assoc : ∃ v : Z8, IsUnit v ∧ lam^2 = oneI * v :=
 ⟨uu, isUnit_uu, lam_sq⟩

/-! ## Complex conjugation -/

/-- Complex conjugation `ζ ↦ ζ⁻¹ = -ζ³`, an involution and ring homomorphism. -/
def conj (z : Z8) : Z8 := ⟨z.a, -z.d, -z.c, -z.b⟩

@[simp] theorem conj_a (z:Z8) : (conj z).a = z.a := rfl
@[simp] theorem conj_b (z:Z8) : (conj z).b = -z.d := rfl
@[simp] theorem conj_c (z:Z8) : (conj z).c = -z.c := rfl
@[simp] theorem conj_d (z:Z8) : (conj z).d = -z.b := rfl

@[simp] theorem conj_conj (z : Z8) : conj (conj z) = z := by
 cases z; simp [conj]

theorem conj_zeta : conj zeta = -zeta^3 := by decide

theorem conj_add (x y : Z8) : conj (x+y) = conj x + conj y := by
 ext <;> simp [conj] <;> ring

theorem conj_mul (x y : Z8) : conj (x*y) = conj x * conj y := by
 ext <;> simp [conj] <;> ring

@[simp] theorem conj_one : conj 1 = 1 := by decide
@[simp] theorem conj_zero : conj 0 = 0 := by decide

/-! ## Divisibility by `1+i`: decidable parity criterion. -/

/-- Decidable parity criterion for divisibility by `1+i`. -/
def dvdOneI (z : Z8) : Prop := (2 ∣ (z.a + z.c)) ∧ (2 ∣ (z.b + z.d))

instance (z : Z8) : Decidable (dvdOneI z) := by
 unfold dvdOneI; infer_instance

/-- `half z` divides every coordinate of `z` by 2 (exact iff the coordinates are even). -/
def half (z : Z8) : Z8 := ⟨z.a/2, z.b/2, z.c/2, z.d/2⟩

end Z8
end Roots
