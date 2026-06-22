import Mathlib

/-!
# The cyclotomic ring `ℤ[ζ₈]`, the prime `λ = 1 - ζ₈`, and the `λ`-adic valuation

This file builds, from scratch, a concrete computable model of the ring of integers
`ℤ[ζ₈] = ℤ[x]/(x⁴ + 1)` of the eighth cyclotomic field, represented by integer
4-tuples `a + b·ζ + c·ζ² + d·ζ³` with `ζ⁴ = -1`.

It then sets up:

* the distinguished prime `λ = 1 - ζ₈` and the element `1 + i = 1 + ζ²` (with `i = ζ²`),
  which are associates since `λ² = u · (1 + i)` for an explicit unit `u = 1 - √2`;
* decidable divisibility characterisations
  `λ ∣ y ↔ divLam y` and `(1+i) ∣ y ↔ divLam2 y` in terms of parities of the coordinates;
* the genuine `λ`-adic valuation `nuLam y := emultiplicity λ y : ℕ∞`, with the bridges
  `1 ≤ nuLam y ↔ divLam y` and `2 ≤ nuLam y ↔ divLam2 y`.

These are the arithmetic foundations of the graded `√Π` infrastructure.
-/

set_option maxRecDepth 4000

namespace Pi3

/-- An element `a + b·ζ + c·ζ² + d·ζ³` of `ℤ[ζ₈] = ℤ[x]/(x⁴+1)`, with `ζ = ζ₈`. -/
@[ext] structure Z8 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq, Repr

namespace Z8

instance : Zero Z8 := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Z8 := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add Z8 := ⟨fun p q => ⟨p.a + q.a, p.b + q.b, p.c + q.c, p.d + q.d⟩⟩
instance : Neg Z8 := ⟨fun p => ⟨-p.a, -p.b, -p.c, -p.d⟩⟩
instance : Sub Z8 := ⟨fun p q => ⟨p.a - q.a, p.b - q.b, p.c - q.c, p.d - q.d⟩⟩
/-- Multiplication reducing `ζ⁴ = -1` (so `ζ⁵ = -ζ`, `ζ⁶ = -ζ²`). -/
instance : Mul Z8 := ⟨fun p q =>
  ⟨p.a * q.a - (p.b * q.d + p.c * q.c + p.d * q.b),
   (p.a * q.b + p.b * q.a) - (p.c * q.d + p.d * q.c),
   (p.a * q.c + p.b * q.b + p.c * q.a) - p.d * q.d,
   p.a * q.d + p.b * q.c + p.c * q.b + p.d * q.a⟩⟩

@[simp] lemma zero_a : (0 : Z8).a = 0 := rfl
@[simp] lemma zero_b : (0 : Z8).b = 0 := rfl
@[simp] lemma zero_c : (0 : Z8).c = 0 := rfl
@[simp] lemma zero_d : (0 : Z8).d = 0 := rfl
@[simp] lemma one_a : (1 : Z8).a = 1 := rfl
@[simp] lemma one_b : (1 : Z8).b = 0 := rfl
@[simp] lemma one_c : (1 : Z8).c = 0 := rfl
@[simp] lemma one_d : (1 : Z8).d = 0 := rfl
@[simp] lemma add_a (p q : Z8) : (p + q).a = p.a + q.a := rfl
@[simp] lemma add_b (p q : Z8) : (p + q).b = p.b + q.b := rfl
@[simp] lemma add_c (p q : Z8) : (p + q).c = p.c + q.c := rfl
@[simp] lemma add_d (p q : Z8) : (p + q).d = p.d + q.d := rfl
@[simp] lemma neg_a (p : Z8) : (-p).a = -p.a := rfl
@[simp] lemma neg_b (p : Z8) : (-p).b = -p.b := rfl
@[simp] lemma neg_c (p : Z8) : (-p).c = -p.c := rfl
@[simp] lemma neg_d (p : Z8) : (-p).d = -p.d := rfl
@[simp] lemma sub_a (p q : Z8) : (p - q).a = p.a - q.a := rfl
@[simp] lemma sub_b (p q : Z8) : (p - q).b = p.b - q.b := rfl
@[simp] lemma sub_c (p q : Z8) : (p - q).c = p.c - q.c := rfl
@[simp] lemma sub_d (p q : Z8) : (p - q).d = p.d - q.d := rfl
@[simp] lemma mul_a (p q : Z8) :
    (p * q).a = p.a * q.a - (p.b * q.d + p.c * q.c + p.d * q.b) := rfl
@[simp] lemma mul_b (p q : Z8) :
    (p * q).b = (p.a * q.b + p.b * q.a) - (p.c * q.d + p.d * q.c) := rfl
@[simp] lemma mul_c (p q : Z8) :
    (p * q).c = (p.a * q.c + p.b * q.b + p.c * q.a) - p.d * q.d := rfl
@[simp] lemma mul_d (p q : Z8) :
    (p * q).d = p.a * q.d + p.b * q.c + p.c * q.b + p.d * q.a := rfl

instance : CommRing Z8 where
  add_assoc := by intro a b c; ext <;> simp <;> ring
  zero_add := by intro a; ext <;> simp
  add_zero := by intro a; ext <;> simp
  add_comm := by intro a b; ext <;> simp <;> ring
  left_distrib := by intro a b c; ext <;> simp <;> ring
  right_distrib := by intro a b c; ext <;> simp <;> ring
  zero_mul := by intro a; ext <;> simp
  mul_zero := by intro a; ext <;> simp
  mul_assoc := by intro a b c; ext <;> simp <;> ring
  one_mul := by intro a; ext <;> simp
  mul_one := by intro a; ext <;> simp
  mul_comm := by intro a b; ext <;> simp <;> ring
  neg_add_cancel := by intro a; ext <;> simp
  sub_eq_add_neg := by intro a b; ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- `ζ₈`, a primitive eighth root of unity. -/
def zeta : Z8 := ⟨0, 1, 0, 0⟩
/-- `i = ζ₈² = ζ²`. -/
def imag : Z8 := ⟨0, 0, 1, 0⟩
/-- The distinguished prime `λ = 1 - ζ₈`. -/
def lam : Z8 := ⟨1, -1, 0, 0⟩
/-- `1 + i = 1 + ζ²`; an associate of `λ²`. -/
def onePlusI : Z8 := ⟨1, 0, 1, 0⟩
/-- The unit `u = 1 - √2` with `λ² = u · (1 + i)`. -/
def uu : Z8 := ⟨1, -1, 0, 1⟩
/-- The inverse `u⁻¹ = -(1 + √2)` of `uu`. -/
def uuInv : Z8 := ⟨-1, -1, 0, 1⟩

/-- `λ` divides `y` iff the coordinate sum of `y` is even. -/
def divLam (y : Z8) : Prop := (y.a + y.b + y.c + y.d) % 2 = 0
/-- `1 + i` divides `y` iff both `a + c` and `b + d` are even. -/
def divLam2 (y : Z8) : Prop := (y.a + y.c) % 2 = 0 ∧ (y.b + y.d) % 2 = 0

instance (y : Z8) : Decidable (divLam y) := by unfold divLam; infer_instance
instance (y : Z8) : Decidable (divLam2 y) := by unfold divLam2; infer_instance

/-- `ζ₈⁴ = -1`. -/
lemma zeta_pow_four : zeta * zeta * (zeta * zeta) = -1 := by decide
/-- `i² = -1`. -/
lemma imag_sq : imag * imag = -1 := by decide
/-- The level-raising identity: `λ² = u · (1 + i)` with `u` a unit. -/
lemma lamsq_eq : lam * lam = uu * onePlusI := by decide
/-- `uu` is a unit. -/
lemma uu_unit : uu * uuInv = 1 := by decide

/-- `λ ∣ y` iff the coordinate sum is even. -/
lemma dvd_lam_iff (y : Z8) : lam ∣ y ↔ divLam y := by
  constructor
  · rintro ⟨z, rfl⟩
    simp only [divLam, lam, mul_a, mul_b, mul_c, mul_d]; ring_nf; omega
  · intro h
    unfold divLam at h
    refine ⟨⟨y.a - (y.a + y.b + y.c + y.d) / 2, y.a + y.b - (y.a + y.b + y.c + y.d) / 2,
            y.a + y.b + y.c - (y.a + y.b + y.c + y.d) / 2, (y.a + y.b + y.c + y.d) / 2⟩, ?_⟩
    ext <;> simp only [lam, mul_a, mul_b, mul_c, mul_d] <;> omega

/-- `(1+i) ∣ y` iff both `a + c` and `b + d` are even. -/
lemma dvd_onePlusI_iff (y : Z8) : onePlusI ∣ y ↔ divLam2 y := by
  constructor
  · rintro ⟨z, rfl⟩
    simp only [divLam2, onePlusI, mul_a, mul_b, mul_c, mul_d]
    refine ⟨by ring_nf; omega, by ring_nf; omega⟩
  · intro h
    unfold divLam2 at h
    refine ⟨⟨(y.a + y.c) / 2, (y.b + y.d) / 2, (y.a + y.c) / 2 - y.a, (y.b + y.d) / 2 - y.b⟩, ?_⟩
    ext <;> simp only [onePlusI, mul_a, mul_b, mul_c, mul_d] <;> omega

/-- `λ² ∣ y ↔ divLam2 y` (since `λ²` and `1 + i` are associates). -/
lemma dvd_lamSq_iff (y : Z8) : lam ^ 2 ∣ y ↔ divLam2 y := by
  rw [← dvd_onePlusI_iff]
  have honei : onePlusI = uuInv * lam ^ 2 := by
    rw [pow_two, lamsq_eq, ← mul_assoc, mul_comm uuInv uu, uu_unit, one_mul]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨uu * t, by rw [pow_two, lamsq_eq]; ring⟩
  · rintro ⟨t, rfl⟩; exact ⟨uuInv * t, by rw [honei]; ring⟩

/-- `divLam2 y → divLam y`. -/
lemma divLam_of_divLam2 (y : Z8) (h : divLam2 y) : divLam y := by
  simp only [divLam2] at h; unfold divLam; omega

/-- The clean parity step: `(λ·y)` is `divLam2` iff `y` is `divLam`. -/
lemma divLam2_lam_mul (y : Z8) : divLam2 (lam * y) ↔ divLam y := by
  simp only [divLam2, lam, mul_a, mul_b, mul_c, mul_d]; unfold divLam; omega

/-- `λ²·y` is always `divLam2`. -/
lemma divLam2_lamSq_mul (y : Z8) : divLam2 (lam ^ 2 * y) := by
  rw [← dvd_lamSq_iff]; exact dvd_mul_right _ _

/-! ### The genuine `λ`-adic valuation -/

/-- The `λ`-adic valuation `ν_λ : ℤ[ζ₈] → ℕ∞`, defined as `emultiplicity λ`. -/
noncomputable def nuLam (y : Z8) : ℕ∞ := emultiplicity lam y

/-- Bridge: `ν_λ(y) ≥ 1 ↔ λ ∣ y ↔ divLam y`. -/
lemma one_le_nuLam_iff (y : Z8) : (1 : ℕ∞) ≤ nuLam y ↔ divLam y := by
  rw [nuLam, ← dvd_lam_iff]
  constructor
  · intro h; simpa using pow_dvd_of_le_emultiplicity h
  · intro h; exact le_emultiplicity_of_pow_dvd (by simpa using h)

/-- Bridge: `ν_λ(y) ≥ 2 ↔ λ² ∣ y ↔ divLam2 y`. -/
lemma two_le_nuLam_iff (y : Z8) : (2 : ℕ∞) ≤ nuLam y ↔ divLam2 y := by
  rw [nuLam, ← dvd_lamSq_iff]
  constructor
  · intro h; exact pow_dvd_of_le_emultiplicity h
  · intro h; exact le_emultiplicity_of_pow_dvd h

end Z8

end Pi3
