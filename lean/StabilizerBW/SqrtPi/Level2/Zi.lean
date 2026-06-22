import StabilizerBW.SqrtPi.Q8
import StabilizerBW.SqrtPi.Catalyst

/-!
# The level-2 cyclotomic ring `ℤ[i] = ℤ[ζ₄]`, the prime `λ₂ = 1 - i`, and its valuation

This file builds, from scratch, a concrete computable model of the Gaussian integers
`ℤ[i] = ℤ[ζ₄] = ℤ[x]/(x² + 1)`, represented by integer pairs `a + b·i` with `i² = -1`.

It is the *level-2* analogue of `Z8Ring.lean`.  We set up:

* the distinguished level-2 prime `λ₂ = 1 - i` and the element `1 + i`, which are associates
  (`λ₂ = (-i)·(1+i)`);
* decidable divisibility characterisations `λ₂ ∣ y ↔ ziDivLam y` (i.e. `a + b` even) and
  `2 ∣ y ↔ ziDiv2 y` (i.e. `a` and `b` both even);
* the genuine `λ₂`-adic valuation `nuLam₂ y := emultiplicity λ₂ y : ℕ∞`, with the bridges
  `1 ≤ nuLam₂ y ↔ λ₂ ∣ y` and `2 ≤ nuLam₂ y ↔ 2 ∣ y`;
* the ring embeddings `ℤ[i] ↪ ℤ[ζ₈]` and `ℤ[i] ↪ ℚ[ζ₈]` (since `ℚ(ζ₈) = ℚ(i, √2)` contains
  `ℚ(i)`), realising `ℤ[i]` concretely inside the level-3 denotation field.

The **level-raising bridge** `λ₃² ~ λ₂` (the cyclotomic-doubling engine of `Γ(g) = 2g`) is
re-exported from `Catalyst.lean` at the end.
-/

set_option maxRecDepth 4000

namespace Pi3

/-- An element `a + b·i` of `ℤ[i] = ℤ[ζ₄] = ℤ[x]/(x²+1)`. -/
@[ext] structure Zi where
  a : ℤ
  b : ℤ
deriving DecidableEq, Repr

namespace Zi

instance : Zero Zi := ⟨⟨0, 0⟩⟩
instance : One Zi := ⟨⟨1, 0⟩⟩
instance : Add Zi := ⟨fun p q => ⟨p.a + q.a, p.b + q.b⟩⟩
instance : Neg Zi := ⟨fun p => ⟨-p.a, -p.b⟩⟩
instance : Sub Zi := ⟨fun p q => ⟨p.a - q.a, p.b - q.b⟩⟩
/-- Multiplication reducing `i² = -1`. -/
instance : Mul Zi := ⟨fun p q => ⟨p.a * q.a - p.b * q.b, p.a * q.b + p.b * q.a⟩⟩

@[simp] lemma zero_a : (0 : Zi).a = 0 := rfl
@[simp] lemma zero_b : (0 : Zi).b = 0 := rfl
@[simp] lemma one_a : (1 : Zi).a = 1 := rfl
@[simp] lemma one_b : (1 : Zi).b = 0 := rfl
@[simp] lemma add_a (p q : Zi) : (p + q).a = p.a + q.a := rfl
@[simp] lemma add_b (p q : Zi) : (p + q).b = p.b + q.b := rfl
@[simp] lemma neg_a (p : Zi) : (-p).a = -p.a := rfl
@[simp] lemma neg_b (p : Zi) : (-p).b = -p.b := rfl
@[simp] lemma sub_a (p q : Zi) : (p - q).a = p.a - q.a := rfl
@[simp] lemma sub_b (p q : Zi) : (p - q).b = p.b - q.b := rfl
@[simp] lemma mul_a (p q : Zi) : (p * q).a = p.a * q.a - p.b * q.b := rfl
@[simp] lemma mul_b (p q : Zi) : (p * q).b = p.a * q.b + p.b * q.a := rfl

instance : CommRing Zi where
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

/-- `i = ζ₄`, a primitive fourth root of unity. -/
def imag : Zi := ⟨0, 1⟩
/-- The level-2 prime `λ₂ = 1 - i`. -/
def lam2 : Zi := ⟨1, -1⟩
/-- `1 + i`, an associate of `λ₂`. -/
def onePlusI : Zi := ⟨1, 1⟩

/-- `i² = -1`. -/
lemma imag_sq : imag * imag = -1 := by decide
/-- `λ₂` and `1 + i` are associates: `λ₂ = (-i)·(1+i)`. -/
lemma lam2_assoc : lam2 = (-imag) * onePlusI := by decide

/-- `λ₂` divides `y` iff the coordinate sum is even. -/
def ziDivLam (y : Zi) : Prop := (y.a + y.b) % 2 = 0
/-- `2` divides `y` iff both coordinates are even. -/
def ziDiv2 (y : Zi) : Prop := y.a % 2 = 0 ∧ y.b % 2 = 0

instance (y : Zi) : Decidable (ziDivLam y) := by unfold ziDivLam; infer_instance
instance (y : Zi) : Decidable (ziDiv2 y) := by unfold ziDiv2; infer_instance

/-- `λ₂ ∣ y` iff the coordinate sum is even. -/
lemma dvd_lam2_iff (y : Zi) : lam2 ∣ y ↔ ziDivLam y := by
  constructor
  · rintro ⟨z, rfl⟩
    simp only [ziDivLam, lam2, mul_a, mul_b]; ring_nf; omega
  · intro h
    unfold ziDivLam at h
    refine ⟨⟨(y.a - y.b) / 2, (y.a + y.b) / 2⟩, ?_⟩
    ext <;> simp only [lam2, mul_a, mul_b] <;> omega

/-- `λ₂² = -2i` so `λ₂² ∣ y ↔ 2 ∣ y ↔ both coordinates even`. -/
lemma dvd_lam2Sq_iff (y : Zi) : lam2 ^ 2 ∣ y ↔ ziDiv2 y := by
  have hsq : lam2 ^ 2 = (⟨0, -2⟩ : Zi) := by decide
  rw [hsq]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨?_, ?_⟩ <;> simp only [mul_a, mul_b] <;> omega
  · intro h
    unfold ziDiv2 at h
    refine ⟨⟨-(y.b / 2), y.a / 2⟩, ?_⟩
    ext <;> simp only [mul_a, mul_b] <;> omega

/-- `2 ∣ y ↔ both coordinates even`. -/
lemma dvd_two_iff (y : Zi) : (2 : Zi) ∣ y ↔ ziDiv2 y := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨?_, ?_⟩ <;> simp only [mul_a, mul_b] <;>
      simp only [show (2 : Zi) = ⟨2, 0⟩ from rfl] <;> omega
  · intro h
    unfold ziDiv2 at h
    refine ⟨⟨y.a / 2, y.b / 2⟩, ?_⟩
    ext <;> simp only [show (2 : Zi) = ⟨2, 0⟩ from rfl, mul_a, mul_b] <;> omega

/-- `λ₂² ∣ y ↔ 2 ∣ y`. -/
lemma dvd_lam2Sq_iff_two (y : Zi) : lam2 ^ 2 ∣ y ↔ (2 : Zi) ∣ y := by
  rw [dvd_lam2Sq_iff, dvd_two_iff]

/-! ### The genuine `λ₂`-adic valuation -/

/-- The level-2 `λ₂`-adic valuation `ν_{λ₂} : ℤ[i] → ℕ∞`, defined as `emultiplicity λ₂`. -/
noncomputable def nuLam2 (y : Zi) : ℕ∞ := emultiplicity lam2 y

/-- Bridge: `ν_{λ₂}(y) ≥ 1 ↔ λ₂ ∣ y`. -/
lemma one_le_nuLam2_iff (y : Zi) : (1 : ℕ∞) ≤ nuLam2 y ↔ lam2 ∣ y := by
  rw [nuLam2]
  constructor
  · intro h; simpa using pow_dvd_of_le_emultiplicity h
  · intro h; exact le_emultiplicity_of_pow_dvd (by simpa using h)

/-- Bridge: `ν_{λ₂}(y) ≥ 2 ↔ λ₂² ∣ y ↔ 2 ∣ y`. -/
lemma two_le_nuLam2_iff (y : Zi) : (2 : ℕ∞) ≤ nuLam2 y ↔ (2 : Zi) ∣ y := by
  rw [nuLam2, ← dvd_lam2Sq_iff_two]
  constructor
  · intro h; exact pow_dvd_of_le_emultiplicity h
  · intro h; exact le_emultiplicity_of_pow_dvd h

/-! ### Embeddings of `ℤ[i]` into the level-3 rings -/

/-- The ring embedding `ℤ[i] ↪ ℤ[ζ₈]`, sending `i = ζ₄` to `ζ₈² = ζ²`. -/
def toZ8 (z : Zi) : Z8 := ⟨z.a, 0, z.b, 0⟩

@[simp] lemma toZ8_a (z : Zi) : (toZ8 z).a = z.a := rfl
@[simp] lemma toZ8_b (z : Zi) : (toZ8 z).b = 0 := rfl
@[simp] lemma toZ8_c (z : Zi) : (toZ8 z).c = z.b := rfl
@[simp] lemma toZ8_d (z : Zi) : (toZ8 z).d = 0 := rfl

/-- `toZ8` as a ring homomorphism `ℤ[i] →+* ℤ[ζ₈]`. -/
def toZ8Hom : Zi →+* Z8 where
  toFun := toZ8
  map_one' := by ext <;> simp [toZ8]
  map_mul' := by intro x y; ext <;> simp [toZ8]
  map_zero' := by ext <;> simp [toZ8]
  map_add' := by intro x y; ext <;> simp [toZ8]

@[simp] lemma toZ8Hom_apply (z : Zi) : toZ8Hom z = toZ8 z := rfl

/-- The ring embedding `ℤ[i] ↪ ℚ[ζ₈]`, factoring through `ℤ[ζ₈]`. -/
def toQ8 (z : Zi) : Q8 := Q8.ofZ8 (toZ8 z)

/-- `toQ8` as a ring homomorphism `ℤ[i] →+* ℚ[ζ₈]`. -/
def toQ8Hom : Zi →+* Q8 := Q8.ofZ8Hom.comp toZ8Hom

@[simp] lemma toQ8Hom_apply (z : Zi) : toQ8Hom z = toQ8 z := rfl

lemma toZ8_injective : Function.Injective toZ8 := by
  intro x y h
  have ha := congrArg Z8.a h
  have hc := congrArg Z8.c h
  simp only [toZ8_a, toZ8_c] at ha hc
  ext <;> assumption

/-- `toZ8` sends the level-2 prime `λ₂ = 1 - i` to `1 - ζ₈² = 1 - i` inside `ℤ[ζ₈]`. -/
@[simp] lemma toZ8_lam2 : toZ8 lam2 = (1 - Z8.imag) := by decide

/-! ### The level-raising bridge `λ₃² ~ λ₂`

The cyclotomic-doubling engine connecting level 3 and level 2: the square of the level-3 prime
`λ₃ = 1 - ζ₈` is an associate of the (image of the) level-2 prime `λ₂ = 1 - i`. -/

/-- **Level-raising (re-export).** `λ₃² ~ λ₂`: the square of the level-3 prime is an associate of
the level-2 prime `λ₂ = 1 - i` (under the embedding `ℤ[i] ↪ ℤ[ζ₈]`). -/
theorem levelRaising_bridge :
    ∃ u : Z8, IsUnit u ∧ Z8.lam ^ 2 = u * (toZ8 lam2) := by
  obtain ⟨u, hu, huEq⟩ := Catalyst.levelRaising
  have himag : IsUnit (Z8.imag) :=
    IsUnit.of_mul_eq_one (a := Z8.imag) (⟨0, 0, -1, 0⟩ : Z8) (by decide)
  refine ⟨u * Z8.imag, hu.mul himag, ?_⟩
  rw [huEq, mul_assoc]; congr 1

/-- Consequently `λ₂ ∣ x ↔ λ₃² ∣ x` inside `ℤ[ζ₈]`: divisibility by the level-2 prime is
divisibility by the *square* of the level-3 prime. -/
theorem dvd_levelTwo_iff (x : Z8) : (toZ8 lam2) ∣ x ↔ Z8.lam ^ 2 ∣ x := by
  rw [toZ8_lam2]; exact Catalyst.dvd_levelTwo_iff x

end Zi

end Pi3
