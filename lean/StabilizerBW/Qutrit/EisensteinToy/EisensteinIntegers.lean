import Mathlib

/-!
# The Eisenstein integers `ℤ[ω]` and the `λ₃`-adic valuation

This file builds a concrete, computable model of the ring of Eisenstein integers

  `ℤ[ω] = ℤ[x]/(x² + x + 1)`,

written `a + b·ω` with `ω = ζ₃` a primitive cube root of unity, so that `ω² = -1 - ω`.
We give it a `CommRing` structure, the norm `N(a + bω) = a² - ab + b²`, the ramified prime
`λ₃ = 1 - ω`, prove the ring is a domain (the norm form is anisotropic over `ℤ`), and develop
the `λ₃`-adic valuation `ν_λ = emultiplicity λ₃` together with the divisibility ↔ valuation
bridge that the qutrit Möbius machinery needs.

## A correction to the DISPATCH ramification identity

The DISPATCH (and `refs/literature.md`) states the ramification identity as
`λ₃² = -3·u with u = 1 + 2ω a unit`.  This is **mathematically incorrect**: the element
`1 + 2ω` has norm `N(1 + 2ω) = 1 - 2 + 4 = 3`, so it is **not a unit** — it is in fact a square
root of `-3` (one checks `(1 + 2ω)² = -3`), and is an *associate* of `λ₃` itself
(`1 + 2ω = ω·λ₃`).  The correct ramification identity is

  `λ₃² = -3·ω`,  with `ω` (not `1 + 2ω`) the unit.

Both the correct identity (`Eis.lam_sq`) and the refutation of the DISPATCH's claim
(`Eis.sqrtNeg3_lam_sq_ne`, `Eis.one_add_two_omega_not_unit`) are proved below; this is
exactly the "test, then prove or refute" discipline the structural strawman asks for.

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace QutritEis

/-- An Eisenstein integer `a + b·ω` with `a, b : ℤ` and `ω = ζ₃` (so `ω² = -1 - ω`). -/
structure Eis where
  re : ℤ   -- coefficient of `1`
  im : ℤ   -- coefficient of `ω`
deriving DecidableEq, Repr

namespace Eis

@[ext] theorem ext' {x y : Eis} (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x; cases y; simp_all

instance : Zero Eis := ⟨⟨0, 0⟩⟩
instance : One Eis := ⟨⟨1, 0⟩⟩
instance : Add Eis := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg Eis := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub Eis := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
/-- Multiplication: `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd)ω`, since `ω² = -1 - ω`. -/
instance : Mul Eis := ⟨fun x y =>
  ⟨x.re * y.re - x.im * y.im,
   x.re * y.im + x.im * y.re - x.im * y.im⟩⟩

@[simp] theorem zero_re : (0 : Eis).re = 0 := rfl
@[simp] theorem zero_im : (0 : Eis).im = 0 := rfl
@[simp] theorem one_re : (1 : Eis).re = 1 := rfl
@[simp] theorem one_im : (1 : Eis).im = 0 := rfl
@[simp] theorem add_re (x y : Eis) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : Eis) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : Eis) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Eis) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : Eis) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : Eis) : (x - y).im = x.im - y.im := rfl
@[simp] theorem mul_re (x y : Eis) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : Eis) :
    (x * y).im = x.re * y.im + x.im * y.re - x.im * y.im := rfl

instance commRing : CommRing Eis where
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

/-- `ω = ζ₃`, a primitive cube root of unity. -/
def omega : Eis := ⟨0, 1⟩
/-- `λ₃ = 1 - ω`, the ramified prime above `3`. -/
def lam : Eis := ⟨1, -1⟩
/-- `√(-3) = 1 + 2ω` (the DISPATCH's purported "unit", which is in fact an associate of `λ₃`). -/
def sqrtNeg3 : Eis := ⟨1, 2⟩

@[simp] theorem omega_def : omega = ⟨0, 1⟩ := rfl
@[simp] theorem lam_def : lam = ⟨1, -1⟩ := rfl
@[simp] theorem sqrtNeg3_def : sqrtNeg3 = ⟨1, 2⟩ := rfl

theorem omega_sq : omega ^ 2 = -1 - omega := by decide
theorem omega_pow_three : omega ^ 3 = 1 := by decide
theorem lam_eq : lam = 1 - omega := by decide

/-- `ω` is a unit, with inverse `ω² = -1 - ω`. -/
theorem omega_mul_omegaSq : omega * (omega ^ 2) = 1 := by decide

theorem isUnit_omega : IsUnit omega :=
  ⟨⟨omega, omega ^ 2, omega_mul_omegaSq, by rw [mul_comm]; exact omega_mul_omegaSq⟩, rfl⟩

/-! ## The norm and the ring being a domain -/

/-- The field norm `N(a + bω) = a² - ab + b²` (the product of the two Galois conjugates). -/
def norm (x : Eis) : ℤ := x.re ^ 2 - x.re * x.im + x.im ^ 2

@[simp] theorem norm_zero : norm 0 = 0 := by decide
@[simp] theorem norm_one : norm 1 = 1 := by decide
theorem norm_lam : norm lam = 3 := by decide
theorem norm_omega : norm omega = 1 := by decide
theorem norm_sqrtNeg3 : norm sqrtNeg3 = 3 := by decide

theorem norm_mul (x y : Eis) : norm (x * y) = norm x * norm y := by
  simp only [norm, mul_re, mul_im]; ring

theorem norm_nonneg (x : Eis) : 0 ≤ norm x := by
  unfold norm; nlinarith [sq_nonneg (2 * x.re - x.im), sq_nonneg x.im]

/-- The norm form `a² - ab + b²` is anisotropic over `ℤ`: it vanishes only at the origin. -/
theorem norm_eq_zero {x : Eis} (h : norm x = 0) : x = 0 := by
  have hsq1 : (2 * x.re - x.im) ^ 2 = 0 := by
    unfold norm at h; nlinarith [sq_nonneg (2 * x.re - x.im), sq_nonneg x.im]
  have hsq2 : x.im ^ 2 = 0 := by
    unfold norm at h; nlinarith [sq_nonneg (2 * x.re - x.im), sq_nonneg x.im]
  have him : x.im = 0 := pow_eq_zero_iff (by norm_num) |>.mp hsq2
  have hlin : 2 * x.re - x.im = 0 := pow_eq_zero_iff (by norm_num) |>.mp hsq1
  have hre : x.re = 0 := by omega
  exact Eis.ext' hre him

instance : Nontrivial Eis := ⟨0, 1, by decide⟩

instance instNoZeroDivisors : NoZeroDivisors Eis where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    have hn : norm x * norm y = 0 := by rw [← norm_mul, h, norm_zero]
    rcases mul_eq_zero.mp hn with hx | hy
    · exact Or.inl (norm_eq_zero hx)
    · exact Or.inr (norm_eq_zero hy)

instance instIsDomain : IsDomain Eis := NoZeroDivisors.to_isDomain Eis

theorem lam_ne_zero : lam ≠ 0 := by decide
theorem lam_pow_ne_zero (j : ℕ) : lam ^ j ≠ 0 := pow_ne_zero j lam_ne_zero

/-! ## The ramification identity (and the refutation of the DISPATCH's unit claim) -/

/-- **Correct ramification identity:** `λ₃² = -3·ω`, with `ω` the unit. -/
theorem lam_sq : lam ^ 2 = -3 * omega := by decide

/-- `λ₃² = -3·v` for a *unit* `v` — exhibiting the genuine ramification `(λ₃)² ∼ (3)`. -/
theorem lam_sq_assoc : ∃ v : Eis, IsUnit v ∧ lam ^ 2 = -3 * v :=
  ⟨omega, isUnit_omega, lam_sq⟩

/-- `(1 + 2ω)² = -3`, so `1 + 2ω = √(-3)`. -/
theorem sqrtNeg3_sq : sqrtNeg3 ^ 2 = -3 := by decide

/-- `1 + 2ω = ω·λ₃`: the DISPATCH's `u = 1 + 2ω` is an *associate of the prime* `λ₃`, not a unit. -/
theorem sqrtNeg3_eq_omega_mul_lam : sqrtNeg3 = omega * lam := by decide

/-- **Refutation (part 1):** `1 + 2ω` is NOT a unit (its norm is `3 ≠ ±1`). -/
theorem one_add_two_omega_not_unit : ¬ IsUnit sqrtNeg3 := by
  intro h
  -- a unit has norm ±1, but `norm sqrtNeg3 = 3`
  obtain ⟨u, hu⟩ := h
  have hinv : norm sqrtNeg3 * norm (↑u⁻¹) = 1 := by
    rw [← norm_mul]
    have : sqrtNeg3 * (↑u⁻¹ : Eis) = 1 := by
      rw [← hu]; exact u.mul_inv
    rw [this, norm_one]
  rw [norm_sqrtNeg3] at hinv
  -- 3 * k = 1 has no integer solution
  omega

/-- **Refutation (part 2):** the literal DISPATCH identity `λ₃² = -3·(1 + 2ω)` is FALSE. -/
theorem sqrtNeg3_lam_sq_ne : lam ^ 2 ≠ -3 * sqrtNeg3 := by decide

/-! ## The `λ₃`-adic valuation and the divisibility ↔ valuation bridge -/

open scoped Classical

/-- The `λ₃`-adic valuation `ν_λ = emultiplicity λ₃`, valued in `ℕ∞`. -/
noncomputable def valLam (y : Eis) : ℕ∞ := emultiplicity lam y

/-- **The divisibility ↔ valuation bridge.** For the ramified prime `λ₃`,
`λ₃^a ∣ λ₃^j · y ↔ (a : ℕ∞) ≤ j + ν_λ(y)`. -/
theorem lam_pow_dvd_lam_pow_mul_iff (a j : ℕ) (y : Eis) :
    lam ^ a ∣ lam ^ j * y ↔ (a : ℕ∞) ≤ j + valLam y := by
  unfold valLam
  rcases Nat.lt_or_ge a j with haj | haj
  · constructor
    · intro _
      calc (a : ℕ∞) ≤ (j : ℕ∞) := by exact_mod_cast (le_of_lt haj)
        _ ≤ j + emultiplicity lam y := le_self_add
    · intro _
      exact Dvd.dvd.mul_right (pow_dvd_pow lam (le_of_lt haj)) y
  · have hcancel : lam ^ a ∣ lam ^ j * y ↔ lam ^ (a - j) ∣ y := by
      have h1 : lam ^ a = lam ^ j * lam ^ (a - j) := by
        rw [← pow_add]; congr 1; omega
      rw [h1, mul_dvd_mul_iff_left (lam_pow_ne_zero j)]
    rw [hcancel, pow_dvd_iff_le_emultiplicity]
    constructor
    · intro h
      have hle : (a : ℕ∞) ≤ (j : ℕ∞) + ((a - j : ℕ) : ℕ∞) := by
        have hh : a ≤ j + (a - j) := by omega
        calc (a : ℕ∞) ≤ ((j + (a - j) : ℕ) : ℕ∞) := by exact_mod_cast hh
          _ = (j : ℕ∞) + ((a - j : ℕ) : ℕ∞) := by push_cast; rfl
      calc (a : ℕ∞) ≤ (j : ℕ∞) + ((a - j : ℕ) : ℕ∞) := hle
        _ ≤ j + emultiplicity lam y := by gcongr
    · intro h
      have hcast : (a : ℕ∞) = (j : ℕ∞) + ((a - j : ℕ) : ℕ∞) := by
        have hh : a = j + (a - j) := by omega
        calc (a : ℕ∞) = ((j + (a - j) : ℕ) : ℕ∞) := by exact_mod_cast hh
          _ = (j : ℕ∞) + ((a - j : ℕ) : ℕ∞) := by push_cast; rfl
      rw [hcast] at h
      exact WithTop.le_of_add_le_add_left (ENat.coe_ne_top j) h

/-! ## The residue field `ℤ[ω]/(λ₃) ≃ 𝔽₃`

Since `λ₃ = 1 - ω`, we have `ω ≡ 1 (mod λ₃)`, so the reduction map sends `a + bω ↦ a + b`
into `ℤ/3`.  We package the reduction as a ring homomorphism `ℤ[ω] → ZMod 3` and record that
it is surjective and kills `λ₃` (the characteristic-3 analogue of the qubit characteristic-2
residue field). -/

/-- Reduction `ℤ[ω] → 𝔽₃`, `a + bω ↦ a + b (mod 3)` (using `ω ≡ 1`). -/
def toF3 : Eis →+* ZMod 3 where
  toFun x := (x.re : ZMod 3) + (x.im : ZMod 3)
  map_one' := by simp
  map_mul' x y := by
    show (((x * y).re : ZMod 3) + ((x * y).im : ZMod 3))
        = (((x.re : ZMod 3) + (x.im : ZMod 3)) * ((y.re : ZMod 3) + (y.im : ZMod 3)))
    simp only [mul_re, mul_im]
    push_cast
    have h3 : (3 : ZMod 3) = 0 := by decide
    linear_combination (-(x.im : ZMod 3) * (y.im : ZMod 3)) * h3
  map_zero' := by simp
  map_add' x y := by simp only [add_re, add_im]; push_cast; ring

theorem toF3_lam : toF3 lam = 0 := by decide

theorem toF3_surjective : Function.Surjective toF3 := by
  intro y
  refine ⟨⟨y.val, 0⟩, ?_⟩
  simp only [toF3, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  push_cast
  simp [ZMod.natCast_val, ZMod.cast_id]

end Eis
end QutritEis
