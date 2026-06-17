import StabilizerBW.Roots.Core
import StabilizerBW.Roots.Z8Valuation
import Mathlib

/-!
# T1A — per-coefficient arithmetic facts in `R = ℤ[ζ₈]`

This file packages the single-variable (`d = 1`) arithmetic underlying the
pure-linear Barnes–Wall grade enumerator.

For `c ∈ ℤ/8` the "phase" `ζ₈^c` is `zpow8 c`, a monoid-hom from `(ℤ/8, +)` to
`(R, ·)`. The key arithmetic fact is the **per-coefficient `λ`-factorisation**:
for `c ≠ 0`,
```
 ζ₈^c − 1 = λ^(ecoef c) · (unit) , ecoef c = ν_λ(ζ₈^c − 1),
```
where `ecoef c = 1` if `c` is odd, `2` if `c ≡ 2 (mod 4)`, `4` if `c ≡ 4 (mod 8)`.
This is the `d = 1` row of the per-monomial grade table.
-/

namespace T1A

open Roots Roots.Z8
open scoped Classical

/-- `ζ₈^c` as a function of `c ∈ ℤ/8`. -/
def zpow8 (c : ZMod 8) : Z8 := Z8.zeta ^ c.val

@[simp] theorem zpow8_zero : zpow8 0 = 1 := by decide

theorem zeta_pow_eight : (Z8.zeta : Z8) ^ 8 = 1 := by decide

/-- `ζ₈^k` only depends on `k mod 8`. -/
theorem zeta_pow_mod (k : ℕ) : (Z8.zeta : Z8) ^ k = Z8.zeta ^ (k % 8) := by
 conv_lhs => rw [← Nat.div_add_mod k 8, pow_add, pow_mul, zeta_pow_eight, one_pow, one_mul]

/-- `zpow8` is multiplicative: `ζ₈^(x+y) = ζ₈^x · ζ₈^y`. -/
theorem zpow8_add (x y : ZMod 8) : zpow8 (x + y) = zpow8 x * zpow8 y := by
 unfold zpow8
 rw [← pow_add, zeta_pow_mod (x.val + y.val), ZMod.val_add]

/-- The per-coefficient `λ`-valuation `ecoef c = ν_λ(ζ₈^c − 1)` for `c ≠ 0`
(odd → 1, `≡2 mod 4` → 2, `≡4 mod 8` → 4). -/
def ecoef (c : ZMod 8) : ℕ :=
 if c.val % 2 = 1 then 1 else if c.val % 4 = 2 then 2 else 4

/-- The unit witness `u_c` in `ζ₈^c − 1 = λ^(ecoef c)·u_c`. -/
def unitOf (c : ZMod 8) : Z8 :=
 match c.val with
 | 1 => ⟨-1, 0, 0, 0⟩
 | 2 => ⟨0, -1, -1, -1⟩
 | 3 => ⟨-1, -1, -1, 0⟩
 | 4 => ⟨0, 2, 3, 2⟩
 | 5 => ⟨0, -1, -1, -1⟩
 | 6 => ⟨1, 1, 0, -1⟩
 | 7 => ⟨0, 0, 0, -1⟩
 | _ => 1

/-- The inverse of `unitOf c`. -/
def unitInv (c : ZMod 8) : Z8 :=
 match c.val with
 | 1 => ⟨-1, 0, 0, 0⟩
 | 2 => ⟨0, 1, -1, 1⟩
 | 3 => ⟨-1, 0, 1, -1⟩
 | 4 => ⟨0, 2, -3, 2⟩
 | 5 => ⟨0, 1, -1, 1⟩
 | 6 => ⟨-1, 1, 0, -1⟩
 | 7 => ⟨0, 1, 0, 0⟩
 | _ => 1

/-- **Per-coefficient factorisation.** For `c ≠ 0`, `ζ₈^c − 1 = λ^(ecoef c)·u_c`. -/
theorem factor_eq : ∀ c : ZMod 8, c ≠ 0 →
 zpow8 c - 1 = Z8.lam ^ (ecoef c) * unitOf c := by decide

/-- `unitOf c · unitInv c = 1` for `c ≠ 0`. -/
theorem unitOf_mul_inv : ∀ c : ZMod 8, c ≠ 0 → unitOf c * unitInv c = 1 := by decide

theorem unitOf_isUnit (c : ZMod 8) (hc : c ≠ 0) : IsUnit (unitOf c) :=
 IsUnit.of_mul_eq_one _ (unitOf_mul_inv c hc)

/-- `λ` is not a unit (its norm is `2`). -/
theorem lam_not_isUnit : ¬ IsUnit (Z8.lam) := by
 rintro ⟨u, hu⟩
 have hdvd : Z8.lam ∣ 1 := ⟨(↑u⁻¹ : Z8), by rw [← hu]; simp⟩
 obtain ⟨v, hv⟩ := hdvd
 have : Z8.norm Z8.lam * Z8.norm v = 1 := by rw [← Z8.norm_mul, ← hv]; decide
 rw [Z8.norm_lam] at this
 omega

/-- **emultiplicity helper.** For a unit `w`, `ν_λ(λ^E·w) = E`. -/
theorem emult_lam_pow_mul_unit (E : ℕ) (w : Z8) (hw : IsUnit w) :
 emultiplicity Z8.lam (Z8.lam ^ E * w) = (E : ℕ∞) := by
 rw [emultiplicity_eq_coe]
 refine ⟨Dvd.dvd.mul_right (dvd_refl _) w, ?_⟩
 intro hdvd
 rw [pow_succ] at hdvd
 have hcancel : Z8.lam ∣ w := by
 have hne : Z8.lam ^ E ≠ 0 := Z8.lam_pow_ne_zero E
 obtain ⟨k, hk⟩ := hdvd
 refine ⟨k, ?_⟩
 apply mul_left_cancel₀ hne
 rw [← mul_assoc]
 linear_combination hk
 exact lam_not_isUnit (isUnit_of_dvd_unit hcancel hw)

end T1A
