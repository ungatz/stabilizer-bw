import StabilizerBW.Roots.Core
import Mathlib

/-!
# The ring `ℤ[ζ₈]` is a domain, and the `λ`-adic divisibility ↔ valuation bridge

This file supplies the two ring-theoretic facts the general-`n` Möbius closed form needs:

* `Roots.Z8.instIsDomain` — `ℤ[ζ₈]` has no zero divisors (via the field norm
  `N(x) = P² + Q²`, `P = a² − c² + 2bd`, `Q = d² − b² + 2ac`, which is multiplicative and
  vanishes only at `0`).
* `Roots.Z8.lam_pow_dvd_lam_pow_mul_iff` — for the ramified prime `λ = 1 − ζ`,
  `λ^a ∣ λ^j · y ↔ (a : ℕ∞) ≤ j + emultiplicity λ y`, the bridge converting `λ`-power
  divisibility (the lattice side) into the `λ`-adic valuation `ν_λ = emultiplicity λ`
  (the closed-form side).

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace Roots
namespace Z8

open scoped Classical

/-- The field norm `N : ℤ[ζ₈] → ℤ`, `N(x) = P² + Q²` with
`P = a² − c² + 2bd`, `Q = d² − b² + 2ac` (the product of the four Galois conjugates). -/
def norm (x : Z8) : ℤ :=
  (x.a^2 - x.c^2 + 2*x.b*x.d)^2 + (x.d^2 - x.b^2 + 2*x.a*x.c)^2

theorem norm_mul (x y : Z8) : norm (x * y) = norm x * norm y := by
  simp only [norm, Z8.mul_a, Z8.mul_b, Z8.mul_c, Z8.mul_d]; ring

/-
**Anisotropy of the norm form.** The integral quaternary form `P² + Q²` (with
`P = a² − c² + 2bd`, `Q = d² − b² + 2ac`) vanishes only at the origin.  This is a genuine
number-theoretic fact (the form is isotropic over `ℝ` but anisotropic over `ℚ`): it is the
statement that `-i` is not a square in `ℚ(i)`.
-/
theorem norm_form_anisotropic (a b c d : ℤ)
    (hP : a^2 - c^2 + 2*b*d = 0) (hQ : d^2 - b^2 + 2*a*c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  by_contra! h_nonzero;
  obtain ⟨g, u, v, hg, hu, hv⟩ : ∃ g u v : GaussianInt, g ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧ u^2 + Complex.I * v^2 = 0 := by
    refine' ⟨ 1, ⟨ a, c ⟩, ⟨ d, -b ⟩, _, _, _, _ ⟩ <;> simp_all +decide [ Complex.ext_iff, sq ];
    · simp_all +decide [ Zsqrtd.ext_iff ];
      aesop;
    · simp_all +decide [ Zsqrtd.ext_iff ];
      aesop;
    · constructor <;> norm_cast <;> linarith;
  -- If $v \neq 0$, then $u^2 = -i v^2$. Since $u$ and $v$ are coprime, $v^2$ must divide $u^2$, implying $v$ divides $u$.
  obtain ⟨k, hk⟩ : ∃ k : GaussianInt, u = k * v := by
    have h_div : v^2 ∣ u^2 := by
      use -⟨0, 1⟩;
      exact Zsqrtd.ext ( by simpa [ ← @Int.cast_inj ℝ ] using by norm_num [ Complex.ext_iff, sq ] at *; linarith ) ( by simpa [ ← @Int.cast_inj ℝ ] using by norm_num [ Complex.ext_iff, sq ] at *; linarith );
    exact exists_eq_mul_left_of_dvd <| by simpa using h_div;
  simp_all +decide [ mul_pow ];
  -- Since $v \neq 0$, we can divide both sides of the equation by $v^2$ to get $k^2 + i = 0$.
  have h_div : k^2 + Complex.I = 0 := by
    exact mul_left_cancel₀ ( pow_ne_zero 2 ( show GaussianInt.toComplex v ≠ 0 from by simpa [ GaussianInt.toComplex_inj ] using hv.1 ) ) ( by linear_combination' hv.2 );
  rcases k with ⟨ k₁, k₂ ⟩ ; norm_num [ Complex.ext_iff, sq ] at h_div;
  norm_cast at h_div; nlinarith [ show k₁ * k₂ = -1 by linarith ] ;

theorem norm_eq_zero {x : Z8} (h : norm x = 0) : x = 0 := by
  have hP : x.a^2 - x.c^2 + 2*x.b*x.d = 0 := by
    have hsq : (x.a^2 - x.c^2 + 2*x.b*x.d)^2 = 0 := by
      have h1 : (x.a^2 - x.c^2 + 2*x.b*x.d)^2 ≥ 0 := sq_nonneg _
      have h2 : (x.d^2 - x.b^2 + 2*x.a*x.c)^2 ≥ 0 := sq_nonneg _
      unfold norm at h; nlinarith [h, h1, h2]
    exact pow_eq_zero_iff (by norm_num) |>.mp hsq
  have hQ : x.d^2 - x.b^2 + 2*x.a*x.c = 0 := by
    have hsq : (x.d^2 - x.b^2 + 2*x.a*x.c)^2 = 0 := by
      have h1 : (x.a^2 - x.c^2 + 2*x.b*x.d)^2 ≥ 0 := sq_nonneg _
      have h2 : (x.d^2 - x.b^2 + 2*x.a*x.c)^2 ≥ 0 := sq_nonneg _
      unfold norm at h; nlinarith [h, h1, h2]
    exact pow_eq_zero_iff (by norm_num) |>.mp hsq
  obtain ⟨ha, hb, hc, hd⟩ := norm_form_anisotropic x.a x.b x.c x.d hP hQ
  exact Z8.ext' ha hb hc hd

theorem norm_zero : norm 0 = 0 := by decide

theorem norm_lam : norm lam = 2 := by decide

instance : Nontrivial Z8 := ⟨0, 1, by decide⟩

instance instNoZeroDivisors : NoZeroDivisors Z8 where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    have hn : norm x * norm y = 0 := by rw [← norm_mul, h, norm_zero]
    rcases mul_eq_zero.mp hn with hx | hy
    · exact Or.inl (norm_eq_zero hx)
    · exact Or.inr (norm_eq_zero hy)

instance instIsDomain : IsDomain Z8 := NoZeroDivisors.to_isDomain Z8

theorem lam_ne_zero : lam ≠ 0 := by decide

theorem lam_pow_ne_zero (j : ℕ) : lam ^ j ≠ 0 := pow_ne_zero j lam_ne_zero

/-- **The divisibility ↔ valuation bridge.** For the ramified prime `λ`,
`λ^a ∣ λ^j · y ↔ (a : ℕ∞) ≤ j + ν_λ(y)`, where `ν_λ = emultiplicity λ`. -/
theorem lam_pow_dvd_lam_pow_mul_iff (a j : ℕ) (y : Z8) :
    lam ^ a ∣ lam ^ j * y ↔ (a : ℕ∞) ≤ j + emultiplicity lam y := by
  rcases Nat.lt_or_ge a j with haj | haj
  · -- a < j : both sides hold
    constructor
    · intro _
      calc (a : ℕ∞) ≤ (j : ℕ∞) := by exact_mod_cast (le_of_lt haj)
        _ ≤ j + emultiplicity lam y := le_self_add
    · intro _
      exact Dvd.dvd.mul_right (pow_dvd_pow lam (le_of_lt haj)) y
  · -- a ≥ j : cancel λ^j
    have hcancel : lam ^ a ∣ lam ^ j * y ↔ lam ^ (a - j) ∣ y := by
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
      -- (a:ℕ∞) ≤ j + emult, and a ≥ j, so (a-j) ≤ emult
      have hcast : (a : ℕ∞) = (j : ℕ∞) + ((a - j : ℕ) : ℕ∞) := by
        have hh : a = j + (a - j) := by omega
        calc (a : ℕ∞) = ((j + (a - j) : ℕ) : ℕ∞) := by exact_mod_cast hh
          _ = (j : ℕ∞) + ((a - j : ℕ) : ℕ∞) := by push_cast; rfl
      rw [hcast] at h
      exact WithTop.le_of_add_le_add_left (ENat.coe_ne_top j) h

end Z8
end Roots