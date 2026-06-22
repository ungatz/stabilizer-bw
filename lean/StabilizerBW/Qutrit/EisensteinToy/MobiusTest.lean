import StabilizerBW.Qutrit.EisensteinToy.QutritPhasePoly
import StabilizerBW.Qutrit.EisensteinToy.BW3

/-!
# TEST 2: the multi-monomial Möbius closed form

The qubit closed form (`Roots.mobius_eq_grade_allN`) reads

  `graden D = ⨆_{∅ ≠ U} (2·|U| − ν_{λ₂}(m_U))`,  `m_U = down-set Möbius coefficient of D`.

It rests on exactly two ingredients:

1. the **down-set Möbius transform** and its inversion (a characteristic-independent piece of
   combinatorics), and
2. the **divisibility ↔ valuation bridge** for the ramified prime, converting `λ`-power
   divisibility into the `λ`-adic valuation.

This file records that *both ingredients generalise verbatim to `d = 3`*:

* `mobT_zetaT_eis` — the Möbius inversion holds over the Eisenstein integers `ℤ[ω]`
  (instantiation of `mobT_zetaT` at `R = Eis`);
* `mobT_zetaT_zmod9` — and over the qutrit phase ring `ZMod 9`;
* `mobius_bridge_eis` — for any Möbius coefficient `m_U : ℤ[ω]`, `λ₃`-power divisibility is
  governed by `ν_{λ₃}` exactly as in the qubit case.

Hence the **shape** of the closed form is preserved.  What is *not* preserved is the arithmetic
**constant**: the `2·|U|` becomes `1·|U|`, not `3·|U|` (the prime above `d = 3` is `λ₃` with
`ν_{λ₃}(λ₃) = 1`); this is the falsification carried out in `StrictSubsetTest.lean`.

**Conclusion: TEST 2's machinery generalises; only the grade constant is `ℤ[ζ₈]`-specific.**

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace QutritEis
open Eis

/-- Möbius inversion over the Eisenstein integers `ℤ[ω]`. -/
theorem mobT_zetaT_eis {n : ℕ} (f : Finset (Fin n) → Eis) (U : Finset (Fin n)) :
    mobT (zetaT f) U = f U :=
  mobT_zetaT f U

/-- Möbius inversion over the qutrit phase ring `ZMod 9`. -/
theorem mobT_zetaT_zmod9 {n : ℕ} (f : Finset (Fin n) → ZMod 9) (U : Finset (Fin n)) :
    mobT (zetaT f) U = f U :=
  mobT_zetaT f U

/-- **The valuation bridge applies to every Eisenstein Möbius coefficient.** For a Möbius
coefficient `m_U = mobT f U`, `λ₃`-power divisibility is governed by the `λ₃`-adic valuation,
exactly as the qubit closed form requires. -/
theorem mobius_bridge_eis {n : ℕ} (f : Finset (Fin n) → Eis) (U : Finset (Fin n))
    (a j : ℕ) :
    lam ^ a ∣ lam ^ j * (mobT f U) ↔ (a : ℕ∞) ≤ j + Eis.valLam (mobT f U) :=
  Eis.lam_pow_dvd_lam_pow_mul_iff a j (mobT f U)

/-- **TEST 2 (headline): the closed-form machinery generalises to `d = 3`.** Both ingredients of
the qubit Möbius/grade closed form — Möbius inversion and the divisibility ↔ valuation bridge —
hold over the Eisenstein integers. -/
theorem mobius_machinery_generalises :
    (∀ {n : ℕ} (f : Finset (Fin n) → Eis) (U : Finset (Fin n)), mobT (zetaT f) U = f U) ∧
    (∀ {n : ℕ} (f : Finset (Fin n) → Eis) (U : Finset (Fin n)) (a j : ℕ),
      lam ^ a ∣ lam ^ j * (mobT f U) ↔ (a : ℕ∞) ≤ j + Eis.valLam (mobT f U)) :=
  ⟨fun f U => mobT_zetaT_eis f U, fun f U a j => mobius_bridge_eis f U a j⟩

end QutritEis
