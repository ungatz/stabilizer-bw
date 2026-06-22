import StabilizerBW.Qutrit.EisensteinToy.StrictSubsetTest
import StabilizerBW.Qutrit.EisensteinToy.MobiusTest
import StabilizerBW.Qutrit.EisensteinToy.TCountTest
import StabilizerBW.Qutrit.EisensteinToy.IncomparabilityTest

/-!
# T8 — Summary: classifying the qubit machinery at `d = 3`

This file collects the four test outcomes of the qutrit Eisenstein stress-test into a single
headline.  The verdict is **PARTIALLY GENERAL**: the combinatorial / valuation *backbone* lifts
cleanly to `ℤ[ω]`, but two arithmetic facts are genuinely `ℤ[ζ₈]`/qubit-specific.

## The four tests

* **TEST 1 (strict-subset closed form) — FAILS.** The naive coefficient lift `2 ↦ 3`
  (`max(0, 3·|S| − 3^{|U|})`) is wrong; the actual level-1 coefficient is `1` (the `λ₃`-valuation
  of the prime above `d = 3`).  Witness: `gradeEMat diagNegOne = 1 ≠ 0 = naivePredict 1 1`
  (`StrictSubsetTest.strict_subset_naive_refuted`).

* **TEST 2 (multi-monomial Möbius closed form) — MACHINERY GENERALISES.** Möbius inversion and
  the divisibility ↔ valuation bridge both hold over `ℤ[ω]`
  (`MobiusTest.mobius_machinery_generalises`); only the grade constant differs (TEST 1).

* **TEST 3 (T-count vs grade) — FAILS.** The Howard–Vala qutrit T-gate phase `ζ₉` is not an
  Eisenstein integer: there is no primitive 9th root of unity in `ℤ[ω]`
  (`TCountTest.no_isPrimitiveRoot_nine`).  The qutrit Clifford+T level `ℤ[ζ₉]` strictly exceeds
  the Eisenstein level `ℤ[ζ₃]`.

* **TEST 4 (cT vs CCZ incomparability) — FAILS TO REPRODUCE.** The diagnostic `T`-bearing gates
  carry `ζ₉` phases, hence are unrepresentable over `ℤ[ω]`
  (`IncomparabilityTest.diagnostic_gates_unrepresentable`); moreover the Eisenstein lattice does
  not keep the qutrit Clifford phase `-1` grade-`0`
  (`IncomparabilityTest.clifford_phase_has_nonzero_grade`).

## A correction to the DISPATCH

The DISPATCH's ramification identity `λ₃² = -3·(1 + 2ω)` with `1 + 2ω` a unit is **false**:
`1 + 2ω` has norm `3` (it is `√(-3) = ω·λ₃`, an associate of the prime, not a unit).  The correct
identity is `λ₃² = -3·ω` with `ω` the unit
(`EisensteinIntegers.Eis.lam_sq_assoc`, `EisensteinIntegers.Eis.one_add_two_omega_not_unit`).

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace QutritEis
open Eis

/-- **Headline classification (PARTIALLY GENERAL).** The conjunction of the four test outcomes:

1. the strict-subset closed-form coefficient does NOT lift as `2 ↦ 3` (TEST 1 fails);
2. the Möbius-inversion + valuation-bridge backbone DOES generalise to `ℤ[ω]` (TEST 2);
3. the qutrit T-gate phase escapes `ℤ[ω]` (no primitive 9th root) (TEST 3 fails);
4. the incomparability diagnostic gates are unrepresentable over `ℤ[ω]` (TEST 4 fails). -/
theorem chapter_is_partially_general_at_d3 :
    -- TEST 1 fails: naive constant `3` refuted
    (gradeEMat diagNegOne ≠ naivePredict 1 1) ∧
    -- TEST 2 generalises: backbone holds over `ℤ[ω]`
    ((∀ {n : ℕ} (f : Finset (Fin n) → Eis) (U : Finset (Fin n)), mobT (zetaT f) U = f U) ∧
      (∀ {n : ℕ} (f : Finset (Fin n) → Eis) (U : Finset (Fin n)) (a j : ℕ),
        lam ^ a ∣ lam ^ j * (mobT f U) ↔ (a : ℕ∞) ≤ j + Eis.valLam (mobT f U))) ∧
    -- TEST 3 fails: no primitive 9th root of unity in `ℤ[ω]`
    (¬ ∃ z : Eis, IsPrimitiveRoot z 9) ∧
    -- TEST 4 fails: diagnostic gates unrepresentable, Clifford phase not grade-0
    ((¬ ∃ z : Eis, IsPrimitiveRoot z 9) ∧
      (gradeEMat diagOmega = 0 ∧ gradeEMat diagNegOne = 1)) :=
  ⟨strict_subset_naive_refuted,
   mobius_machinery_generalises,
   no_isPrimitiveRoot_nine,
   diagnostic_gates_unrepresentable, clifford_phase_has_nonzero_grade⟩

/-- **The DISPATCH ramification-unit claim is false; the corrected identity holds.** -/
theorem integrality_corrections :
    (¬ IsUnit Eis.sqrtNeg3) ∧
    (Eis.lam ^ 2 ≠ -3 * Eis.sqrtNeg3) ∧
    (∃ v : Eis, IsUnit v ∧ Eis.lam ^ 2 = -3 * v) :=
  ⟨Eis.one_add_two_omega_not_unit, Eis.sqrtNeg3_lam_sq_ne, Eis.lam_sq_assoc⟩

end QutritEis
