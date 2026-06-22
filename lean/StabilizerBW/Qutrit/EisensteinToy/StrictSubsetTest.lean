import StabilizerBW.Qutrit.EisensteinToy.BW3

/-!
# TEST 1: the strict-subset closed form

The qubit chapter's single-monomial law is `g(D_{c·x_S}) = max(0, 2·|S| − p)`, where `p` is the
`λ₂`-adic valuation of the corner phase `c − 1`; the coefficient `2` is the `λ₂`-valuation of the
"doubling prime" `1+i` above the dimension `d = 2` (`(1+i) = λ₂²·unit`).  The DISPATCH proposes
the naive qutrit lift `g = max(0, 3·|S| − 3^{|U|})`, replacing `2` by `3`.

We test this on the Eisenstein lattice `L = {(x,y) : λ₃ ∣ (x+y)}` of `BW3.lean`.  A direct
valuation computation (carried out concretely for the representable phases) gives the **actual**
level-1 single-monomial law

  `g(diag(1, c)) = max(0, 1·|S| − p)`,  `p = ν_{λ₃}(c − 1)`,

with coefficient **`1`**, not `3`: the prime above the dimension `d = 3` in `ℤ[ω]` is `λ₃`
itself, with `ν_{λ₃}(λ₃) = 1` (`3` is ramified with exponent `2`, so `(3) = (λ₃)²`, but the
relevant *doubling* prime above `d = 3` is `λ₃`, of valuation `1`).

**Conclusion: TEST 1 fails** — the naive coefficient `3` is wrong (and, separately, so is the
qubit coefficient `2`).  Concrete refutation: the monomial `diag(1, -1)` (support `|S| = 1`,
`|U| = 1`) has grade `1`, whereas the naive formula `max(0, 3·1 − 3^1) = 0` predicts `0`
(`strict_subset_naive_refuted`); the qubit formula `max(0, 2·1 − 2^1) = 0` is also wrong
(`strict_subset_qubit_formula_also_wrong`).  The corrected level-1 law (coefficient `1`) is
recorded in `gradeEMat_diag_omega`/`gradeEMat_diag_negOne`.

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace QutritEis
open Eis

/-- The DISPATCH's naive qutrit-lift prediction `max(0, 3·d − 3^m)` (`ℕ` truncated subtraction). -/
def naivePredict (d m : ℕ) : ℕ := 3 * d - 3 ^ m

/-- The qubit prediction `max(0, 2·d − 2^m)`. -/
def qubitPredict (d m : ℕ) : ℕ := 2 * d - 2 ^ m

/-- The corrected qutrit level-1 prediction `max(0, 1·d − p)` (coefficient `1`). -/
def correctedPredict (d p : ℕ) : ℕ := 1 * d - p

theorem naivePredict_one_one : naivePredict 1 1 = 0 := by decide
theorem qubitPredict_one_one : qubitPredict 1 1 = 0 := by decide

/-- The monomial `diag(1, -1)` has support `|S| = 1`, phase valuation `p = ν_{λ₃}(-1-1) = 0`,
and grade `1` — matching the corrected coefficient-`1` law `max(0, 1·1 − 0) = 1`. -/
theorem correctedPredict_diag_negOne : correctedPredict 1 0 = 1 := by decide

/-- **TEST 1 refuted (naive coefficient `3`).** The grade of `diag(1, -1)` is `1`, but the
naive formula `max(0, 3·1 − 3^1)` predicts `0`. -/
theorem strict_subset_naive_refuted :
    gradeEMat diagNegOne ≠ naivePredict 1 1 := by
  rw [gradeEMat_diag_negOne, naivePredict_one_one]; decide

/-- The qubit coefficient `2` is also wrong here (predicts `0`, actual is `1`). -/
theorem strict_subset_qubit_formula_also_wrong :
    gradeEMat diagNegOne ≠ qubitPredict 1 1 := by
  rw [gradeEMat_diag_negOne, qubitPredict_one_one]; decide

/-- **The corrected coefficient `1` matches.** For `diag(1, -1)` (`|S| = 1`, `p = 0`)
the corrected law gives the actual grade `1`. -/
theorem strict_subset_corrected_holds :
    gradeEMat diagNegOne = correctedPredict 1 0 := by
  rw [gradeEMat_diag_negOne, correctedPredict_diag_negOne]

/-- And for the order-3 phase `ω` (`|S| = 1`, `p = ν_{λ₃}(ω - 1) = 1`) the corrected law gives
the actual grade `0`. -/
theorem strict_subset_corrected_holds_omega :
    gradeEMat diagOmega = correctedPredict 1 1 := by
  rw [gradeEMat_diag_omega]; decide

end QutritEis
