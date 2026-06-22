import StabilizerBW.Qutrit.CSSBarnesWall.QutritGrade
import StabilizerBW.Qutrit.EisensteinToy.BW3

/-!
# TEST 1 re-run: the strict-subset closed form over the *genuine* lattice

The qubit chapter's single-coordinate strict-subset law
(`StabilizerBW.Roots/StrictSubsetLowerBoundAllN.lean`) is
`graden (topMon n d s) = 2·d − p`, with `p = ν_{λ₂}(s−1)` the `λ₂`-adic
valuation of the corner phase defect, and the **coefficient `2 = ν_{λ₂}(2)`**:
the dimension `d = 2` is `λ₂²·unit`.

the development's *toy* lattice gave the wrong coefficient `1`
(`EisensteinToy/StrictSubsetTest.lean`): it used the prime `λ₃`
itself as the lattice modulus (instead of its square), collapsing the constant
to `ν_{λ₃}(λ₃) = 1`.  The DISPATCH's naive lift proposed coefficient `3`.

Over the **genuine** lattice (`QutritGrade.lean`, modulus `λ₃² = -3ω`, an
associate of `d = 3`) the law is restored with the **correct coefficient
`2 = ν_{λ₃}(3)`**, matching the qubit case exactly:

* `gradeQ diagNegOne = 2 = correctedPredict 1 0`  (corner `−1`, defect `p = 0`);
* `gradeQ diagOmega1 = 1 = correctedPredict 1 1`  (corner `ω`, defect `p = 1`);
* the coefficient `2` is `ν_{λ₃}(3)`: `λ₃² ∣ 3` but `λ₃³ ∤ 3`
  (`lamSq_dvd_three`, `not_lamCube_dvd_three`).

The toy lattice's coefficient `1` and the naive `3` are both refuted.

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace QutritCSSBW

open QutritEis QutritEis.Eis

/-! ## The coefficient is `ν_{λ₃}(3) = 2` -/

/-- `λ₃² ∣ 3`: indeed `3 = λ₃² · (−ω²)`. -/
theorem lamSq_dvd_three : lamSq ∣ (3 : Eis) := ⟨-(omega ^ 2), by decide⟩

/-- The norm of a power is the power of the norm. -/
theorem norm_pow' (z : Eis) (n : ℕ) : Eis.norm (z ^ n) = (Eis.norm z) ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Eis.norm_mul, ih]

/-- `λ₃³ ∤ 3`: otherwise `27 = N(λ₃³) ∣ N(3) = 9`, impossible. -/
theorem not_lamCube_dvd_three : ¬ (lam ^ 3 ∣ (3 : Eis)) := by
  rintro ⟨c, hc⟩
  have hnorm : Eis.norm (3 : Eis) = Eis.norm (lam ^ 3) * Eis.norm c := by
    rw [← Eis.norm_mul, ← hc]
  have h27 : Eis.norm (lam ^ 3) = 27 := by rw [norm_pow']; decide
  have h9 : Eis.norm (3 : Eis) = 9 := by decide
  rw [h9, h27] at hnorm
  have hcnn : 0 ≤ Eis.norm c := Eis.norm_nonneg c
  omega

/-- **The genuine coefficient is `ν_{λ₃}(3) = 2`**: `λ₃² ∣ 3` and `λ₃³ ∤ 3`. -/
theorem coefficient_is_nu_lam_three :
    lamSq ∣ (3 : Eis) ∧ ¬ (lam ^ 3 ∣ (3 : Eis)) :=
  ⟨lamSq_dvd_three, not_lamCube_dvd_three⟩

/-! ## The strict-subset predictions -/

/-- The DISPATCH's naive qutrit-lift prediction `max(0, 3·d − 3^m)`. -/
def naivePredict (d m : ℕ) : ℕ := 3 * d - 3 ^ m

/-- The qubit prediction `max(0, 2·d − 2^m)`. -/
def qubitPredict (d m : ℕ) : ℕ := 2 * d - 2 ^ m

/-- the development's toy-lattice prediction (coefficient `1`): `max(0, 1·d − p)`. -/
def toyPredict (d p : ℕ) : ℕ := 1 * d - p

/-- The **corrected** genuine-lattice prediction (coefficient `2 = ν_{λ₃}(3)`):
`max(0, 2·d − p)`. -/
def correctedPredict (d p : ℕ) : ℕ := 2 * d - p

/-! ## The genuine grades match the corrected coefficient-`2` law -/

/-- Corner `−1` (`|S| = d = 1`, defect `p = ν_{λ₃}(−1−1) = ν_{λ₃}(−2) = 0`):
the corrected law gives `2·1 − 0 = 2`, the actual genuine grade. -/
theorem strict_subset_corrected_negOne :
    gradeQ diagNegOne = correctedPredict 1 0 := by
  rw [gradeQ_diagNegOne]; decide

/-- Corner `ω` (`|S| = d = 1`, defect `p = ν_{λ₃}(ω−1) = 1`): the corrected law
gives `2·1 − 1 = 1`, the actual genuine grade. -/
theorem strict_subset_corrected_omega :
    gradeQ diagOmega1 = correctedPredict 1 1 := by
  rw [gradeQ_diagOmega1]; decide

/-- The naive coefficient `3` is refuted: it predicts `max(0, 3·1 − 3^1) = 0`,
but the genuine grade of the corner-`−1` phase is `2`. -/
theorem strict_subset_naive_refuted :
    gradeQ diagNegOne ≠ naivePredict 1 1 := by
  rw [gradeQ_diagNegOne]; decide

/-- The toy-lattice coefficient `1` is refuted: it predicts `1·1 − 0 = 1`, but
the genuine grade is `2`.  (Concretely, the toy lattice records
`QutritEis.gradeEMat diagNegOne = 1`, while the genuine lattice gives `2`.) -/
theorem strict_subset_toy_coefficient_refuted :
    gradeQ diagNegOne ≠ toyPredict 1 0 := by
  rw [gradeQ_diagNegOne]; decide

/-- The toy lattice's grade `1` and the genuine lattice's grade `2` for the same
Clifford phase `−1`, exhibited side by side. -/
theorem toy_vs_genuine_negOne :
    QutritEis.gradeEMat QutritEis.diagNegOne = 1 ∧ gradeQ diagNegOne = 2 :=
  ⟨QutritEis.gradeEMat_diag_negOne, gradeQ_diagNegOne⟩

/-! ## Headline -/

/-- **TEST 1 re-run (headline): the strict-subset coefficient is `2 = ν_{λ₃}(3)`,
matching the qubit `ν_{λ₂}(2) = 2`.**

Over the genuine qutrit Barnes–Wall lattice the single-coordinate Clifford phase
`−1` has grade exactly `2`, equal to:
* the corrected coefficient-`2` prediction `correctedPredict 1 0`, and
* the `λ₃`-adic valuation of the dimension, `ν_{λ₃}(3) = 2` (`λ₃² ∣ 3`, `λ₃³ ∤ 3`);

while the toy-lattice coefficient `1` and the DISPATCH's naive coefficient `3`
are both refuted. -/
theorem qutrit_strict_subset_coefficient_eq_2 :
    gradeQ diagNegOne = 2 ∧
    gradeQ diagNegOne = correctedPredict 1 0 ∧
    (lamSq ∣ (3 : Eis) ∧ ¬ (lam ^ 3 ∣ (3 : Eis))) ∧
    gradeQ diagNegOne ≠ toyPredict 1 0 ∧
    gradeQ diagNegOne ≠ naivePredict 1 1 :=
  ⟨gradeQ_diagNegOne, strict_subset_corrected_negOne, coefficient_is_nu_lam_three,
   strict_subset_toy_coefficient_refuted, strict_subset_naive_refuted⟩

end QutritCSSBW
