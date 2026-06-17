import StabilizerBW.Roots.Grades
import StabilizerBW.Roots.Level4

/-!
# Cross-level self-similarity of the Barnes–Wall grade (Target T3)

The level-raising identity `(1 − ζ₁₆)² = (1 − ζ₈)·u'` (`Z16.lam16_sq`, i.e. `λ₁₆² ∼ λ₈`)
says that one cyclotomic level is a single ramified quadratic step: a `λ₈`-step at level 3
becomes *two* `λ₁₆`-steps at level 4. This file lifts that ring identity to a statement
about the **grade filtration** itself, grounding the level-4 grade table of `Level4.lean`
in the genuine, separately-proved **level-3 grade** `g₃(T) = 1` (`Roots.grade_T`, the
single-qubit grade over the level-3 Barnes–Wall lattice `L₃ ⊂ ℤ[ζ₈]²`).

## The two grades in play

* `g₃ := Roots.grade` — the level-3 grade `g₃(U) = min k, λ₈^k·U·L₃ ⊆ L₃`
 (over `ℤ[ζ₈]`, `Grades.lean`). Here `g₃(T) = 1` (`grade_T`).
* `g₄ := Roots.graded` — the level-4 grade `g₄,d(D) = min k, λ₁₆^k·D·L_d ⊆ L_d`
 (over `ℤ[ζ₁₆]`, `Level4.lean`) for the two lattices
 * `L4a = {(a,b) : λ₈ ∣ a+b}` — the genuine level-4 design,
 * `L4b = {(a,b) : (1+i) ∣ a+b}` — the **base change** of the level-3 lattice
 (`(1+i) ∼ λ₁₆⁴ ∼ λ₈²`).

The generators are `T = diag(1, ζ₈)` (`T16`), its square root `√T = diag(1, ζ₁₆)`
(`sqrtT16`), and the scalar `ζ₁₆·I` (`zI16`).

## Main results (each grounded in `grade_T : grade T = 1`)

* **Level self-similarity** (`crossLevel_self_similar`):
 `g₄,L4a(√T) = g₃(T)`. Level 4 prices *its own* new generator `√T` at exactly the
 same grade `1` that level 3 charged for *its* new generator `T`.
* **Base-change doubling** (`crossLevel_base_change`):
 `g₄,L4b(T) = 2·g₃(T)` and `g₄,L4b(√T) = 2·g₃(T) + 1`. Re-grading the level-3
 generator against the base-changed lattice exactly doubles its grade (with the extra
 half-rung for the square root), the grade-level shadow of `λ₁₆² ∼ λ₈`.
* **Base-change rung** (`crossLevel_base_change_rung`):
 `g₄,L4b(U) = g₄,L4a(U) + 2` for both `U ∈ {T, √T}`, while scalars are unaffected
 (`g₄,L4b(ζ₁₆I) = g₄,L4a(ζ₁₆I) = 0`); the base change to `L4b` (divisor `λ₁₆⁴` vs
 `λ₁₆²`) lifts every non-scalar grade by the two-rung depth difference `4 − 2`.
-/

namespace Roots
open Z16 Mat2

/-- The level-raising identity in associate form, `λ₁₆² ∼ λ₈` (re-export of
`Z16.lam16_sq_assoc`): there is a unit `v` with `λ₁₆² = λ₈·v`. This is the arithmetic
source of every cross-level doubling below. -/
theorem cross_level_ramification : ∃ v vinv : Z16, v * vinv = 1 ∧ lam16 ^ 2 = lam8 * v := by
 obtain ⟨v, vinv, hv, he⟩ := Z16.lam16_sq_assoc
 exact ⟨v, vinv, hv, by rw [pow_two]; exact he⟩

/-! ## Level self-similarity -/

/-- **Level self-similarity.** The level-4 lattice `L4a` prices its own new generator
`√T` at exactly the level-3 grade of `T`: `g₄,L4a(√T) = g₃(T)`. Both equal `1`: each
cyclotomic level charges grade `1` for the single fresh square-root generator it
introduces. -/
theorem crossLevel_self_similar : graded lam8 sqrtT16 = grade T := by
 rw [grade_T]; exact grade_a_sqrtT

/-! ## Base-change doubling -/

/-- **Base-change doubling for `T`.** Re-grading the level-3 generator `T` against the
base-changed lattice `L4b` doubles its level-3 grade: `g₄,L4b(T) = 2·g₃(T)` (both sides
`= 2`). -/
theorem crossLevel_base_change_T : graded oneI16 T16 = 2 * grade T := by
 rw [grade_T]; exact grade_b_T

/-- **Base-change doubling for `√T`.** `g₄,L4b(√T) = 2·g₃(T) + 1` (both sides `= 3`):
the doubling of `T`'s grade plus the one extra rung for taking a square root. -/
theorem crossLevel_base_change_sqrtT : graded oneI16 sqrtT16 = 2 * grade T + 1 := by
 rw [grade_T]; exact grade_b_sqrtT

/-- **Base-change doubling (combined).** Grounded in `g₃(T) = 1`:
`g₄,L4a(√T) = g₃(T)`, `g₄,L4b(T) = 2·g₃(T)`, `g₄,L4b(√T) = 2·g₃(T) + 1`. -/
theorem crossLevel_base_change :
 graded lam8 sqrtT16 = grade T ∧
 graded oneI16 T16 = 2 * grade T ∧
 graded oneI16 sqrtT16 = 2 * grade T + 1 :=
 ⟨crossLevel_self_similar, crossLevel_base_change_T, crossLevel_base_change_sqrtT⟩

/-! ## The base-change rung -/

/-- **The base-change rung.** Passing from the genuine level-4 lattice `L4a` (divisor
`λ₈ ∼ λ₁₆²`) to the base change `L4b` (divisor `1+i ∼ λ₁₆⁴`) lifts the grade of every
non-scalar generator by exactly the two-rung depth difference, while leaving scalars
fixed:
`g₄,L4b(T) = g₄,L4a(T) + 2`, `g₄,L4b(√T) = g₄,L4a(√T) + 2`, `g₄,L4b(ζ₁₆I) = g₄,L4a(ζ₁₆I)`. -/
theorem crossLevel_base_change_rung :
 graded oneI16 T16 = graded lam8 T16 + 2 ∧
 graded oneI16 sqrtT16 = graded lam8 sqrtT16 + 2 ∧
 graded oneI16 zI16 = graded lam8 zI16 := by
 refine ⟨?_, ?_, ?_⟩
 · rw [grade_b_T, grade_a_T]
 · rw [grade_b_sqrtT, grade_a_sqrtT]
 · rw [grade_b_zI, grade_a_zI]

/-- **The cross-level table, fully grounded.** The complete level-3 ⇄ level-4
correspondence: the level-3 grade `g₃(T) = 1` together with the six level-4 grades and
their self-similar / base-change-doubled relationships. -/
theorem crossLevel_table :
 grade T = 1 ∧
 graded lam8 T16 = 0 ∧ graded lam8 sqrtT16 = grade T ∧ graded lam8 zI16 = 0 ∧
 graded oneI16 T16 = 2 * grade T ∧ graded oneI16 sqrtT16 = 2 * grade T + 1 ∧
 graded oneI16 zI16 = 0 :=
 ⟨grade_T, grade_a_T, crossLevel_self_similar, grade_a_zI,
 crossLevel_base_change_T, crossLevel_base_change_sqrtT, grade_b_zI⟩

end Roots
