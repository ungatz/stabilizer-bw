import StabilizerBW.Roots.BW3
import StabilizerBW.Roots.Tensor

/-!
# Embedding invariance (T1.3) and the linear-formula audit (T2.1 / T2.2)

This file collects the consequences of the tensor structure that are stated at the
concrete levels `n ≤ 3` already mechanized in `Roots.BW2` / `Roots.BW3`.

## T1.3 — embedding preserves the grade (`g(D ⊗ I) = g(D)`)

For every two-qubit diagonal character `D` that has been tabulated, attaching a fresh
idle qubit (`D ↦ D ⊗ I`, the level `2 → 3` embedding) leaves the grade unchanged.
This is the `n → n+1` invariance tested ad hoc in round R3, here stated as the exact
equalities `g_{BW₃}(D ⊗ I) = g_{BW₂}(D)`.

## T2.1 — the linear closed form `w(d, ν) = max(0, 2d − 2^ν)` (monomial case, audited d ≤ 3)

For a single-monomial diagonal character `D_{c·x_S}` with `d = |S|` and `ν = ν₂(c mod 8)`,
the conjectured grade is `w(d, ν) = max(0, 2d − 2^ν)` (`Roots.wFit`). We verify the
**equality** `g = w(d, ν)` for every single-monomial character computed at `n ≤ 3`:

| character | `(d, ν)` | grade | `wFit d ν` |
|---|---|---|---|
| `T` (`ζ·x₁`) | `(1, 0)` | `1` | `max(0, 2−1) = 1` |
| `CS` (`2·x₁x₂`) | `(2, 1)` | `2` | `max(0, 4−2) = 2` |
| `cT` (`1·x₁x₂`) | `(2, 0)` | `3` | `max(0, 4−1) = 3` |
| `CCZ` (`4·x₁x₂x₃`) | `(3, 2)` | `2` | `max(0, 6−4) = 2` |
| `CCS` (`2·x₁x₂x₃`) | `(3, 1)` | `4` | `max(0, 6−2) = 4` |
| `ccT` (`1·x₁x₂x₃`) | `(3, 0)` | `5` | `max(0, 6−1) = 5` |

This is the audit-fallback at small `n`; the general-`n` upper bound requires the
full `BW_n` tower (see `BWn.lean` and `UpperBoundAllN.lean`), but every tabulated case
here satisfies the linear formula *exactly* (so in particular the `≤` upper bound holds).

## T2.2 — the additive bound (disjoint-support sum), audited

For the mixed character `e = x₁x₂ + x₃` the grade is the sum of the per-monomial
weights `g = wFit 2 0 + wFit 1 0 = 3 + 1 = 4` (`Roots.additivity_mixed` and
`linear_bound_mixed`), so the additive upper bound is tight in that case.
-/

namespace Roots
open Z8 Mat2

/-! ## T1.3 — embedding preserves the grade -/

/-- **T1.3: `g(CZ ⊗ I) = g(CZ)`.** -/
theorem embed_CZ : grade3 CZI = grade2 CZ := by rw [grade3_CZI, grade2_CZ]

/-- **T1.3: `g((T⊗I) ⊗ I) = g(T⊗I)`.** -/
theorem embed_TI : grade3 TII = grade2 TI := by rw [grade3_TII, grade2_TI]

/-- **T1.3: `g(CS ⊗ I) = g(CS)`.** -/
theorem embed_CS : grade3 CSI = grade2 CS := by rw [grade3_CSI, grade2_CS]

/-- **T1.3: `g(cT ⊗ I) = g(cT)`.** -/
theorem embed_cT : grade3 cTI = grade2 cT := by rw [grade3_cTI, grade2_cT]

/-- **T1.3: `g((T⊗T) ⊗ I) = g(T⊗T)`.** -/
theorem embed_TT : grade3 TTI = grade2 TT := by rw [grade3_TTI, grade2_TT]

/-! ## T2.1 — the linear closed form, audited at `d ≤ 3` (single monomials) -/

/-- **T2.1 (audit, exact form).** Every tabulated single-monomial diagonal character
satisfies `g = wFit d ν = max(0, 2d − 2^ν)`. -/
theorem linear_form_audit :
 grade T = wFit 1 0 ∧
 grade2 CS = wFit 2 1 ∧ grade2 cT = wFit 2 0 ∧
 grade3 CCZ = wFit 3 2 ∧ grade3 CCS = wFit 3 1 ∧ grade3 ccT = wFit 3 0 := by
 refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
 · rw [grade_T]; decide
 · rw [grade2_CS]; decide
 · rw [grade2_cT]; decide
 · rw [grade3_CCZ]; decide
 · rw [grade3_CCS]; decide
 · rw [grade3_ccT]; decide

/-- **T2.1 (audit, upper bound form).** The grade is bounded above by the linear
formula `wFit d ν` in every tabulated single-monomial case. -/
theorem linear_bound_audit :
 grade T ≤ wFit 1 0 ∧
 grade2 CS ≤ wFit 2 1 ∧ grade2 cT ≤ wFit 2 0 ∧
 grade3 CCZ ≤ wFit 3 2 ∧ grade3 CCS ≤ wFit 3 1 ∧ grade3 ccT ≤ wFit 3 0 := by
 obtain ⟨h1, h2, h3, h4, h5, h6⟩ := linear_form_audit
 exact ⟨h1.le, h2.le, h3.le, h4.le, h5.le, h6.le⟩

/-! ## T2.2 — the additive bound (disjoint-support sum), audited -/

/-- **T2.2 (audit).** The mixed character `e = x₁x₂ + x₃` saturates the additive
upper bound: `g = wFit 2 0 + wFit 1 0 = 3 + 1 = 4`. -/
theorem linear_bound_mixed : grade3 mixed = wFit 2 0 + wFit 1 0 := by
 rw [grade3_mixed]; decide

end Roots
