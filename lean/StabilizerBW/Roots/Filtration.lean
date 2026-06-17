import StabilizerBW.Roots.Grades

/-!
# The grade is a filtration (Priority 2, single-qubit / integral case)

We prove the multiplicativity law of the grade for integral operators on `L₃`:

* **(a)** `g(M·N) ≤ g(M) + g(N)` (`grade_mul`),

together with the algebraic backbone for the remaining parts:

* every integral operator has finite grade (`gradeLE_top : gradeLE M 4`), because
 `(2) = (λ)⁴` and `(1+i) ∣ λ⁴`;
* the Hermitian form `h((a,b),(c,d)) = a·conj(c) + b·conj(d)` and the matrix adjoint
 `M†` (conjugate transpose), with the adjunction `h(M·v, w) = h(v, M†·w)`;
* `IsIsometry` of the named generators (`X`, `S`, `T`, the four roots).

The general-`n` statements (b) tensor sub-additivity and (c) `g = 0 ⟺ Aut` require the
`BW_n` tower; see `Proofs/ArithmeticOfRoots.md` for the status of those.
-/

set_option maxHeartbeats 1000000

namespace Roots
open Z8 Mat2

/-! ## Composition of actions -/

/-- The action of a product is the composite of actions. -/
theorem mulVec_mul (M N : Mat2) (v : Z8 × Z8) :
 (M * N).mulVec v = M.mulVec (N.mulVec v) := by
 have h1 : ((M * N).mulVec v).1 = (M.mulVec (N.mulVec v)).1 := by
 simp only [mulVec_fst, mulVec_snd, mul_m00, mul_m01]; ring
 have h2 : ((M * N).mulVec v).2 = (M.mulVec (N.mulVec v)).2 := by
 simp only [mulVec_fst, mulVec_snd, mul_m10, mul_m11]; ring
 exact Prod.ext h1 h2

/-! ## Every integral operator has finite grade -/

/-- `(1+i) ∣ λ⁴ = ⟨0,-4,6,-4⟩`, since `λ² = (1+i)·u`. -/
theorem oneI_dvd_lam_pow_four : Z8.oneI ∣ Z8.lam ^ 4 :=
 ⟨⟨3, -4, 3, 0⟩, by decide⟩

/-- `λ⁴·M` always preserves `L₃` (indeed `λ⁴·(anything) ∈ L₃`), so every integral
operator has grade `≤ 4`. -/
theorem gradeLE_top (M : Mat2) : gradeLE M 4 := by
 intro v _
 rw [smul_mulVec, inL]
 simp only [vsmul_fst, vsmul_snd]
 have : Z8.lam ^ 4 * (M.mulVec v).1 + Z8.lam ^ 4 * (M.mulVec v).2
 = Z8.lam ^ 4 * ((M.mulVec v).1 + (M.mulVec v).2) := by ring
 rw [this]
 exact Dvd.dvd.mul_right oneI_dvd_lam_pow_four _

theorem gradeLE_nonempty (M : Mat2) : (∃ k, gradeLE M k) := ⟨4, gradeLE_top M⟩

theorem gradeLE_grade (M : Mat2) : gradeLE M (grade M) :=
 Nat.sInf_mem (gradeLE_nonempty M)

/-! ## Priority 2(a): sub-multiplicativity of the grade -/

/-- If `λ^j·M` and `λ^k·N` preserve `L₃`, then `λ^{j+k}·(M·N)` does. -/
theorem gradeLE_mul {M N : Mat2} {j k : ℕ} (hM : gradeLE M j) (hN : gradeLE N k) :
 gradeLE (M * N) (j + k) := by
 intro v hv
 have hw : inL (vsmul (Z8.lam ^ k) (N.mulVec v)) := by
 have := hN v hv; rwa [smul_mulVec] at this
 have key : (Mat2.smul (Z8.lam ^ (j + k)) (M * N)).mulVec v
 = (Mat2.smul (Z8.lam ^ j) M).mulVec (vsmul (Z8.lam ^ k) (N.mulVec v)) := by
 rw [smul_mulVec, smul_mulVec, mulVec_vsmul, mulVec_mul, pow_add]
 simp only [vsmul]
 exact Prod.ext (by ring) (by ring)
 rw [key]
 exact hM _ hw

/-- **Priority 2(a): `g(M·N) ≤ g(M) + g(N)`.** -/
theorem grade_mul (M N : Mat2) : grade (M * N) ≤ grade M + grade N :=
 grade_le (gradeLE_mul (gradeLE_grade M) (gradeLE_grade N))

/-! ## The Hermitian form and the adjoint -/

/-- Hermitian inner product `h((a,b),(c,d)) = a·conj(c) + b·conj(d)`. -/
def herm (v w : Z8 × Z8) : Z8 := v.1 * Z8.conj w.1 + v.2 * Z8.conj w.2

/-- Conjugate transpose (adjoint) of a `2×2` matrix. -/
def Mat2.adj (M : Mat2) : Mat2 :=
 ⟨Z8.conj M.m00, Z8.conj M.m10, Z8.conj M.m01, Z8.conj M.m11⟩

/-- Adjunction: `h(M·v, w) = h(v, M†·w)`. -/
theorem herm_adj (M : Mat2) (v w : Z8 × Z8) :
 herm (M.mulVec v) w = herm v (M.adj.mulVec w) := by
 simp only [herm, Mat2.mulVec, Mat2.adj]
 rw [Z8.conj_add, Z8.conj_add, Z8.conj_mul, Z8.conj_mul, Z8.conj_mul, Z8.conj_mul,
 Z8.conj_conj, Z8.conj_conj, Z8.conj_conj, Z8.conj_conj]
 ring

/-- `adj` is an involution. -/
@[simp] theorem Mat2.adj_adj (M : Mat2) : M.adj.adj = M := by
 cases M; simp [Mat2.adj]

/-! ## Isometries of the form (Priority 2(c)/(d) backbone) -/

/-- An operator is an isometry of `h` when `M† · M = I`. -/
def IsIsometry (M : Mat2) : Prop := M.adj * M = II

/-- `X` is an isometry. -/
theorem X_isometry : IsIsometry X := by unfold IsIsometry; decide
/-- `S` is an isometry. -/
theorem S_isometry : IsIsometry S := by unfold IsIsometry; decide
/-- `T` is an isometry. -/
theorem T_isometry : IsIsometry T := by unfold IsIsometry; decide

/-- For the doubled roots, `(2R)† · (2R) = 4I`, i.e. each `R` is unitary. -/
theorem twoR1_isometry : twoR1.adj * twoR1 = Mat2.smul 4 II := by decide
theorem twoR2_isometry : twoR2.adj * twoR2 = Mat2.smul 4 II := by decide
theorem twoR3_isometry : twoR3.adj * twoR3 = Mat2.smul 4 II := by decide
theorem twoR4_isometry : twoR4.adj * twoR4 = Mat2.smul 4 II := by decide

end Roots
