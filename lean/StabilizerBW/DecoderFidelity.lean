import Mathlib

/-!
# Target 1 — the fidelity–distance dictionary (`lem:fidelity-distance`)

For a unit vector `ψ`, a phase `θ`, the "lifted target" `t_θ = e^{iθ} 2^{n/2} ψ`, a unit
stabilizer state `S`, and its lattice representatives `v_k = i^k (1+i)^n S` (`k ∈ ℤ₄`):

* `dist_sq_eq` : `‖t_θ − v_k‖² = 2^{n+1} (1 − Re( (-i)^k e^{i(θ−πn/4)} ⟨S|ψ⟩ ))`,
* `dist_sq_ge` : the global lower bound `‖t_θ − v_k‖² ≥ 2^{n+1}(1 − |⟨S|ψ⟩|)`,
* `exists_dist_sq_eq_inf` : the bound is attained, so
 `inf_θ min_k ‖t_θ − v_k‖² = 2^{n+1}(1 − |⟨S|ψ⟩|)`.

This is pure inner-product algebra over `ℂ`. We work in an arbitrary complex inner-product
space `E` (in particular `EuclideanSpace ℂ (Fin (2^n))`), with `⟨S|ψ⟩` the physics inner
product `inner ℂ S ψ` (conjugate-linear in `S`).
-/

open ComplexConjugate Complex

namespace DecoderFidelity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The lifted target vector `t_θ = e^{iθ} · 2^{n/2} · ψ`. -/
noncomputable def tvec (n : ℕ) (psi : E) (θ : ℝ) : E :=
 (((Real.sqrt 2 ^ n : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) • psi

/-- The lattice representative `v_k = i^k (1+i)^n · S`. -/
noncomputable def vvec (n : ℕ) (S : E) (k : ℕ) : E :=
 (Complex.I ^ k * (1 + Complex.I) ^ n) • S

/-
Polar form of `(1+i)^n`: `(1+i)^n = 2^{n/2} · e^{iπn/4}`.
-/
theorem oneI_pow_polar (n : ℕ) :
 (1 + Complex.I) ^ n
 = ((Real.sqrt 2 ^ n : ℝ) : ℂ) * Complex.exp (((Real.pi : ℂ) * n / 4) * Complex.I) := by
 rw [ show ( 1 + Complex.I ) = Real.sqrt 2 * Complex.exp ( Real.pi / 4 * Complex.I ) by rw [ Complex.ext_iff ] ; norm_num [ Complex.exp_re, Complex.exp_im, Real.sqrt_div_self' ] ] ; rw [ mul_pow ] ; ring;
 rw [ ← Complex.exp_nat_mul ] ; push_cast ; ring

/-
The modulus `|（1 + i)^n| = 2^{n/2}`.
-/
theorem abs_oneI_pow (n : ℕ) : ‖(1 + Complex.I) ^ n‖ = Real.sqrt 2 ^ n := by
 norm_num [ ← sq, Complex.norm_def, Complex.normSq ]

/-
**Core fidelity–distance identity** (per `k`, per `θ`).
-/
theorem dist_sq_eq (n : ℕ) (psi S : E) (hpsi : ‖psi‖ = 1) (hS : ‖S‖ = 1)
 (θ : ℝ) (k : ℕ) :
 ‖tvec n psi θ - vvec n S k‖ ^ 2
 = 2 ^ (n + 1)
 * (1 - (((-Complex.I) ^ k
 * Complex.exp (((θ : ℂ) - (Real.pi : ℂ) * n / 4) * Complex.I)
 * inner ℂ S psi)).re) := by
 have h_norm_sq : ‖tvec n psi θ - vvec n S k‖ ^ 2 = ‖tvec n psi θ‖ ^ 2 + ‖vvec n S k‖ ^ 2 - 2 * (starRingEnd ℂ (inner ℂ (tvec n psi θ) (vvec n S k))).re := by
 rw [ @norm_sub_sq ℂ ] ; norm_num ; ring;
 rw [ ← inner_conj_symm, Complex.conj_re ] ; ring;
 have h_norm_tvec : ‖tvec n psi θ‖ ^ 2 = 2 ^ n := by
 simp +decide [ tvec, norm_smul, hpsi ];
 rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ), pow_right_comm, Real.sq_sqrt ( by norm_num ) ]
 have h_norm_vvec : ‖vvec n S k‖ ^ 2 = 2 ^ n := by
 unfold vvec; simp +decide [ *, norm_smul ] ; ring;
 norm_num [ pow_mul', Complex.normSq, Complex.norm_def ]
 have h_inner : starRingEnd ℂ (inner ℂ (tvec n psi θ) (vvec n S k)) = 2 ^ n * (-Complex.I) ^ k * Complex.exp ((θ - Real.pi * n / 4) * Complex.I) * inner ℂ S psi := by
 unfold tvec vvec; simp +decide [ inner_smul_left, inner_smul_right ] ; ring;
 rw [ show ( 1 - Complex.I ) = ( Real.sqrt 2 : ℂ ) * Complex.exp ( - ( Real.pi / 4 ) * Complex.I ) by rw [ Complex.ext_iff ] ; norm_num [ Complex.exp_re, Complex.exp_im, neg_div ] ; ring_nf ; norm_num [ mul_div, Real.sqrt_div_self ] ] ; rw [ mul_pow, ← Complex.exp_nat_mul ] ; ring; norm_num [ Complex.exp_re, Complex.exp_im, mul_div ] ; ring;
 norm_cast ; norm_num [ pow_mul', ← mul_pow ] ; ring;
 rw [ Complex.exp_add ] ; ring;
 simp_all +decide [ pow_succ' ] ; ring;
 norm_cast ; norm_num ; ring

/-
**Global lower bound**: every lattice representative is at squared distance
 at least `2^{n+1}(1 − |⟨S|ψ⟩|)` from every lifted target.
-/
theorem dist_sq_ge (n : ℕ) (psi S : E) (hpsi : ‖psi‖ = 1) (hS : ‖S‖ = 1)
 (θ : ℝ) (k : ℕ) :
 2 ^ (n + 1) * (1 - ‖(inner ℂ S psi : ℂ)‖)
 ≤ ‖tvec n psi θ - vvec n S k‖ ^ 2 := by
 rw [ dist_sq_eq n psi S hpsi hS θ k ];
 gcongr;
 exact le_trans ( Complex.re_le_norm _ ) ( by simp +decide [ Complex.norm_exp, norm_mul ] )

/-
**Attainment**: the global lower bound is achieved for a suitable phase and `k = 0`,
 hence `inf_θ min_k ‖t_θ − v_k‖² = 2^{n+1}(1 − |⟨S|ψ⟩|)`.
-/
theorem exists_dist_sq_eq_inf (n : ℕ) (psi S : E) (hpsi : ‖psi‖ = 1) (hS : ‖S‖ = 1) :
 ∃ θ : ℝ, ∃ k : ℕ,
 ‖tvec n psi θ - vvec n S k‖ ^ 2
 = 2 ^ (n + 1) * (1 - ‖(inner ℂ S psi : ℂ)‖) := by
 refine' ⟨ Real.pi * n / 4 - Complex.arg ( inner ℂ S psi ), 0, _ ⟩;
 -- Substitute θ = Real.pi * n / 4 - (inner ℂ S psi).arg and k = 0 into the distance formula.
 rw [dist_sq_eq n psi S hpsi hS];
 norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
 rw [ ← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg ] ; ring;
 rw [ Real.sin_sq, Real.cos_sq ] ; ring

end DecoderFidelity