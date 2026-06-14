import Mathlib

/-!
# Uniqueness threshold (`prop:uniqueness-threshold`)

We prove the **overlap triangle bound** and deduce that fidelity above `cos(π/8)` forces a
unique maximizing stabilizer ray, given the bridge field that distinct stabilizer rays satisfy
`|⟨S₁|S₂⟩| ≤ 2^{-1/2}`.

* `overlap_triangle_bound` — for unit `S₁, S₂, ψ`:
 `2 |⟨S₁|ψ⟩| |⟨S₂|ψ⟩| − 1 ≤ |⟨S₁|S₂⟩|` (the standard overlap/Fubini–Study triangle bound).
* `two_cos_pi_div_eight_sq_sub_one` — `2 cos²(π/8) − 1 = √2 / 2`.
* `uniqueness_threshold` — if `|⟨S₁|S₂⟩| ≤ √2/2` (bridge field) and both fidelities exceed
 `cos(π/8)`, contradiction; hence at most one ray can exceed `cos(π/8)`.

Here `⟨a|b⟩ := inner ℂ a b` (conjugate-linear in the first slot), so `|⟨S|ψ⟩| = ‖inner ℂ S ψ‖`.
-/

open ComplexConjugate

namespace DecoderUniqueness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-
Squared norm of the residual of `x` after projecting onto a unit vector `ψ`.
-/
theorem proj_residual_norm_sq (psi x : E) (h : ‖psi‖ = 1) :
 ‖x - (inner ℂ psi x) • psi‖ ^ 2 = ‖x‖ ^ 2 - ‖(inner ℂ psi x : ℂ)‖ ^ 2 := by
 rw [ @norm_sub_pow_two ℂ ];
 simp_all +decide [ Cardinal.lift_one, sq, mul_assoc, mul_comm, mul_left_comm, inner_smul_right, norm_smul ];
 simp +decide [ ← sq, Complex.normSq, Complex.sq_norm ];
 rw [ ← inner_conj_symm, Complex.conj_re, Complex.conj_im ] ; ring

/-
The off-diagonal overlap equals the residual inner product:
 `⟨r₁|r₂⟩ = ⟨S₁|S₂⟩ − conj⟨ψ|S₁⟩ ⟨ψ|S₂⟩`.
-/
theorem overlap_residual_eq (psi S₁ S₂ : E) (h : ‖psi‖ = 1) :
 inner ℂ (S₁ - (inner ℂ psi S₁) • psi) (S₂ - (inner ℂ psi S₂) • psi)
 = inner ℂ S₁ S₂ - (starRingEnd ℂ) (inner ℂ psi S₁) * (inner ℂ psi S₂) := by
 simp +decide [ inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, h ];
 ring

/-
Real inequality powering the triangle bound:
 `√(1−a²)·√(1−b²) ≤ 1 − ab` for `0 ≤ a,b ≤ 1`.
-/
theorem sqrt_one_sub_sq_mul_le (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
 (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
 Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) ≤ 1 - a * b := by
 rw [ ← Real.sqrt_mul ( by nlinarith ) ] ; exact Real.sqrt_le_iff.mpr ⟨ by nlinarith, by nlinarith [ sq_nonneg ( a - b ) ] ⟩ ;

/-
**Overlap triangle bound.** For unit vectors `S₁, S₂, ψ`,
 `2 |⟨S₁|ψ⟩| |⟨S₂|ψ⟩| − 1 ≤ |⟨S₁|S₂⟩|`.
-/
theorem overlap_triangle_bound (psi S₁ S₂ : E)
 (hpsi : ‖psi‖ = 1) (hS₁ : ‖S₁‖ = 1) (hS₂ : ‖S₂‖ = 1) :
 2 * ‖(inner ℂ S₁ psi : ℂ)‖ * ‖(inner ℂ S₂ psi : ℂ)‖ - 1
 ≤ ‖(inner ℂ S₁ S₂ : ℂ)‖ := by
 -- By the triangle inequality, we have:
 have h_triangle : ‖inner ℂ S₁ S₂‖ ≥ ‖(inner ℂ S₁ psi) * (inner ℂ S₂ psi)‖ - ‖inner ℂ (S₁ - (inner ℂ psi S₁) • psi) (S₂ - (inner ℂ psi S₂) • psi)‖ := by
 simp_all +decide;
 convert norm_sub_le ( inner ℂ S₁ S₂ ) ( inner ℂ S₁ S₂ - inner ℂ psi S₂ * inner ℂ S₁ psi ) using 1 ; simp +decide;
 grind +suggestions;
 -- By the Cauchy-Schwarz inequality, we have:
 have h_cauchy_schwarz : ‖inner ℂ (S₁ - (inner ℂ psi S₁) • psi) (S₂ - (inner ℂ psi S₂) • psi)‖ ≤ ‖S₁ - (inner ℂ psi S₁) • psi‖ * ‖S₂ - (inner ℂ psi S₂) • psi‖ := by
 exact norm_inner_le_norm _ _;
 -- By the properties of the norm, we have:
 have h_norm : ‖S₁ - (inner ℂ psi S₁) • psi‖ = Real.sqrt (1 - ‖inner ℂ psi S₁‖^2) ∧ ‖S₂ - (inner ℂ psi S₂) • psi‖ = Real.sqrt (1 - ‖inner ℂ psi S₂‖^2) := by
 constructor <;> rw [ ← Real.sqrt_sq ( norm_nonneg _ ) ]; all_goals rw [ proj_residual_norm_sq ] <;> aesop;
 -- By the properties of the norm, we have ‖inner ℂ psi S₁‖ = ‖inner ℂ S₁ psi‖ and ‖inner ℂ psi S₂‖ = ‖inner ℂ S₂ psi‖.
 have h_norm_eq : ‖inner ℂ psi S₁‖ = ‖inner ℂ S₁ psi‖ ∧ ‖inner ℂ psi S₂‖ = ‖inner ℂ S₂ psi‖ := by
 exact ⟨ by rw [ ← inner_conj_symm, RCLike.norm_conj ], by rw [ ← inner_conj_symm, RCLike.norm_conj ] ⟩;
 simp_all +decide;
 linarith [ sqrt_one_sub_sq_mul_le ‖inner ℂ S₁ psi‖ ‖inner ℂ S₂ psi‖ ( norm_nonneg _ ) ( by simpa [ hS₁, hpsi ] using norm_inner_le_norm S₁ psi ) ( norm_nonneg _ ) ( by simpa [ hS₂, hpsi ] using norm_inner_le_norm S₂ psi ) ]

/-
`2 cos²(π/8) − 1 = √2 / 2` (the half-angle identity that pins the threshold).
-/
theorem two_cos_pi_div_eight_sq_sub_one :
 2 * Real.cos (Real.pi / 8) ^ 2 - 1 = Real.sqrt 2 / 2 := by
 rw [ Real.cos_sq ] ; ring_nf ; norm_num [ mul_div ] ;

/-
**Uniqueness threshold.** Given the bridge field `|⟨S₁|S₂⟩| ≤ √2/2` for distinct
 stabilizer rays, two rays cannot both have fidelity exceeding `cos(π/8)`.
-/
theorem uniqueness_threshold (psi S₁ S₂ : E)
 (hpsi : ‖psi‖ = 1) (hS₁ : ‖S₁‖ = 1) (hS₂ : ‖S₂‖ = 1)
 (hbridge : ‖(inner ℂ S₁ S₂ : ℂ)‖ ≤ Real.sqrt 2 / 2)
 (ha : Real.cos (Real.pi / 8) < ‖(inner ℂ S₁ psi : ℂ)‖)
 (hb : Real.cos (Real.pi / 8) < ‖(inner ℂ S₂ psi : ℂ)‖) :
 False := by
 contrapose! hbridge;
 refine' lt_of_lt_of_le _ ( overlap_triangle_bound psi S₁ S₂ hpsi hS₁ hS₂ );
 nlinarith [ show 0 < Real.cos ( Real.pi / 8 ) from Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩, two_cos_pi_div_eight_sq_sub_one, mul_lt_mul'' ha hb ( by exact Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ) ( by exact Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ) ]

end DecoderUniqueness