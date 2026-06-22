import Mathlib

/-!
# n = 1 universality (`prop:n1-universality`)

Every single-qubit unit vector `ψ = (ψ₀, ψ₁)` has a stabilizer ray with squared overlap at
least `(1 + 1/√3)/2`, the magic-state value `F(T)²`; in particular `> (7/8)²`.  Writing the
six single-qubit stabilizer overlaps explicitly, this is the closed quadratic optimization

  `max(|ψ₀|², |ψ₁|², |ψ₀+ψ₁|²/2, |ψ₀−ψ₁|²/2, |ψ₀−iψ₁|²/2, |ψ₀+iψ₁|²/2) ≥ (1+1/√3)/2`.

The Bloch identity makes the six values `(1±A)/2, (1±B)/2, (1±C)/2` with `A²+B²+C² = 1`, so
one of `|A|,|B|,|C|` is `≥ 1/√3`.
-/

open Complex

namespace DecoderN1

/-- `(1/√3)² = 1/3`. -/
theorem one_div_sqrt_three_sq : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)]

/-
The Bloch sum-of-squares identity: with `A = |ψ₀|²−|ψ₁|²`, `B = 2 Re(conj ψ₀ ψ₁)`,
    `C = 2 Im(conj ψ₀ ψ₁)`, one has `A² + B² + C² = (|ψ₀|²+|ψ₁|²)²`.
-/
theorem bloch_identity (ψ₀ ψ₁ : ℂ) :
    (‖ψ₀‖ ^ 2 - ‖ψ₁‖ ^ 2) ^ 2
      + (2 * ((starRingEnd ℂ) ψ₀ * ψ₁).re) ^ 2
      + (2 * ((starRingEnd ℂ) ψ₀ * ψ₁).im) ^ 2
      = (‖ψ₀‖ ^ 2 + ‖ψ₁‖ ^ 2) ^ 2 := by
  norm_num [ Complex.normSq, Complex.sq_norm ] ; ring;

/-
**n = 1 universality.** Every single-qubit unit vector has a stabilizer ray with squared
    overlap `≥ (1 + 1/√3)/2`.
-/
theorem n1_universality (ψ₀ ψ₁ : ℂ) (h : ‖ψ₀‖ ^ 2 + ‖ψ₁‖ ^ 2 = 1) :
    (1 + 1 / Real.sqrt 3) / 2
      ≤ max (‖ψ₀‖ ^ 2)
          (max (‖ψ₁‖ ^ 2)
            (max (‖ψ₀ + ψ₁‖ ^ 2 / 2)
              (max (‖ψ₀ - ψ₁‖ ^ 2 / 2)
                (max (‖ψ₀ - Complex.I * ψ₁‖ ^ 2 / 2)
                     (‖ψ₀ + Complex.I * ψ₁‖ ^ 2 / 2))))) := by
  -- Set s := Real.sqrt 3 (s > 0, s^2 = 3 so 1/s^2 = 1/3 by one_div_sqrt_three_sq).
  set s : ℝ := Real.sqrt 3
  have hs_pos : 0 < s := by
    positivity
  have hs_sq : s^2 = 3 := by
    exact Real.sq_sqrt <| by norm_num;
  have hs_inv_sq : (1 / s)^2 = 1 / 3 := by
    rw [ one_div_pow, hs_sq ]
  have hs_bound : (1 + 1 / s) / 2 = (1 + 1 / Real.sqrt 3) / 2 := by
    rfl;
  -- By max_lt_iff, if all components of M are < bound, then M < bound.
  by_contra h_contra
  have hM_lt_bound : max (‖ψ₀‖ ^ 2) (max (‖ψ₁‖ ^ 2) (max (‖ψ₀ + ψ₁‖ ^ 2 / 2) (max (‖ψ₀ - ψ₁‖ ^ 2 / 2) (max (‖ψ₀ - I * ψ₁‖ ^ 2 / 2) (‖ψ₀ + I * ψ₁‖ ^ 2 / 2))))) < (1 + 1 / s) / 2 := by
    exact lt_of_not_ge h_contra
  simp_all +decide;
  norm_num [ Complex.normSq, Complex.sq_norm ] at *;
  ring_nf at *;
  nlinarith [ inv_pos.mpr ( Real.sqrt_pos.mpr zero_lt_three ), mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_three ) ), Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three, inv_pow ( Real.sqrt 3 ) 2 ]

/-
The threshold `(1+1/√3)/2` strictly exceeds `(7/8)²`, so n = 1 universality clears the
    BDD threshold.
-/
theorem n1_threshold_gt : (7 / 8 : ℝ) ^ 2 < (1 + 1 / Real.sqrt 3) / 2 := by
  nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt <| show 0 ≤ 3 by norm_num, one_div_mul_cancel <| ne_of_gt <| Real.sqrt_pos.2 <| show 0 < 3 by norm_num ]

end DecoderN1