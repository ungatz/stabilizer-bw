import Mathlib
import StabilizerBW.DecoderThreshold

/-!
# Target 4 — logical decoding via the similarity reduction (`cor:logical-decoding`)

The constraint sublattice of the logical stabilizer `⟨Z₁ … Z_m⟩` is, by the iterated pinned
theorem `BWArith.pinned_iter` (already kernel-checked in `BWFreeModule.lean`),

  `BW_{k+m}^{⟨pin⟩} = (1+i)^m · |0^m⟩ ⊗ BW_k`,

an isometrically `(1+i)^m`-scaled copy of `BW_k`.  Multiplication by `(1+i)^m` is a
**similarity**: it scales every norm by `‖(1+i)^m‖ = 2^{m/2}` and therefore commutes with
`argmin`.  Hence the closest-point problem on the sublattice reduces to the inner lattice's
problem.  This file proves that reduction abstractly:

* `norm_smul_sub` — scaling scales distances: `‖c•x − c•y‖ = ‖c‖ ‖x−y‖`.
* `smul_lattice_min` — a scaled lattice has minimal distance `‖c‖·dmin`.
* `closest_smul` — the closest-point map is **similarity-equivariant**: if `z` is the unique
  in-radius lattice point of `s`, then `c•z` is the unique in-radius point of `c•s` in `c•L`.

Connection to the Barnes–Wall project (both already kernel-checked, zero `sorry`):
* the lattice identity is `BWArith.pinned_iter`;
* the Bell-code instance `m = n = 2` is `BWArith.bell_theory` / `BWArith.bell_minimal_iff`.
Together with `closest_smul` (the similarity step) these give logical decoding.
-/

namespace DecoderLogical

open scoped Real

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Scaling by a scalar scales distances by its norm. -/
theorem norm_smul_sub (c : ℂ) (x y : F) : ‖c • x - c • y‖ = ‖c‖ * ‖x - y‖ := by
  rw [← smul_sub, norm_smul]

/-- A `c`-scaled lattice has minimal distance `‖c‖ · dmin`. -/
theorem smul_lattice_min (c : ℂ) {L : Set F} {dmin : ℝ}
    (hmin : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → dmin ≤ ‖x - y‖) :
    ∀ x ∈ (c • ·) '' L, ∀ y ∈ (c • ·) '' L, x ≠ y → ‖c‖ * dmin ≤ ‖x - y‖ := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
  have hxy : x ≠ y := fun h => hne (by rw [h])
  rw [norm_smul_sub]
  exact mul_le_mul_of_nonneg_left (hmin x hx y hy hxy) (norm_nonneg c)

/-- **Similarity-equivariance of closest-point decoding.**  If `z` is the (unique) lattice
    point within `dmin/2` of the target `s`, then `c • z` (`c ≠ 0`) is the unique point of the
    scaled lattice `c • L` within `‖c‖·dmin/2` of the scaled target `c • s`.  This is the
    reduction that turns the logical (sublattice) closest-point problem into the inner one. -/
theorem closest_smul (c : ℂ) (hc : c ≠ 0) {L : Set F} {dmin : ℝ}
    (hmin : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → dmin ≤ ‖x - y‖)
    {s z : F} (hz : z ∈ L) (hclose : ‖s - z‖ < dmin / 2) :
    c • z ∈ (c • ·) '' L
      ∧ ‖c • s - c • z‖ < ‖c‖ * dmin / 2
      ∧ ∀ w ∈ (c • ·) '' L, ‖c • s - w‖ < ‖c‖ * dmin / 2 → w = c • z := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  refine ⟨⟨z, hz, rfl⟩, ?_, ?_⟩
  · rw [norm_smul_sub]
    have : ‖c‖ * ‖s - z‖ < ‖c‖ * (dmin / 2) := by
      exact mul_lt_mul_of_pos_left hclose hcpos
    rw [mul_div_assoc]
    linarith
  · rintro _ ⟨w, hw, rfl⟩ hwclose
    -- pull the scaling out of `hwclose`, reduce to the inner in-radius uniqueness
    rw [norm_smul_sub] at hwclose
    have hwclose' : ‖s - w‖ < dmin / 2 := by
      rw [mul_div_assoc] at hwclose
      exact lt_of_mul_lt_mul_left (by linarith) (norm_nonneg c)
    have : w = z := DecoderThreshold.inradius_unique hmin hw hz hwclose' hclose
    rw [this]

end DecoderLogical
