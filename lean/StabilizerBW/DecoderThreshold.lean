import Mathlib

/-!
# Targets 2 & 3 (abstract core) — BDD promise logic, in-radius uniqueness,
# the misalignment bound, and equivariance.

We model the bounded-distance decoder (Micciancio–Nicolosi) as an *abstract interface* over a
lattice `L` in a normed space `E`, with minimal distance `dmin`.  We do **not** formalize the
MN08 algorithm; we formalize the promise logic around it:

* `inradius_unique` — two lattice points within `dmin/2` of one target coincide
  (this is the uniqueness part of the BDD contract; it follows from the minimal distance).
* `dec_eq_of_close` — under the BDD contract a decoder returns the (unique) in-radius point.
* `misalignment_cos_bound` / `misalignment_bound` — the phase-grid misalignment estimate
  `cos δ ≥ (7/8)/(7/8+η)` for `δ ≤ π/(4G)` and `G ≥ (π/4)/√(2η/F)`.
* `equivariance` — for a linear isometry `U` preserving `L`, the closest-point map commutes
  with `U`:  `dec (U s) = U (dec s)` (Theorem `thm:equivariant-decoding`).

The Barnes–Wall instance has `dmin = 2^{n/2}` (`d²_min = 2^n`), so the BDD in-radius
`‖s − z‖² < 2^n/4` is exactly `‖s − z‖ < dmin/2`.
-/

namespace DecoderThreshold

open scoped Real

/-! ## In-radius uniqueness -/

variable {E : Type*} [NormedAddCommGroup E]

/-- **In-radius uniqueness.** If two lattice points `z₁, z₂` are each strictly within `dmin/2`
    of a target `s`, and any two distinct lattice points are at distance `≥ dmin`, then
    `z₁ = z₂`.  (This is the uniqueness clause of the BDD contract; `d²_min = 2^n` ⇒
    `dmin = 2^{n/2}`.) -/
theorem inradius_unique {L : Set E} {dmin : ℝ}
    (hmin : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → dmin ≤ ‖x - y‖)
    {s z₁ z₂ : E} (hz₁ : z₁ ∈ L) (hz₂ : z₂ ∈ L)
    (h₁ : ‖s - z₁‖ < dmin / 2) (h₂ : ‖s - z₂‖ < dmin / 2) :
    z₁ = z₂ := by
  by_contra hne
  have hd : dmin ≤ ‖z₁ - z₂‖ := hmin z₁ hz₁ z₂ hz₂ hne
  have htri : ‖z₁ - z₂‖ ≤ ‖z₁ - s‖ + ‖s - z₂‖ := by
    simpa using norm_sub_le_norm_sub_add_norm_sub z₁ s z₂
  rw [norm_sub_rev z₁ s] at htri
  have : ‖z₁ - z₂‖ < dmin := by
    have := add_lt_add h₁ h₂
    linarith
  linarith

/-- **Decoder correctness under the BDD contract.** A decoder `dec` satisfying the contract
    "every lattice point within `dmin/2` of `s` is returned" outputs the unique in-radius
    point when one exists. -/
theorem dec_eq_of_close {L : Set E} {dmin : ℝ} {dec : E → E}
    (contract : ∀ s z, z ∈ L → ‖s - z‖ < dmin / 2 → dec s = z)
    {s z : E} (hz : z ∈ L) (hclose : ‖s - z‖ < dmin / 2) :
    dec s = z :=
  contract s z hz hclose

/-! ## Equivariance (Theorem `thm:equivariant-decoding`) -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Equivariance = naturality.** For a linear isometry `U` preserving the lattice `L`, the
    BDD closest-point map commutes with `U`:  `dec (U s) = U (dec s)`.  Proof = in-radius
    uniqueness + isometry. -/
theorem equivariance {L : Set F} {dmin : ℝ} {dec : F → F}
    (contract : ∀ s z, z ∈ L → ‖s - z‖ < dmin / 2 → dec s = z)
    (U : F ≃ₗᵢ[ℂ] F) (hUL : ∀ x, U x ∈ L ↔ x ∈ L)
    {s z : F} (hz : z ∈ L) (hclose : ‖s - z‖ < dmin / 2) :
    dec (U s) = U (dec s) := by
  have hdec_s : dec s = z := contract s z hz hclose
  have hUz : U z ∈ L := (hUL z).mpr hz
  have hclose' : ‖U s - U z‖ < dmin / 2 := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    exact hclose
  have hdec_Us : dec (U s) = U z := contract (U s) (U z) hUz hclose'
  rw [hdec_Us, hdec_s]

/-! ## The misalignment bound -/

/-- **Misalignment cosine bound (core).** If `F = 7/8 + η` with `η > 0`, then a phase error
    `δ` with `δ² ≤ 2η/F` keeps the cosine above the threshold `(7/8)/F`. -/
theorem misalignment_cos_bound {Fid η δ : ℝ} (hF : Fid = 7/8 + η) (hη : 0 < η)
    (hδ : δ ^ 2 ≤ 2 * η / Fid) :
    (7/8) / Fid ≤ Real.cos δ := by
  have hFpos : 0 < Fid := by rw [hF]; linarith
  have hcos : 1 - δ ^ 2 / 2 ≤ Real.cos δ := Real.one_sub_sq_div_two_le_cos
  have h2 : δ ^ 2 * Fid ≤ 2 * η := (le_div_iff₀ hFpos).mp hδ
  have hstep : (7/8) / Fid ≤ 1 - δ ^ 2 / 2 := by
    rw [div_le_iff₀ hFpos]
    nlinarith [h2, hF, hFpos]
  linarith

/-- **Misalignment bound (grid form).** With grid size `G ≥ (π/4)/√(2η/F)` and a phase error
    `δ ≤ π/(4G)`, the cosine stays above the threshold `(7/8)/F`. -/
theorem misalignment_bound {Fid η δ G : ℝ} (hF : Fid = 7/8 + η) (hη : 0 < η)
    (hG : (Real.pi / 4) / Real.sqrt (2 * η / Fid) ≤ G)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / (4 * G)) :
    (7/8) / Fid ≤ Real.cos δ := by
  have hFpos : 0 < Fid := by rw [hF]; linarith
  have hrpos : 0 < 2 * η / Fid := by positivity
  have hsqrt : 0 < Real.sqrt (2 * η / Fid) := Real.sqrt_pos.mpr hrpos
  have hGpos : 0 < G := lt_of_lt_of_le (by positivity) hG
  -- π/(4G) ≤ √(2η/F)
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hstep : Real.pi / (4 * G) ≤ Real.sqrt (2 * η / Fid) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * G)]
    rw [div_le_iff₀ hsqrt] at hG
    nlinarith [hG, hsqrt, hGpos, Real.sqrt_nonneg (2 * η / Fid)]
  have hδbound : δ ≤ Real.sqrt (2 * η / Fid) := le_trans hδ hstep
  have hsq : (Real.sqrt (2 * η / Fid)) ^ 2 = 2 * η / Fid := Real.sq_sqrt hrpos.le
  have hδsq : δ ^ 2 ≤ 2 * η / Fid := by
    nlinarith [hδbound, hδ0, hsq, Real.sqrt_nonneg (2 * η / Fid)]
  exact misalignment_cos_bound hF hη hδsq

end DecoderThreshold
