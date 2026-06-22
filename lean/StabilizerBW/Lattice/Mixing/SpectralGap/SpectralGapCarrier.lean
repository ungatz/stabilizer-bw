import Mathlib

/-!
# T4 — The LaRacuente spectral-gap carrier

This file declares the **spectral-gap carrier** for the parity-conditioned
birth–death Markov chain `K_t = #{1's at time t}` studied by LaRacuente.

The numerical content is taken **verbatim** from

> M. LaRacuente, *Noise & 2-Designs Notes (Markov chain analysis)*,
> `refs/laracuente/noise-2designs-markov-chain.tex` (unpublished working note,
> IU CS, 2026), **lines 344–372**:
> the relaxation eigenvalue `λ₁` of the parity-conditioned birth–death chain at
> bipartite transition probability `p` on `n` qudits satisfies
> `λ₁ ≤ 1 - 4(1-p)/n`, derived via a monotone path coupling with contraction
> coefficient `c_k = (4(1-p)n + 4(2p-1)k + 8p-6)/(n(n-1)) ≥ 4(1-p)/n`,
> and (lines 439–465) the sharper linearised relaxation rate `4√(p(1-p))/n`.

We do **not** re-derive this spectral gap (Mathlib has no birth–death-chain
spectral theory at this granularity). Instead we package it as a `Prop` that
constrains an *abstract* separation-distance function `dist : ℕ → ℝ` of the
chain to decay at the LaRacuente spectral rate.  The transport file (T6)
consumes this carrier as a hypothesis; it is therefore a **named, conditional
assumption**, never an axiom.
-/

namespace ParityChainBWGradeMixing.SpectralGapCarrier

open Real

/-- The LaRacuente contraction / spectral-gap rate `4(1-p)/m` (with `m = n` the
number of parity bits), from `noise-2designs-markov-chain.tex` lines 344–372. -/
noncomputable def laracuenteGap (p : ℝ) (m : ℕ) : ℝ := 4 * (1 - p) / (m : ℝ)

/-- LaRacuente's spectral upper-bound **model** for the separation distance of
the parity-conditioned chain after `ℓ` steps: `m · exp(-gap · ℓ)`.

This is the closed-form bound the spectral gap produces (a relaxation
`sep(ℓ) ≤ (1/π_min)·λ₁^ℓ ≤ m·exp(-gap·ℓ)` with `1 - x ≤ e^{-x}`); it is the
concrete witness that realises the abstract carrier below. -/
noncomputable def laracuenteMixingDistance (p : ℝ) (m : ℕ) (ℓ : ℕ) : ℝ :=
  (m : ℝ) * Real.exp (- laracuenteGap p m * (ℓ : ℝ))

/-- **Spectral-gap carrier.**  LaRacuente's spectral gap `λ₁ ≤ 1 - 4(1-p)/m`
(noise-2designs-markov-chain.tex, lines 344–372) implies that the separation
distance `dist ℓ` of the parity-conditioned chain decays at the gap rate:
`dist ℓ ≤ m · exp(-(4(1-p)/m)·ℓ)`.

The carrier is stated about an *abstract* distance `dist`, so it is genuinely
informative (it is **not** definitionally true) and is load-bearing in the
transport theorem. -/
def LaRacuenteSpectralGapBound (p : ℝ) (m : ℕ) (dist : ℕ → ℝ) : Prop :=
  ∀ ℓ : ℕ, dist ℓ ≤ (m : ℝ) * Real.exp (- laracuenteGap p m * (ℓ : ℝ))

/-- Positivity of the gap on the physical parameter range `0 ≤ p < 1`, `1 ≤ m`. -/
theorem laracuenteGap_pos {p : ℝ} {m : ℕ} (hp : p < 1) (hm : 1 ≤ m) :
    0 < laracuenteGap p m := by
  have hpm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  unfold laracuenteGap
  have : 0 < 1 - p := by linarith
  positivity

/-- The concrete LaRacuente model `laracuenteMixingDistance` realises the
spectral-gap carrier (with equality), showing the carrier is satisfiable. -/
theorem laracuenteMixingDistance_spectralGapBound (p : ℝ) (m : ℕ) :
    LaRacuenteSpectralGapBound p m (laracuenteMixingDistance p m) :=
  fun _ => le_of_eq rfl

/-- **Specialisation at symmetric transitions `p = 1/2`.**  The gap becomes
`2/m`, i.e. `λ₁ ≤ 1 - 2/m` (the operationally relevant uniform-sampling case). -/
theorem bwGrade_spectral_gap_at_pHalf (m : ℕ) :
    laracuenteGap (1 / 2) m = 2 / (m : ℝ) := by
  unfold laracuenteGap; ring

end ParityChainBWGradeMixing.SpectralGapCarrier
