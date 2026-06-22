import StabilizerBW.SubsetParityBWBridge.Distribution
import StabilizerBW.SubsetParityBWBridge.SymmetricEquilibrium
import StabilizerBW.SubsetParityBWBridge.GradeIsParityCount

/-!
# SubsetParityBWBridge — T8: the bridge theorem

The Barnes–Wall linear-stratum grade enumerator is the parity-count marginal of
the symmetric Ehrenfest urn equilibrium.

* `grade_distribution_eq_symmetric_equilibrium_marginal` is the headline,
  *conditional on the named carrier* `SymmetricEquilibriumMarginal`:
  the normalised operator-side grade distribution equals the measurement-side
  the symmetric Ehrenfest urn parity-count marginal.
* `grade_distribution_eq_symmetric_equilibrium_marginal_unconditional` is the
  same identity with the carrier discharged via `symmetric_chain_carrier`.
* `walshHadamard_grade_inversion` is the secondary outcome: the Walsh–Hadamard
  (sign-character) inversion of the grade as a function of the parity tag,
  exhibiting the shared powerset-lattice Fourier structure.

**Circularity check (structural).** The carrier
`SymmetricEquilibriumMarginal m` is a statement about
`symmetricEquilibriumMarginal` (the measurement-side equilibrium probabilities); the
headline is a statement about `#{P | gradeOf P = k}` (the operator-side BW grade
counts).  The headline's proof uses *both* the operator-side closed form
`grade_distribution_BW` *and* the carrier `h`.  Substituting the headline
for the carrier does not typecheck — the BW side is independent — so the carrier
is not a restatement of the headline.
-/

namespace SubsetParityBWBridge.Bridge

open Finset SubsetParityBWBridge.TauMap SubsetParityBWBridge.SymmetricEquilibrium
open SubsetParityBWBridge.GradeIsParityCount

/-- **T8 headline (conditional on the named carrier).** The normalised
Barnes–Wall grade distribution on the linear stratum equals the the symmetric Ehrenfest urn
symmetric-transition equilibrium parity-count marginal. -/
theorem grade_distribution_eq_symmetric_equilibrium_marginal {m : ℕ}
    (h : SymmetricEquilibriumMarginal m) (k : ℕ) (hk : k ≤ m) :
    ((Finset.univ.filter (fun P : ReedMuller.LinPhase m => ReedMuller.gradeOf P = k)).card : ℚ) / 8 ^ (m + 1)
      = symmetricEquilibriumMarginal m k := by
  rw [SubsetParityBWBridge.Distribution.grade_distribution_BW k hk, h k hk]

/-- The bridge identity with the carrier discharged. -/
theorem grade_distribution_eq_symmetric_equilibrium_marginal_unconditional {m : ℕ}
    (k : ℕ) (hk : k ≤ m) :
    ((Finset.univ.filter (fun P : ReedMuller.LinPhase m => ReedMuller.gradeOf P = k)).card : ℚ) / 8 ^ (m + 1)
      = symmetricEquilibriumMarginal m k :=
  grade_distribution_eq_symmetric_equilibrium_marginal (symmetric_chain_carrier m) k hk

/-- **Secondary outcome.** Walsh–Hadamard (sign-character) inversion of the
Barnes–Wall grade as a function of the parity tag `τ P`:
`gradeOf P = (m − Σ_i (−1)^{τ(P)_i}) / 2`.  This exhibits the grade as the
zero-frequency-shifted Walsh transform of its parity tag — the same
powerset-lattice Fourier structure used on the symmetric chain's state-distribution
side. -/
theorem walshHadamard_grade_inversion {m : ℕ} (P : ReedMuller.LinPhase m) :
    (ReedMuller.gradeOf P : ℚ) = ((m : ℚ) - ∑ i, (-1 : ℚ) ^ (tau P i).toNat) / 2 := by
  rw [gradeOf_eq_tau_countOnes P]
  rw [eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)]
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_mul, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  rw [show (m : ℚ) = ∑ _i : Fin m, (1 : ℚ) by simp]
  apply Finset.sum_congr rfl
  intro i _
  rcases h : tau P i <;> norm_num [h]

end SubsetParityBWBridge.Bridge
