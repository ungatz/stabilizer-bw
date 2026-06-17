import StabilizerBW.DecoderFidelity
import StabilizerBW.DecoderThreshold
import StabilizerBW.DecoderUniqueness
import StabilizerBW.DecoderN1
import StabilizerBW.DecoderLogical

/-!
# Decoding theorems for stabilizer geometry — aggregator and axiom audit

This module gathers the six decoder targets used in the narrative,
built on the existing Barnes–Wall project (`BarnesWall.lean`, `BWFreeModule.lean`).

* **Target 1** (fidelity–distance dictionary): `DecoderFidelity.dist_sq_eq`,
 `DecoderFidelity.dist_sq_ge`, `DecoderFidelity.exists_dist_sq_eq_inf`.
* **Target 2** (BDD threshold logic): `DecoderThreshold.inradius_unique`,
 `DecoderThreshold.dec_eq_of_close`, `DecoderThreshold.misalignment_cos_bound`,
 `DecoderThreshold.misalignment_bound`.
* **Target 3a** (uniqueness threshold `cos(π/8)`): `DecoderUniqueness.overlap_triangle_bound`,
 `DecoderUniqueness.uniqueness_threshold`.
* **Target 3b** (n = 1 universality): `DecoderN1.n1_universality`,
 `DecoderN1.n1_threshold_gt`.
* **Target 4** (abstract equivariance): `DecoderThreshold.equivariance`.
* **Target 5** (logical decoding / similarity reduction): `DecoderLogical.closest_smul`,
 connecting to `BWArith.pinned_iter` and `BWArith.bell_theory`.

All proofs use only the standard axioms `propext`, `Classical.choice`, `Quot.sound`
(plus `Lean.ofReduceBool`/`Lean.trustCompiler` for the pre-existing `native_decide`
computations in `BarnesWall.lean`, which we do not touch).
-/

-- Target 1
#print axioms DecoderFidelity.dist_sq_eq
#print axioms DecoderFidelity.dist_sq_ge
#print axioms DecoderFidelity.exists_dist_sq_eq_inf
-- Target 2
#print axioms DecoderThreshold.inradius_unique
#print axioms DecoderThreshold.misalignment_bound
#print axioms DecoderThreshold.equivariance
-- Target 3
#print axioms DecoderUniqueness.overlap_triangle_bound
#print axioms DecoderUniqueness.uniqueness_threshold
#print axioms DecoderN1.n1_universality
-- Target 5
#print axioms DecoderLogical.closest_smul
