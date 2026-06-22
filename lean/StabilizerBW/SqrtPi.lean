import StabilizerBW.SqrtPi.Z8Ring
import StabilizerBW.SqrtPi.Q8
import StabilizerBW.SqrtPi.Lattice
import StabilizerBW.SqrtPi.OplusCost
import StabilizerBW.SqrtPi.Grade
import StabilizerBW.SqrtPi.Pi3
import StabilizerBW.SqrtPi.Clifford
import StabilizerBW.SqrtPi.BW2Table
import StabilizerBW.SqrtPi.Catalyst
import StabilizerBW.SqrtPi.Level2.Zi
import StabilizerBW.SqrtPi.Level2.Grade2
import StabilizerBW.SqrtPi.Level2.Lattice
import StabilizerBW.SqrtPi.Level2.Pi2
import StabilizerBW.SqrtPi.Catalyst.Phi3
import StabilizerBW.SqrtPi.Catalyst.SwapTensor
import StabilizerBW.SqrtPi.Catalyst.Phi3General
import StabilizerBW.SqrtPi.CliffordConverse
import StabilizerBW.SqrtPi.CliffordSemantic
import StabilizerBW.SqrtPi.Headlines

/-!
# Graded `√Π`: a lattice stratification of the free model of quantum computing

Umbrella import for the graded `√Π` infrastructure. See ``StabilizerBW.SqrtPi.`Headlines.lean`
for the headline theorems and `Proofs/` for the paper-grade exposition.

## Continuation round (T3*, T4*)

* **T3\*** (``StabilizerBW.SqrtPi.`Level2/` and `Catalyst/Phi3.lean`): the level-2 ring `ℤ[i]`,
  the level-2 Barnes–Wall lattices and grade, the catalytic embedding `Φ₃ : Π₃ → Π₂`, and the
  three generator grade verifications.  The conjectured grade-doubling `Γ(g) = 2g` is
  **kernel-falsified** on `T` (`Pi3.Falsification_T3`); the corrected rule `Γ(g) = g` is
  kernel-proved on `T, S, V` (`Pi3.Headline_T3`).
* **T4\*** (``StabilizerBW.SqrtPi.`CliffordConverse.lean`): the literal syntactic converse
  `grade2obj a = 0 → IsClifford2 a` is **kernel-falsified** (`Pi3.Falsification_T4_syntactic`,
  counterexample `ζ₃ ⊕ ζ₃`); the true diagonal-phase converse `grade-0 ↔ Clifford phase` is
  kernel-proved (`Pi3.Headline_T4_converse_diagonal`).
-/
