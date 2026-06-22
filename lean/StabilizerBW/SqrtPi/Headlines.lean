import StabilizerBW.SqrtPi.Pi3
import StabilizerBW.SqrtPi.OplusCost
import StabilizerBW.SqrtPi.Clifford
import StabilizerBW.SqrtPi.BW2Table
import StabilizerBW.SqrtPi.Catalyst.Phi3
import StabilizerBW.SqrtPi.Catalyst.SwapTensor
import StabilizerBW.SqrtPi.Catalyst.Phi3General
import StabilizerBW.SqrtPi.CliffordConverse
import StabilizerBW.SqrtPi.CliffordSemantic

/-!
# Headline theorems of the graded `√Π` infrastructure

This file re-exports the headline results of the round.

* `Pi3.Headline_T1` — the graded `Π₃` infrastructure (inductive type, denotation, grade;
  `id`, `ζ₃`, `V` are grade `0`, grade is subadditive).
* `Pi3.Headline_T2` — the local cost of `⊕`: `g(diag(1,A)) = max(0, 2 - ν_λ(A-1))`, with the
  `ℤ/8ℤ` corollary `Pi3.Headline_T2_zeta_table`.
* `Pi3.Headline_T4` — the soundness (forward) inclusion of grade-`0` = Clifford at `n ≤ 2`:
  every Clifford morphism is grade `0`.
* `Pi3.Headline_T5` — the two-qubit `BW₂` diagonal grade table.
* `Pi3.Headline_T3` — catalytic-embedding grade preservation, corrected rule `Γ(g) = g` on the
  three generators `T, S, V`; the structural strawman's `Γ(g) = 2g` is refuted by `Pi3.Falsification_T3`.
* `Pi3.Headline_T4_converse_diagonal` — the sharp grade-`0` ↔ Clifford diagonal-phase converse;
  the literal syntactic converse is refuted by `Pi3.Falsification_T4_syntactic`.

## Continuation round 2 (T3**, T4**)

* `Pi3.gradeWrt2_conj_eq` — general invariance: conjugation by a grade-`0` lattice automorphism
  preserves the level-2 grade (T3**(a)(iii)).
* `Pi3.grade2_swap_eq_zero`, `Pi3.grade2_swap_conj_invariant`, `Pi3.Headline_T3_with_swap` — the
  CHKRS-S12 tensor-swap `σ^⊗` is a grade-`0` lattice automorphism, its conjugation leaves every
  level-2 grade invariant, and `Φ₃(T)` keeps grade `1` with the swap restored (discharging the
  prior round's blocker §6).
* `Pi3.Headline_T3_general` — the honest general bound: `Φ₃` preserves the grade exactly on every
  single-qubit generator (`Γ(g) = g`), and never inflates the T-count budget on composites.
* `Pi3.Falsification_T4_semantic_n1` — the **Verified Falsification** of the semantic converse:
  `diag(1, 1+√2)` is a grade-`0` integral automorphism of `L₃` that is not a phased Clifford, so
  `Aut(L₃)` is strictly larger than the phased Clifford group (`Pi3.IsClifford2Matrix`).
-/

namespace Pi3

/-- **T4 (Headline).** Soundness direction of "grade `0` = Clifford" at `n ≤ 2`:
every Clifford morphism has lattice grade `0`. -/
theorem Headline_T4 {a : Pi3 2 2} (h : IsClifford2 a) : grade2obj a = 0 :=
  Headline_T4_sound h

end Pi3
