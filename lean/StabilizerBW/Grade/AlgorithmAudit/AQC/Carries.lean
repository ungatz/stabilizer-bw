import StabilizerBW.Grade.AlgorithmAudit.AQC.PhaseEstimation
import StabilizerBW.Grade.AlgorithmAudit.AQC.AmplitudeAmplification
import StabilizerBW.Grade.AlgorithmAudit.AQC.HHL
import StabilizerBW.Grade.AlgorithmAudit.AQC.VQE

/-!
# T5 — The bundled synthesis carries and concrete `JiangWangCarry` instances

This file collects the four-algorithm audit's two kinds of carried data.

## The synthesis-cost bundle

`AQCSynthesisCarry` bundles the per-sub-circuit `T`-count carries of the four
algorithms into a single record (mirroring Layer 60's `tPerToff = 7` discipline:
honest structural unknowns parameterised by structure, **not** axioms):

* `tPerControlledU`     — `T`-count of one controlled-unitary at a given precision (QPE/HHL);
* `tPerGroverOracle`    — `T`-count of one amplitude-amplification oracle call;
* `tPerGroverDiffusion` — `T`-count of one diffusion (reflection) operator;
* `tPerCtrlRotation`    — `T`-count of one HHL eigenvalue-conditioned rotation;
* `tPerVQELayer`        — `T`-count of one VQE ansatz layer (layers, qubits).

## The concrete `JiangWangCarry` instances

For each algorithm we produce a concrete `GradeAudit.JiangWangCarry n` instance,
matching the `cT_JiangWangCarry` / `CCZ_JiangWangCarry` discipline of Layer 65:
a genuine `n`-qubit unitary (with a unitarity proof), the realised `T`-count
(set to the audited circuit's actual `circuitGrade` at concrete parameters), and
the carried Jiang–Wang bound `ν(U) ≤ T(U)` discharged by kernel computation
(`decide`, no `native_decide`).  Each instance has **positive** nullity
(`ν = 2n > 0`), so the comparison theorems are genuinely substantive — never a
`Nat.zero_le` tautology.  As in Layer 60's `comparison_is_substantive`, the
register unitary is taken to be the identity with `commutantCard = 1`, certifying
non-vacuity with the maximal nullity floor `2n`; the algorithm-specific synthesis
content lives in the realised `tCount`.
-/

namespace GradeAudit

/-- The bundled per-sub-circuit `T`-count carries of the four AQC algorithms.
Each field is an honest structural unknown about a specific synthesis choice,
parameterised by the relevant structure, exactly as Layer 60's `tPerToff = 7`. -/
structure AQCSynthesisCarry where
  /-- `T`-count of one controlled-unitary at a given precision (QPE / HHL). -/
  tPerControlledU : ℕ → ℕ
  /-- `T`-count of one amplitude-amplification marking oracle call. -/
  tPerGroverOracle : ℕ → ℕ
  /-- `T`-count of one amplitude-amplification diffusion (reflection) operator. -/
  tPerGroverDiffusion : ℕ → ℕ
  /-- `T`-count of one HHL eigenvalue-conditioned Ross–Selinger rotation. -/
  tPerCtrlRotation : ℕ → ℕ
  /-- `T`-count of one VQE ansatz layer, as a function of (layers, qubits). -/
  tPerVQELayer : ℕ → ℕ → ℕ

/-! ### The concrete `JiangWangCarry` instances -/

/-- A concrete `JiangWangCarry 2` instance for **QPE** (`k = 2` precision qubits),
with `tCount` the realised grade at the sample parameters and positive nullity
`ν = 4`. -/
noncomputable def qpeCarry : JiangWangCarry 2 where
  U := 1
  unitary := one_mem _
  commutantCard := 1
  tCount := circuitGrade (phaseEstimation 2 4 2 (fun _ => 3))
  jw_bound := by rw [qpe_grade]; decide

/-- A concrete `JiangWangCarry 2` instance for **amplitude amplification**
(`n = 2` qubits, `m = 3` iterations), with positive nullity `ν = 4`. -/
noncomputable def aaCarry : JiangWangCarry 2 where
  U := 1
  unitary := one_mem _
  commutantCard := 1
  tCount := circuitGrade (amplitudeAmplification 3 2 2 2)
  jw_bound := by rw [aa_grade]; decide

/-- A concrete `JiangWangCarry 2` instance for **HHL** (`k = 2` precision qubits),
with positive nullity `ν = 4`. -/
noncomputable def hhlCarry : JiangWangCarry 2 where
  U := 1
  unitary := one_mem _
  commutantCard := 1
  tCount := circuitGrade (hhl 2 4 2 2 2 (fun _ => 3))
  jw_bound := by rw [hhl_grade]; decide

/-- A concrete `JiangWangCarry 2` instance for **VQE** (`n = 2` qubits, `L = 2`
layers), with positive nullity `ν = 4`. -/
noncomputable def vqeCarry : JiangWangCarry 2 where
  U := 1
  unitary := one_mem _
  commutantCard := 1
  tCount := circuitGrade (vqe 2 2 2 2)
  jw_bound := by rw [vqe_grade]; decide

/-! ### The recorded nullities are positive (non-vacuity) -/

theorem qpeCarry_nullity : qpeCarry.nullity = 4 := by
  rw [JiangWangCarry.nullity]; decide

theorem aaCarry_nullity : aaCarry.nullity = 4 := by
  rw [JiangWangCarry.nullity]; decide

theorem hhlCarry_nullity : hhlCarry.nullity = 4 := by
  rw [JiangWangCarry.nullity]; decide

theorem vqeCarry_nullity : vqeCarry.nullity = 4 := by
  rw [JiangWangCarry.nullity]; decide

/-- All four concrete carries have **positive** Jiang–Wang nullity: the AQC
comparison theorems dominate a genuinely positive invariant, not a definitional
`0`. -/
theorem aqc_carries_substantive :
    0 < qpeCarry.nullity ∧ 0 < aaCarry.nullity ∧
    0 < hhlCarry.nullity ∧ 0 < vqeCarry.nullity := by
  rw [qpeCarry_nullity, aaCarry_nullity, hhlCarry_nullity, vqeCarry_nullity]
  exact ⟨by decide, by decide, by decide, by decide⟩

end GradeAudit
