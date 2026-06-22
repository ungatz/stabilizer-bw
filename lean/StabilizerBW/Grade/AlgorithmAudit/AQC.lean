import StabilizerBW.Grade.AlgorithmAudit.AQC.PhaseEstimation
import StabilizerBW.Grade.AlgorithmAudit.AQC.AmplitudeAmplification
import StabilizerBW.Grade.AlgorithmAudit.AQC.HHL
import StabilizerBW.Grade.AlgorithmAudit.AQC.VQE
import StabilizerBW.Grade.AlgorithmAudit.AQC.Carries
import StabilizerBW.Grade.AlgorithmAudit.AQC.Summary
import StabilizerBW.Grade.AlgorithmAudit.AQC.AxiomProbe

/-!
# AQCAudit — a Barnes–Wall λ-adic grade audit of four further AQC algorithms

Aggregator for the gate-level grade audit of four standard advanced-quantum-computing
algorithm classes, extending the development (``StabilizerBW.GradeAudit.``: QFT / Shor /
Grover / Trotter) and the development (``StabilizerBW.Grade.Comparisons.Incomparability.``: the cT /
CCZ strict-dominance witnesses).

Every reported grade is a genuine `T`-count of an honest Clifford+T circuit on the
strict fragment `{H, S, T, CNOT}`, with the non-Clifford synthesis content carried
as explicit named structural unknowns (never axioms, never fabricated closed forms).

Contents:

* `PhaseEstimation` — QPE grade `k · tPerControlledU m + tPerRot · k(k-1)/2`;
* `AmplitudeAmplification` — AA grade `m · (tO + tD)`;
* `HHL` — HHL grade `2 · QPE-grade + eigCount · tPerCtrlRotation`, with the
  eigenvalue count carried (and bounded by the matrix dimension `2^k`);
* `VQE` — VQE grade `L · (n · tPerRot) + 3 · tPerTrotterRot · (n-1)`;
* `Carries` — the `AQCSynthesisCarry` bundle and the concrete, substantive
  `JiangWangCarry` instances `qpeCarry`, `aaCarry`, `hhlCarry`, `vqeCarry`;
* `Summary` — the `gradeAudit_summary_AQC` four-algorithm table;
* `AxiomProbe` — `#print axioms` on every headline.

Each algorithm also has a substantive comparison theorem
`X_grade_dominates_jiangWang` proving `circuitGrade ≥ ν(U)` against the genuine
(possibly positive) Jiang–Wang unitary stabilizer nullity, never via `Nat.zero_le`.
-/
