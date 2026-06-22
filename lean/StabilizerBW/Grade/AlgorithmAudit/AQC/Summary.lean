import StabilizerBW.Grade.AlgorithmAudit.AQC.Carries

/-!
# T6 — The AQC grade-audit summary table

`gradeAudit_summary_AQC` collects, in one place, the four headline closed-form
grades (= T-counts) of the audited AQC algorithms, each a genuine `T`-count of an
honest Clifford+T circuit with its synthesis carries explicit:

| Algorithm | `circuitGrade` closed form | `Θ(...)` asymptotic |
|-----------|----------------------------|---------------------|
| QPE  `phaseEstimation k m tPerRot tPerControlledU` | `k · tPerControlledU m + tPerRot · k(k-1)/2` | `Θ(k · tPerControlledU m + k² log 1/ε)` |
| AA   `amplitudeAmplification m n tO tD`            | `m · (tO + tD)`                              | `Θ(m · (tPerGroverOracle + tPerGroverDiffusion))` |
| HHL  `hhl k m tPerRot eigCount tPerCtrlRotation tPerControlledU` | `2 · QPE-grade + eigCount · tPerCtrlRotation` | `Θ(k · tPerControlledU m + k² log 1/ε + eigCount log 1/ε)` |
| VQE  `vqe L n tPerRot tPerTrotterRot`              | `L · (n · tPerRot) + 3 · tPerTrotterRot · (n-1)` | `Θ(L · n log 1/ε + n log 1/ε)` |

This is the publishable summary for the AQC half of the chapter's positioning,
extending Layer 60 (QFT / Shor / Grover / Trotter) and Layer 65 (incomparability
witnesses).
-/

namespace GradeAudit

/-- **The AQC grade-audit summary table.**  Each conjunct is the headline
closed-form grade (= T-count) of one audited AQC algorithm. -/
theorem gradeAudit_summary_AQC
    (k m tPerRot eigCount tPerCtrlRotation L n tO tD tPerTrotterRot : ℕ)
    (tPerControlledU : ℕ → ℕ) :
    -- QPE
    (circuitGrade (phaseEstimation k m tPerRot tPerControlledU)
      = k * tPerControlledU m + tPerRot * (k * (k - 1) / 2)) ∧
    -- Amplitude amplification
    (circuitGrade (amplitudeAmplification m n tO tD) = m * (tO + tD)) ∧
    -- HHL
    (circuitGrade (hhl k m tPerRot eigCount tPerCtrlRotation tPerControlledU)
      = 2 * (k * tPerControlledU m + tPerRot * (k * (k - 1) / 2))
          + eigCount * tPerCtrlRotation) ∧
    -- VQE
    (circuitGrade (vqe L n tPerRot tPerTrotterRot)
      = L * (n * tPerRot) + 3 * tPerTrotterRot * (n - 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [qpe_grade]; rfl
  · rw [aa_grade]; rfl
  · rw [hhl_grade]
    show 2 * phaseEstimation_grade_closedForm k m tPerRot tPerControlledU
        + eigCount * tPerCtrlRotation = _
    rfl
  · rw [vqe_grade]; rfl

end GradeAudit
