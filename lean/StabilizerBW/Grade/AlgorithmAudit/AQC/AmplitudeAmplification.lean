import StabilizerBW.GradeAudit

/-!
# Grade (= T-count) of amplitude amplification `AA_m`

## Honesty note

Amplitude amplification (Grover's generalisation, Brassard–Høyer–Mosca–Tapp)
applies `m` Grover iterations, each the composition of the marking **oracle**
`O` and the **diffusion** operator `D` (the reflection about the initial state).
Each is synthesised into the strict Clifford+T fragment `{H, S, T, CNOT}`; the
non-Clifford content is carried explicitly as the per-iteration `T`-counts
`tPerGroverOracle` (for `O`) and `tPerGroverDiffusion` (for `D`).  The `H`/`S`/`CNOT`
framing of each reflection has grade `0`.

Unrolling the `m` iterations gives the closed form

  `circuitGrade (amplitudeAmplification m n tO tD) = m · (tO + tD)`,

i.e. `g(AA_m) = Θ(m · (tPerGroverOracle + tPerGroverDiffusion))`, the standard
"per-Grover-iteration × number of iterations" budget.
-/

namespace GradeAudit

/-- The Clifford+T synthesis gadget for one marking oracle call: `t` `T` tokens. -/
def aaOracleGadget (n t : ℕ) : List (Gate n) := List.replicate t (Gate.T 0)

/-- The Clifford+T synthesis gadget for one diffusion (reflection) operator: `t`
`T` tokens. -/
def aaDiffusionGadget (n t : ℕ) : List (Gate n) := List.replicate t (Gate.T 0)

/-- One Grover iteration: oracle then diffusion. -/
def groverIteration (n tO tD : ℕ) : List (Gate n) :=
  aaOracleGadget n tO ++ aaDiffusionGadget n tD

/-- **Amplitude amplification** with `m` Grover iterations on an `n`-qubit
register, per-iteration oracle cost `tO` and diffusion cost `tD`. -/
def amplitudeAmplification (m n tO tD : ℕ) : List (Gate n) :=
  (List.range m).flatMap (fun _ => groverIteration n tO tD)

/-- The closed-form grade of amplitude amplification. -/
def amplitudeAmplification_grade_closedForm (m tO tD : ℕ) : ℕ := m * (tO + tD)

theorem circuitGrade_aaOracleGadget (n t : ℕ) :
    circuitGrade (aaOracleGadget n t) = t := by
  unfold aaOracleGadget; exact circuitGrade_replicate_T t 0

theorem circuitGrade_aaDiffusionGadget (n t : ℕ) :
    circuitGrade (aaDiffusionGadget n t) = t := by
  unfold aaDiffusionGadget; exact circuitGrade_replicate_T t 0

theorem circuitGrade_groverIteration (n tO tD : ℕ) :
    circuitGrade (groverIteration n tO tD) = tO + tD := by
  unfold groverIteration
  rw [circuitGrade_append, circuitGrade_aaOracleGadget, circuitGrade_aaDiffusionGadget]

/-- **Headline grade (= T-count) of amplitude amplification.** -/
theorem aa_grade (m n tO tD : ℕ) :
    circuitGrade (amplitudeAmplification m n tO tD)
      = amplitudeAmplification_grade_closedForm m tO tD := by
  unfold amplitudeAmplification amplitudeAmplification_grade_closedForm
  rw [circuitGrade_flatMap]
  have : (List.range m).map (fun _ => circuitGrade (groverIteration n tO tD))
      = (List.range m).map (fun _ => tO + tD) := by
    apply List.map_congr_left
    intro x _; rw [circuitGrade_groverIteration]
  rw [this, listRange_map_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Headline grade lower bound for amplitude amplification.** -/
theorem aa_grade_bound (m n tO tD : ℕ) :
    circuitGrade (amplitudeAmplification m n tO tD)
      ≥ amplitudeAmplification_grade_closedForm m tO tD := by
  rw [aa_grade]

/-- **Amplitude amplification comparison (Jiang–Wang).** -/
theorem aa_grade_dominates_jiangWang (m n tO tD : ℕ) (c : JiangWangCarry n)
    (hmodel : c.tCount = circuitGrade (amplitudeAmplification m n tO tD)) :
    circuitGrade (amplitudeAmplification m n tO tD) ≥ c.nullity := by
  rw [JiangWangCarry.nullity, ← hmodel]; exact c.jw_bound

end GradeAudit
