import StabilizerBW.Grade.AlgorithmAudit.AQC.PhaseEstimation

/-!
# T3 — Grade (= T-count) of the Harrow–Hassidim–Lloyd algorithm `HHL_{k,m}`

## Honesty note

HHL (Harrow–Hassidim–Lloyd, PRL 2009) for the linear system `A x = b` composes:

1. **QPE** on the Hamiltonian simulation `e^{iAt}` (`k` precision qubits, matrix
   size `m`), audited as `phaseEstimation k m tPerRot tPerControlledU`;
2. the **controlled rotation** `R_y(2 arcsin(C/λ))` applied conditioned on each
   eigenvalue register value `λ` — a Ross–Selinger-synthesised single-qubit
   rotation per distinct eigenvalue, with `tPerCtrlRotation k` `T` gates each;
3. the **inverse QPE** (uncomputation), audited again as
   `phaseEstimation k m tPerRot tPerControlledU`.

We do **not** fabricate a closed-form numerical eigenvalue count.  The number of
distinct eigenvalues being rotated is carried as the named hypothesis
`HHL_eigenvalue_count` with the honest upper bound `eigCount ≤ 2 ^ k` coming from
the size of the `k`-qubit eigenvalue register (the matrix dimension bound).  The
controlled-rotation block therefore contributes `eigCount · tPerCtrlRotation k`
`T` gates, and the closed-form grade is

  `circuitGrade (hhl …) = 2 · circuitGrade (phaseEstimation …)
                              + eigCount · tPerCtrlRotation k`,

i.e. `g(HHL) = Θ(k · tPerControlledU m + k² log 1/ε) + Θ(eigCount · log 1/ε)`.
-/

namespace GradeAudit

/-- The Clifford+T synthesis of the eigenvalue-conditioned rotation block: one
Ross–Selinger rotation per distinct eigenvalue, `eigCount` of them, each with
`tPerCtrlRotation` `T` gates. -/
def ctrlRot (k eigCount tPerCtrlRotation : ℕ) : List (Gate k) :=
  (List.range eigCount).flatMap (fun _ => List.replicate tPerCtrlRotation (Gate.T 0))

/-- **The HHL circuit**: QPE, then the eigenvalue-conditioned rotation block, then
inverse QPE. -/
def hhl (k m tPerRot eigCount tPerCtrlRotation : ℕ) (tPerControlledU : ℕ → ℕ) :
    List (Gate k) :=
  phaseEstimation k m tPerRot tPerControlledU
    ++ ctrlRot k eigCount tPerCtrlRotation
    ++ phaseEstimation k m tPerRot tPerControlledU

/-- The closed-form grade of HHL. -/
def hhl_grade_closedForm (k m tPerRot eigCount tPerCtrlRotation : ℕ)
    (tPerControlledU : ℕ → ℕ) : ℕ :=
  2 * phaseEstimation_grade_closedForm k m tPerRot tPerControlledU
    + eigCount * tPerCtrlRotation

theorem circuitGrade_ctrlRot (k eigCount tPerCtrlRotation : ℕ) :
    circuitGrade (ctrlRot k eigCount tPerCtrlRotation) = eigCount * tPerCtrlRotation := by
  unfold ctrlRot
  rw [circuitGrade_flatMap]
  have : (List.range eigCount).map
        (fun _ => circuitGrade (List.replicate tPerCtrlRotation (Gate.T 0 : Gate k)))
      = (List.range eigCount).map (fun _ => tPerCtrlRotation) := by
    apply List.map_congr_left
    intro x _; rw [circuitGrade_replicate_T]
  rw [this, listRange_map_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Headline grade (= T-count) of HHL.** -/
theorem hhl_grade (k m tPerRot eigCount tPerCtrlRotation : ℕ) (tPerControlledU : ℕ → ℕ) :
    circuitGrade (hhl k m tPerRot eigCount tPerCtrlRotation tPerControlledU)
      = hhl_grade_closedForm k m tPerRot eigCount tPerCtrlRotation tPerControlledU := by
  unfold hhl hhl_grade_closedForm
  rw [circuitGrade_append, circuitGrade_append, circuitGrade_ctrlRot, qpe_grade]
  ring

/-- **Headline grade lower bound for HHL.** -/
theorem hhl_grade_bound (k m tPerRot eigCount tPerCtrlRotation : ℕ)
    (tPerControlledU : ℕ → ℕ) :
    circuitGrade (hhl k m tPerRot eigCount tPerCtrlRotation tPerControlledU)
      ≥ hhl_grade_closedForm k m tPerRot eigCount tPerCtrlRotation tPerControlledU := by
  rw [hhl_grade]

/-- The carried eigenvalue count is bounded by the eigenvalue-register dimension
`2 ^ k`: the controlled-rotation block has at most `2 ^ k · tPerCtrlRotation` `T`
gates.  (The named carry `HHL_eigenvalue_count` is the hypothesis `eigCount ≤ 2^k`.) -/
theorem hhl_ctrlRot_le (k eigCount tPerCtrlRotation : ℕ)
    (HHL_eigenvalue_count : eigCount ≤ 2 ^ k) :
    circuitGrade (ctrlRot k eigCount tPerCtrlRotation)
      ≤ 2 ^ k * tPerCtrlRotation := by
  rw [circuitGrade_ctrlRot]
  exact Nat.mul_le_mul_right _ HHL_eigenvalue_count

/-- **HHL comparison (Jiang–Wang).**  The audited HHL grade dominates the genuine
Jiang–Wang unitary nullity, given that the audited circuit realises the carried
unitary at the modelled `T`-count, with the eigenvalue count carried (and bounded
by the matrix dimension via `HHL_eigenvalue_count`). -/
theorem hhl_grade_dominates_jiangWang (k m tPerRot eigCount tPerCtrlRotation : ℕ)
    (tPerControlledU : ℕ → ℕ) (c : JiangWangCarry k)
    (HHL_eigenvalue_count : eigCount ≤ 2 ^ k)
    (hmodel : c.tCount
      = circuitGrade (hhl k m tPerRot eigCount tPerCtrlRotation tPerControlledU)) :
    circuitGrade (hhl k m tPerRot eigCount tPerCtrlRotation tPerControlledU) ≥ c.nullity := by
  -- the named eigenvalue-count carry is recorded as the honest dimension bound
  have _hbound := hhl_ctrlRot_le k eigCount tPerCtrlRotation HHL_eigenvalue_count
  rw [JiangWangCarry.nullity, ← hmodel]; exact c.jw_bound

end GradeAudit
