import StabilizerBW.GradeAudit

/-!
# T4 — Grade (= T-count) of the variational quantum eigensolver `VQE_{L,n}`

## Honesty note

VQE (Peruzzo et al., Nat. Commun. 2014) prepares a variational state with a
**hardware-efficient ansatz** and measures the expectation of a Trotterised
Hamiltonian.  We audit the standard layout:

* The ansatz has `L` layers; each layer is a per-qubit single-qubit rotation on
  all `n` qubits (a Ross–Selinger-synthesised rotation with `tPerRot` `T` gates
  each, so `n · tPerRot` `T` gates per layer) followed by a **ladder of `n - 1`
  CNOTs** (Clifford, grade `0`).  Hence each layer contributes `n · tPerRot`,
  exactly the structural strawman's `n · tPerRot + (n-1) · 0`.
* The Trotterised Hamiltonian evolution is the Layer 60 single Heisenberg Trotter
  step on `n` sites, with per-Pauli-rotation cost `tPerTrotterRot`, contributing
  `3 · tPerTrotterRot · (n - 1)`.

The closed-form grade is

  `circuitGrade (vqe L n tPerRot tPerTrotterRot)
      = L · (n · tPerRot) + 3 · tPerTrotterRot · (n - 1)`,

i.e. `g(VQE) = Θ(L · n · log 1/ε) + Θ(n · log 1/ε)` (the per-layer term plus the
Trotter term).
-/

namespace GradeAudit

/-- The per-qubit single-qubit rotations of one ansatz layer: `n` rotations, each
a `tPerRot`-`T` synthesis. -/
def vqeRotLayer (n tPerRot : ℕ) : List (Gate n) :=
  (List.range n).flatMap (fun _ => List.replicate tPerRot (Gate.T 0))

/-- The CNOT entangling ladder of one ansatz layer: `n - 1` CNOTs (Clifford,
grade `0`). -/
def vqeCnotLadder (n : ℕ) : List (Gate n) :=
  (List.range (n - 1)).map (fun i => Gate.CNOT i (i + 1))

/-- One hardware-efficient ansatz layer: per-qubit rotations then the CNOT ladder. -/
def vqeAnsatzLayer (n tPerRot : ℕ) : List (Gate n) :=
  vqeRotLayer n tPerRot ++ vqeCnotLadder n

/-- The full `L`-layer hardware-efficient ansatz. -/
def vqeAnsatz (L n tPerRot : ℕ) : List (Gate n) :=
  (List.range L).flatMap (fun _ => vqeAnsatzLayer n tPerRot)

/-- **The VQE circuit**: the `L`-layer ansatz followed by a Trotterised
Heisenberg Hamiltonian evolution on the `n` qubits. -/
def vqe (L n tPerRot tPerTrotterRot : ℕ) : List (Gate n) :=
  vqeAnsatz L n tPerRot ++ Heisenberg1DTrotter n tPerTrotterRot

/-- The closed-form grade of VQE. -/
def vqe_grade_closedForm (L n tPerRot tPerTrotterRot : ℕ) : ℕ :=
  L * (n * tPerRot) + 3 * tPerTrotterRot * (n - 1)

/-- `circuitGrade` of the CNOT ladder is `0` (Clifford). -/
theorem circuitGrade_vqeCnotLadder (n : ℕ) : circuitGrade (vqeCnotLadder n) = 0 := by
  unfold vqeCnotLadder
  induction (List.range (n - 1)) with
  | nil => rfl
  | cons a as ih => simp [List.map_cons, circuitGrade_cons, gradeOf_CNOT, ih]

theorem circuitGrade_vqeRotLayer (n tPerRot : ℕ) :
    circuitGrade (vqeRotLayer n tPerRot) = n * tPerRot := by
  unfold vqeRotLayer
  rw [circuitGrade_flatMap]
  have : (List.range n).map
        (fun _ => circuitGrade (List.replicate tPerRot (Gate.T 0 : Gate n)))
      = (List.range n).map (fun _ => tPerRot) := by
    apply List.map_congr_left
    intro x _; rw [circuitGrade_replicate_T]
  rw [this, listRange_map_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem circuitGrade_vqeAnsatzLayer (n tPerRot : ℕ) :
    circuitGrade (vqeAnsatzLayer n tPerRot) = n * tPerRot := by
  unfold vqeAnsatzLayer
  rw [circuitGrade_append, circuitGrade_vqeRotLayer, circuitGrade_vqeCnotLadder, Nat.add_zero]

theorem circuitGrade_vqeAnsatz (L n tPerRot : ℕ) :
    circuitGrade (vqeAnsatz L n tPerRot) = L * (n * tPerRot) := by
  unfold vqeAnsatz
  rw [circuitGrade_flatMap]
  have : (List.range L).map (fun _ => circuitGrade (vqeAnsatzLayer n tPerRot))
      = (List.range L).map (fun _ => n * tPerRot) := by
    apply List.map_congr_left
    intro x _; rw [circuitGrade_vqeAnsatzLayer]
  rw [this, listRange_map_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Headline grade (= T-count) of VQE.** -/
theorem vqe_grade (L n tPerRot tPerTrotterRot : ℕ) :
    circuitGrade (vqe L n tPerRot tPerTrotterRot)
      = vqe_grade_closedForm L n tPerRot tPerTrotterRot := by
  unfold vqe vqe_grade_closedForm
  rw [circuitGrade_append, circuitGrade_vqeAnsatz, circuitGrade_Heisenberg1DTrotter]

/-- **Headline grade lower bound for VQE.** -/
theorem vqe_grade_bound (L n tPerRot tPerTrotterRot : ℕ) :
    circuitGrade (vqe L n tPerRot tPerTrotterRot)
      ≥ vqe_grade_closedForm L n tPerRot tPerTrotterRot := by
  rw [vqe_grade]

/-- **VQE comparison (Jiang–Wang).** -/
theorem vqe_grade_dominates_jiangWang (L n tPerRot tPerTrotterRot : ℕ) (c : JiangWangCarry n)
    (hmodel : c.tCount = circuitGrade (vqe L n tPerRot tPerTrotterRot)) :
    circuitGrade (vqe L n tPerRot tPerTrotterRot) ≥ c.nullity := by
  rw [JiangWangCarry.nullity, ← hmodel]; exact c.jw_bound

end GradeAudit
