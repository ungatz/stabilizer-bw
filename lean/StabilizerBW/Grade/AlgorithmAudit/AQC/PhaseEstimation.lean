import StabilizerBW.GradeAudit

/-!
# T1 — Grade (= T-count) of quantum phase estimation `QPE_{k,m}`

## Honesty note

Quantum phase estimation on `k` precision qubits has the standard Cleve–Watrous /
Nielsen–Chuang layout:

1. `k` Hadamards on the precision register (Clifford, grade `0`);
2. the controlled powers `controlled-U^{2^j}` for `j ∈ {0, …, k-1}` — `k`
   controlled-unitary calls, each synthesised in the strict Clifford+T fragment
   `{H, S, T, CNOT}` using `tPerControlledU m` `T` gates (`m` is the size of the
   controlled-unitary's classical/quantum description; the per-call `T`-count is
   carried as the explicit structural unknown `tPerControlledU : ℕ → ℕ`);
3. the inverse QFT on the `k` precision qubits, audited exactly as the approximate
   `AQFT_k^ε` of Layer 60 (`invQFTCircuit k tPerRot`).

Because the `k` Hadamards are Clifford they contribute grade `0`; the closed-form
grade is therefore

  `circuitGrade (phaseEstimation k m tPerRot tPerControlledU)
      = k · tPerControlledU m + circuitGrade (invQFTCircuit k tPerRot)`
      ` = k · tPerControlledU m + tPerRot · k(k-1)/2`,

i.e. `g(QPE_{k,m}) = Θ(k · tPerControlledU m) + Θ(k² · log 1/ε)`.  (The original
informal `+ k` Hadamard term is `0` in this Clifford+T accounting and is recorded
honestly as such.)
-/

namespace GradeAudit

/-- `circuitGrade` of a layer of Hadamards is `0` (Clifford). -/
theorem circuitGrade_map_H {n : ℕ} (l : List ℕ) :
    circuitGrade (l.map (fun q => (Gate.H q : Gate n))) = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.map_cons, circuitGrade_cons, gradeOf_H, ih]

/-- The `k` precision-register Hadamards of QPE. -/
def qpeHadamards (k : ℕ) : List (Gate k) := (List.range k).map (fun q => Gate.H q)

/-- The Clifford+T synthesis gadget for one `controlled-U^{2^j}` call: `t` `T`
tokens (with `t = tPerControlledU m` the carried per-call cost). -/
def controlledUGadget (k t : ℕ) : List (Gate k) := List.replicate t (Gate.T 0)

/-- The `k` controlled powers `controlled-U^{2^j}`, `j = 0, …, k-1`, each
synthesised with `tPerControlledU m` `T` gates. -/
def qpeControlledUs (k m : ℕ) (tPerControlledU : ℕ → ℕ) : List (Gate k) :=
  (List.range k).flatMap (fun _ => controlledUGadget k (tPerControlledU m))

/-- The inverse QFT on the `k` precision qubits, audited as the approximate
`AQFT_k^ε` (same gate count as its inverse). -/
def invQFTCircuit (k tPerRot : ℕ) : List (Gate k) := AQFTCircuit k tPerRot

/-- **Quantum phase estimation** on `k` precision qubits for an `m`-described
controlled unitary: `k` Hadamards, then the `k` controlled powers, then the
inverse QFT. -/
def phaseEstimation (k m tPerRot : ℕ) (tPerControlledU : ℕ → ℕ) : List (Gate k) :=
  qpeHadamards k ++ qpeControlledUs k m tPerControlledU ++ invQFTCircuit k tPerRot

/-- The closed-form grade of QPE. -/
def phaseEstimation_grade_closedForm (k m tPerRot : ℕ) (tPerControlledU : ℕ → ℕ) : ℕ :=
  k * tPerControlledU m + AQFT_grade_closedForm k tPerRot

theorem circuitGrade_qpeHadamards (k : ℕ) : circuitGrade (qpeHadamards k) = 0 :=
  circuitGrade_map_H _

theorem circuitGrade_controlledUGadget (k t : ℕ) :
    circuitGrade (controlledUGadget k t) = t := by
  unfold controlledUGadget
  exact circuitGrade_replicate_T t 0

theorem circuitGrade_qpeControlledUs (k m : ℕ) (tPerControlledU : ℕ → ℕ) :
    circuitGrade (qpeControlledUs k m tPerControlledU) = k * tPerControlledU m := by
  unfold qpeControlledUs
  rw [circuitGrade_flatMap]
  have : (List.range k).map
        (fun _ => circuitGrade (controlledUGadget k (tPerControlledU m)))
      = (List.range k).map (fun _ => tPerControlledU m) := by
    apply List.map_congr_left
    intro x _; rw [circuitGrade_controlledUGadget]
  rw [this, listRange_map_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem circuitGrade_invQFTCircuit (k tPerRot : ℕ) :
    circuitGrade (invQFTCircuit k tPerRot) = AQFT_grade_closedForm k tPerRot := by
  unfold invQFTCircuit
  exact aqft_grade k tPerRot

/-- **Headline grade (= T-count) of quantum phase estimation.** -/
theorem qpe_grade (k m tPerRot : ℕ) (tPerControlledU : ℕ → ℕ) :
    circuitGrade (phaseEstimation k m tPerRot tPerControlledU)
      = phaseEstimation_grade_closedForm k m tPerRot tPerControlledU := by
  unfold phaseEstimation phaseEstimation_grade_closedForm
  rw [circuitGrade_append, circuitGrade_append, circuitGrade_qpeHadamards,
      circuitGrade_qpeControlledUs, circuitGrade_invQFTCircuit, Nat.zero_add]

/-- **Headline grade lower bound for quantum phase estimation.** -/
theorem qpe_grade_bound (k m tPerRot : ℕ) (tPerControlledU : ℕ → ℕ) :
    circuitGrade (phaseEstimation k m tPerRot tPerControlledU)
      ≥ phaseEstimation_grade_closedForm k m tPerRot tPerControlledU := by
  rw [qpe_grade]

/-- **QPE comparison (Jiang–Wang).**  The audited QPE grade dominates the genuine
Jiang–Wang unitary nullity, given that the audited circuit realises the carried
unitary at the modelled `T`-count. -/
theorem qpe_grade_dominates_jiangWang (k m tPerRot : ℕ) (tPerControlledU : ℕ → ℕ)
    (c : JiangWangCarry k)
    (hmodel : c.tCount = circuitGrade (phaseEstimation k m tPerRot tPerControlledU)) :
    circuitGrade (phaseEstimation k m tPerRot tPerControlledU) ≥ c.nullity := by
  rw [JiangWangCarry.nullity, ← hmodel]; exact c.jw_bound

end GradeAudit
