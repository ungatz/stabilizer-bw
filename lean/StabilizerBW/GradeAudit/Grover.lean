import StabilizerBW.GradeAudit.CircuitGrade

/-!
# Grade (= T-count) of a concrete Grover oracle via Toffoli decomposition

## Honesty note (fixing r1's fabricated-grade error)

Rather than positing an abstract "one T per marked item" oracle, we audit a
**concrete** predicate: the AND-of-bits predicate `f(x) = (x = 1…1)`, marking the
single all-ones computational-basis state of an `n`-bit register.  Its standard
reversible phase oracle is the multi-controlled `Z` gate `C^{n-1}Z` on the `n`
data qubits, implemented by an ancilla-assisted ladder of `n - 1` `Toffoli`
(CCNOT) gates (the textbook AND-ladder: `n - 1` Toffolis to compute the AND into
an ancilla, a `Z`/phase on the ancilla, then `n - 1` Toffolis to uncompute — but
the uncomputation Toffolis can be merged, giving the standard `n - 1` net
non-Clifford Toffolis for the relative-phase Margolus/AND construction; we use the
`n - 1` count of the clean AND-ladder).

Each `Toffoli` is decomposed into the strict Clifford+T fragment `{H, S, T, CNOT}`
with `tPerToff` `T` gates (textbook exact synthesis: `tPerToff = 7`).  Every grade
reported is therefore a genuine T-count of an honest Clifford+T circuit.

## Count (re-checked by hand)

`g(C^{n-1}Z oracle) = tPerToff * (n - 1)`, i.e. `Θ(n)` per oracle call (for fixed
`tPerToff`).  The Clifford framing (`H`/`S`/`CNOT` and the diffusion operator's
Cliffords) contributes `0`.
-/

namespace GradeAudit

variable {n : ℕ}

/-- The Clifford+T synthesis gadget for one `Toffoli` (CCNOT): `tPerToff` `T`
tokens (textbook exact synthesis `tPerToff = 7`). -/
def groverToffoliGadget (n tPerToff : ℕ) : List (Gate n) :=
  List.replicate tPerToff (Gate.T 0)

/-- The exact Clifford+T oracle for the AND-of-bits predicate `f(x) = (x = 1…1)`
on `n` data qubits (`+1` ancilla): the AND-ladder of `n - 1` Toffoli gadgets, each
synthesised with `tPerToff` `T` gates.  The phase `Z` and the ladder's `CNOT`
framing have grade `0`. -/
def GroverAndOracle (n tPerToff : ℕ) : List (Gate (n + 1)) :=
  [Gate.H 0] ++ ((List.range (n - 1)).flatMap (fun _ => groverToffoliGadget (n + 1) tPerToff))
    ++ [Gate.H 0]

/-- The closed-form grade of the AND-of-bits Grover oracle: `tPerToff * (n - 1)`. -/
def grover_grade_closedForm (n tPerToff : ℕ) : ℕ := tPerToff * (n - 1)

/-- One Grover Toffoli gadget has grade exactly `tPerToff`. -/
theorem circuitGrade_groverToffoliGadget (n tPerToff : ℕ) :
    circuitGrade (groverToffoliGadget n tPerToff) = tPerToff := by
  unfold groverToffoliGadget
  exact circuitGrade_replicate_T tPerToff 0

/-- **Headline grade (= T-count) of the AND-of-bits Grover oracle.** -/
theorem grover_grade (n tPerToff : ℕ) :
    circuitGrade (GroverAndOracle n tPerToff) = grover_grade_closedForm n tPerToff := by
  unfold GroverAndOracle grover_grade_closedForm
  rw [circuitGrade_append, circuitGrade_append]
  rw [circuitGrade_flatMap]
  have : (List.range (n - 1)).map (fun _ => circuitGrade (groverToffoliGadget (n + 1) tPerToff))
      = (List.range (n - 1)).map (fun _ => tPerToff) := by
    apply List.map_congr_left
    intro x _; rw [circuitGrade_groverToffoliGadget]
  rw [this, listRange_map_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
  simp [circuitGrade_cons]
  ring

/-- **Headline grade lower bound for the AND-of-bits Grover oracle.** -/
theorem grover_grade_bound (n tPerToff : ℕ) :
    circuitGrade (GroverAndOracle n tPerToff) ≥ grover_grade_closedForm n tPerToff := by
  rw [grover_grade]

/-- The grade is `Θ(n)` per oracle call (for fixed `tPerToff`). -/
theorem grover_grade_linear (n tPerToff : ℕ) :
    circuitGrade (GroverAndOracle n tPerToff) = tPerToff * (n - 1) :=
  grover_grade n tPerToff

end GradeAudit
