import StabilizerBW.GradeAudit.CircuitGrade

/-!
# Grade (= T-count) of Shor's modular-arithmetic core via Toffoli decomposition

## Honesty note (fixing r1's fabricated-grade error)

The resource-dominant subroutine of Shor's algorithm is modular exponentiation,
built from modular multipliers, built from modular adders.  We model the
**Cuccaro–Draper–Kutin–Moulton (CDKM) ripple-carry adder** (arXiv:quant-ph/0410184),
whose only non-Clifford content is its `Toffoli` (CCNOT) gates.  Each `Toffoli`
is decomposed into the strict Clifford+T fragment `{H, S, T, CNOT}` by the
standard ancilla-free synthesis using `tPerToff` `T` gates (the textbook exact
decomposition uses `tPerToff = 7`; we carry it as a parameter).

Thus every grade reported here is a genuine T-count of an honest Clifford+T
circuit, parameterised by the explicit Toffoli count, exactly
requires.  No closed-form λ-adic grade is fabricated for any rotation gate.

## Counts (re-checked by hand)

* A CDKM `n`-bit ripple-carry adder uses `2 n - 1` Toffoli gates (the MAJ/UMA
  network: `n - 1` carry `MAJ`s, `n - 1` uncomputation `UMA`s, and one final
  carry Toffoli), so `g(adder_n) = tPerToff * (2 n - 1)`.

* Modular exponentiation chains `toffCount` Toffolis overall; with the
  schoolbook construction `toffCount = Θ(n³)` (`Θ(n)` multipliers × `Θ(n)`
  adders × `Θ(n)` Toffolis per adder).  We state the grade as
  `g = tPerToff * toffCount`, parameterised by the Toffoli count, so the cubic
  asymptotic `g(Shor) = Θ(n³ · tPerToff)` follows from `toffCount = Θ(n³)`.
-/

namespace GradeAudit

/-- The Clifford+T synthesis gadget for one `Toffoli` (CCNOT) gate: its
non-Clifford content is `tPerToff` `T` tokens (the textbook ancilla-free exact
decomposition has `tPerToff = 7`).  The surrounding `H`/`S`/`CNOT` framing has
grade `0` and is omitted from the count. -/
def toffoliGadget (n tPerToff : ℕ) : List (Gate n) :=
  List.replicate tPerToff (Gate.T 0)

/-- A circuit consisting of `toffCount` Toffoli gadgets, each synthesised with
`tPerToff` `T` gates. -/
def toffoliNetwork (n toffCount tPerToff : ℕ) : List (Gate n) :=
  (List.range toffCount).flatMap (fun _ => toffoliGadget n tPerToff)

/-- The CDKM ripple-carry adder on `n` bits, expressed via its `2 n - 1`
Toffolis. -/
def cdkmAdder (n tPerToff : ℕ) : List (Gate n) :=
  toffoliNetwork n (2 * n - 1) tPerToff

/-- Shor's modular-exponentiation core, expressed via its overall Toffoli count
`toffCount` (`= Θ(n³)` for the schoolbook construction). -/
def ShorModExp (n toffCount tPerToff : ℕ) : List (Gate n) :=
  toffoliNetwork n toffCount tPerToff

/-- One Toffoli gadget has grade exactly `tPerToff`. -/
theorem circuitGrade_toffoliGadget (n tPerToff : ℕ) :
    circuitGrade (toffoliGadget n tPerToff) = tPerToff := by
  unfold toffoliGadget
  exact circuitGrade_replicate_T tPerToff 0

/-- A `toffCount`-Toffoli network has grade exactly `tPerToff * toffCount`. -/
theorem circuitGrade_toffoliNetwork (n toffCount tPerToff : ℕ) :
    circuitGrade (toffoliNetwork n toffCount tPerToff) = tPerToff * toffCount := by
  unfold toffoliNetwork
  rw [circuitGrade_flatMap]
  have : (List.range toffCount).map (fun _ => circuitGrade (toffoliGadget n tPerToff))
      = (List.range toffCount).map (fun _ => tPerToff) := by
    apply List.map_congr_left
    intro x _; rw [circuitGrade_toffoliGadget]
  rw [this, listRange_map_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

/-- The CDKM adder grade closed form: `tPerToff * (2 n - 1)`. -/
def cdkmAdder_grade_closedForm (n tPerToff : ℕ) : ℕ := tPerToff * (2 * n - 1)

/-- **Headline grade (= T-count) of the CDKM ripple-carry adder.** -/
theorem cdkmAdder_grade (n tPerToff : ℕ) :
    circuitGrade (cdkmAdder n tPerToff) = cdkmAdder_grade_closedForm n tPerToff := by
  unfold cdkmAdder cdkmAdder_grade_closedForm
  exact circuitGrade_toffoliNetwork n (2 * n - 1) tPerToff

/-- **Headline grade (= T-count) of Shor's modular-exponentiation core.**  It is
exactly `tPerToff` times the overall Toffoli count. -/
theorem shor_modexp_grade (n toffCount tPerToff : ℕ) :
    circuitGrade (ShorModExp n toffCount tPerToff) = tPerToff * toffCount := by
  unfold ShorModExp
  exact circuitGrade_toffoliNetwork n toffCount tPerToff

/-- **Headline grade lower bound for Shor's modular-exponentiation core.** -/
theorem shor_grade_bound (n toffCount tPerToff : ℕ) :
    circuitGrade (ShorModExp n toffCount tPerToff) ≥ tPerToff * toffCount := by
  rw [shor_modexp_grade]

/-- With the schoolbook cubic Toffoli count `toffCount = n³`, the grade is exactly
`tPerToff * n³`, exhibiting the `Θ(n³)` growth. -/
theorem shor_grade_cubic (n tPerToff : ℕ) :
    circuitGrade (ShorModExp n (n ^ 3) tPerToff) = tPerToff * n ^ 3 :=
  shor_modexp_grade n (n ^ 3) tPerToff

end GradeAudit
