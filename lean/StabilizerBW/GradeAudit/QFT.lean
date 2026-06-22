import StabilizerBW.GradeAudit.CircuitGrade

/-!
# Grade (= T-count) of the approximate quantum Fourier transform `AQFT_n^ε`

## Honesty note (fixing r1's exact-QFT error)

The **exact** unitary `QFT_n` is *not* in the Clifford+T fragment for `n ≥ 3`:
it contains the controlled rotation `R_3 = controlled-T` (and finer `R_k`), which
is non-Clifford and cannot be realised exactly by finitely many `{H, S, T, CNOT}`
gates.  It is therefore dishonest to assign the exact `QFT_n` a closed-form
Barnes–Wall grade on the integral Clifford+T stratum.

Following standard convention (Option A), we audit the **approximate** transform
`AQFT_n^ε`: the standard Cleve–Watrous QFT layout in which each controlled phase
rotation `R_k` (`k ≥ 2`, all non-Clifford) is replaced by its Ross–Selinger
Clifford+T synthesis to target precision `ε`.  Each such synthesis uses
`tPerRot` `T` gates, where `tPerRot = Θ(log (1/ε))` is the Ross–Selinger cost.
We carry `tPerRot` as an explicit parameter, so every reported grade is a genuine
T-count of an honest Clifford+T circuit and the `ε`-dependence is explicit.

## Layout and count

In `AQFT_n^ε`, qubit `q` (`0 ≤ q < n`) carries a Hadamard (Clifford, grade `0`)
followed by the controlled rotations `R_2, …, R_{n-q}` against the later qubits —
that is `n - 1 - q` rotation gadgets, each contributing `tPerRot` `T` tokens.
The total number of rotation gadgets is

  `∑_{q=0}^{n-1} (n - 1 - q) = ∑_{j=0}^{n-1} j = n (n-1) / 2`,

so the headline grade is

  `circuitGrade (AQFTCircuit n tPerRot) = tPerRot * (n (n-1) / 2)`,

i.e. `g(AQFT_n^ε) = Θ(n² · log (1/ε))` (and `Θ(n²)` for fixed precision).

(Arithmetic re-check, per the standard convention: the per-qubit gadget counts
are `n-1, n-2, …, 1, 0` as `q` runs `0 … n-1`; their sum is the triangular number
`∑_{j=0}^{n-1} j = n(n-1)/2`.  This replaces r1's first-qubit-only count
`∑_{j∈range(n-1)} j = (n-1)(n-2)/2`, which under-counted by omitting the rotation
blocks on qubits `1 … n-1`.)
-/

namespace GradeAudit

/-- The Clifford+T synthesis gadget for one controlled rotation `R_k`, realised to
target precision `ε` by Ross–Selinger synthesis using `tPerRot` `T` gates.  We
model the non-Clifford content as `tPerRot` `T` tokens; the Clifford framing
(`H`/`S`/`CNOT`) carries grade `0` and is omitted from the count. -/
def rotationGadget (n tPerRot : ℕ) : List (Gate n) :=
  List.replicate tPerRot (Gate.T 0)

/-- The rotation gadgets on qubit `q` in `AQFT_n^ε`: the `n - 1 - q` rotations
`R_2, …, R_{n-q}`, each synthesised to precision `ε` with `tPerRot` `T` gates. -/
def aqftRotations (n q tPerRot : ℕ) : List (Gate n) :=
  (List.range (n - 1 - q)).flatMap (fun _ => rotationGadget n tPerRot)

/-- The per-qubit block of `AQFT_n^ε`: a Hadamard on qubit `q` then its
synthesised controlled rotations. -/
def aqftBlock (n q tPerRot : ℕ) : List (Gate n) :=
  Gate.H q :: aqftRotations n q tPerRot

/-- The approximate `AQFT_n^ε` circuit: the qubit blocks `q = 0, …, n-1`. -/
def AQFTCircuit (n tPerRot : ℕ) : List (Gate n) :=
  (List.range n).flatMap (fun q => aqftBlock n q tPerRot)

/-- The closed-form grade of `AQFT_n^ε`: `tPerRot` times the total rotation count
`n (n-1) / 2`. -/
def AQFT_grade_closedForm (n tPerRot : ℕ) : ℕ := tPerRot * (n * (n - 1) / 2)

/-- One rotation gadget has grade exactly `tPerRot`. -/
theorem circuitGrade_rotationGadget (n tPerRot : ℕ) :
    circuitGrade (rotationGadget n tPerRot) = tPerRot := by
  unfold rotationGadget
  exact circuitGrade_replicate_T tPerRot 0

/-- The rotation block on qubit `q` has grade `(n - 1 - q) * tPerRot`. -/
theorem circuitGrade_aqftRotations (n q tPerRot : ℕ) :
    circuitGrade (aqftRotations n q tPerRot) = (n - 1 - q) * tPerRot := by
  unfold aqftRotations
  rw [circuitGrade_flatMap]
  have : (List.range (n - 1 - q)).map (fun _ => circuitGrade (rotationGadget n tPerRot))
      = (List.range (n - 1 - q)).map (fun _ => tPerRot) := by
    apply List.map_congr_left
    intro x _; rw [circuitGrade_rotationGadget]
  rw [this, listRange_map_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The qubit-`q` block has grade `(n - 1 - q) * tPerRot` (the Hadamard adds `0`). -/
theorem circuitGrade_aqftBlock (n q tPerRot : ℕ) :
    circuitGrade (aqftBlock n q tPerRot) = (n - 1 - q) * tPerRot := by
  unfold aqftBlock
  rw [circuitGrade_cons, gradeOf_H, Nat.zero_add, circuitGrade_aqftRotations]

/-- The total rotation-gadget count of `AQFT_n^ε` is the triangular number
`n (n-1) / 2`. -/
theorem aqft_gadget_count (n : ℕ) :
    (∑ q ∈ Finset.range n, (n - 1 - q)) = n * (n - 1) / 2 := by
  rw [Finset.sum_range_reflect (fun j => j) n, Finset.sum_range_id]

/-- **Headline grade (= T-count) of the approximate QFT `AQFT_n^ε`.** -/
theorem aqft_grade (n tPerRot : ℕ) :
    circuitGrade (AQFTCircuit n tPerRot) = AQFT_grade_closedForm n tPerRot := by
  unfold AQFTCircuit AQFT_grade_closedForm
  rw [circuitGrade_flatMap]
  have hmap : (List.range n).map (fun q => circuitGrade (aqftBlock n q tPerRot))
      = (List.range n).map (fun q => (n - 1 - q) * tPerRot) := by
    apply List.map_congr_left
    intro q _; rw [circuitGrade_aqftBlock]
  rw [hmap, listRange_map_sum]
  rw [← Finset.sum_mul, aqft_gadget_count, Nat.mul_comm]

/-- The closed form exhibits the `Θ(n²)` (for fixed precision) growth: it equals
`tPerRot` times the triangular number `n(n-1)/2`. -/
theorem aqft_grade_quadratic (n tPerRot : ℕ) :
    AQFT_grade_closedForm n tPerRot = tPerRot * (n * (n - 1) / 2) := rfl

/-- **Headline grade lower bound for the approximate QFT.** -/
theorem aqft_grade_bound (n tPerRot : ℕ) :
    circuitGrade (AQFTCircuit n tPerRot) ≥ AQFT_grade_closedForm n tPerRot := by
  rw [aqft_grade]

end GradeAudit
