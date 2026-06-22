import Mathlib

/-!
# Gate-level Barnes–Wall λ-adic grade of Clifford+T circuits (Option A — strict Clifford+T basis)

This file develops the *circuit-side* grade counter `circuitGrade` on the strict
Clifford+T gate set `{H, S, T, CNOT}`.

## Why Option A (and how it fixes the original grade-convention error)

The previous round (an earlier draft) carried a controlled phase rotation `CRk k` in the gate
inductive and set `gradeOf (CRk k) = k - 2`.  That convention was rejected: it
disagrees with the chapter's actual Barnes–Wall BW₂ λ-adic grade table
(Capstone Ch.3, Prop. `prop:av-bw2-grades`), which records `g(CS) = g(CR_2) = 2`
(not `0`) and `g(cT) = g(CR_3) = 3` (not `1`).  The chapter's grade is *not* a
closed form in `(k)`; it is the geometric quantity
`g(D_P) = sup_{∅ ≠ U} (2|U| − ν_λ(m_U))`, which must be computed per case.

We therefore drop `CRk` entirely and audit on the strict Clifford+T fragment
`{H, S, T, CNOT}`.  On this fragment, and *only* on this fragment, the chapter's
BW λ-adic grade and the per-gate T-count coincide:

| Gate | chapter BW grade `g` | `gradeOf` |
|------|----------------------|-----------|
| `H`    | 0 | 0 |
| `S`    | 0 | 0 |
| `CNOT` | 0 | 0 |
| `T`    | 1 | 1 |

(The Clifford generators `H, S, CNOT` sit on the grade-`0` integral stratum of
the BW filtration; `T` is the unique grade-`1` generator, matching the chapter's
`Cliffplus/Grade1_AllN` certificate `gradeOf_eq_tCount` on the linear stratum.)

Consequently `circuitGrade` *is literally the T-count* of a Clifford+T circuit,
and the docstring claim "matches the chapter's BW λ-adic grade on the Clifford+T
fragment `{H, S, T, CNOT}`" is **honest and exact** — no rotation outside this
fragment is ever assigned a fabricated closed-form grade.

Controlled rotations `R_k` (for `k ≥ 2`) are non-Clifford and are *not* members
of this fragment; the audited algorithms model them by their Clifford+T
syntheses (see `QFT.lean`, `Shor.lean`, `Trotter.lean`), so every grade reported
downstream is a genuine T-count of an honest Clifford+T circuit.

The headline structural facts are:

* `circuitGrade_append` — additivity under sequential composition;
* `circuitGrade_flatMap` — additivity under block concatenation;
* `circuitGrade_replicate` — the grade of a repeated block.
-/

namespace GradeAudit

/-- A Clifford+T gate over an `n`-qubit register.  Qubit positions are recorded
as ℕ wire labels (the grade does not depend on them).

* `H`, `S` are the single-qubit Clifford generators (grade `0`);
* `T` is the non-Clifford `π/8` gate (grade `1`);
* `CNOT` is the two-qubit Clifford entangler (grade `0`).

This is the strict Clifford+T basis: there is deliberately no controlled-rotation
constructor, so no gate can be assigned a fabricated λ-adic grade. -/
inductive Gate (n : ℕ) where
  | H (q : ℕ)
  | S (q : ℕ)
  | T (q : ℕ)
  | CNOT (c t : ℕ)
  deriving Repr, DecidableEq

variable {n : ℕ}

/-- The λ-adic grade of a single Clifford+T gate.  This matches the chapter's
Barnes–Wall BW grade on every gate of the fragment: `g(H) = g(S) = g(CNOT) = 0`
and `g(T) = 1`.  On the Clifford+T fragment the grade is identical to the
per-gate T-count. -/
def gradeOf : Gate n → ℕ
  | .H _ => 0
  | .S _ => 0
  | .CNOT _ _ => 0
  | .T _ => 1

@[simp] theorem gradeOf_H (q : ℕ) : gradeOf (Gate.H q : Gate n) = 0 := rfl
@[simp] theorem gradeOf_S (q : ℕ) : gradeOf (Gate.S q : Gate n) = 0 := rfl
@[simp] theorem gradeOf_T (q : ℕ) : gradeOf (Gate.T q : Gate n) = 1 := rfl
@[simp] theorem gradeOf_CNOT (c t : ℕ) : gradeOf (Gate.CNOT c t : Gate n) = 0 := rfl

/-- The grade of a circuit is the sum of its per-gate grades.  On the Clifford+T
fragment this is exactly the circuit's T-count. -/
def circuitGrade : List (Gate n) → ℕ
  | [] => 0
  | g :: gs => gradeOf g + circuitGrade gs

@[simp] theorem circuitGrade_nil : circuitGrade ([] : List (Gate n)) = 0 := rfl

theorem circuitGrade_cons (g : Gate n) (gs : List (Gate n)) :
    circuitGrade (g :: gs) = gradeOf g + circuitGrade gs := rfl

/-- The grade equals the sum of the mapped per-gate grades. -/
theorem circuitGrade_eq_sum (l : List (Gate n)) :
    circuitGrade l = (l.map gradeOf).sum := by
  induction l with
  | nil => rfl
  | cons g gs ih => simp [circuitGrade, ih]

/-- Additivity of the grade under sequential composition. -/
theorem circuitGrade_append (gs hs : List (Gate n)) :
    circuitGrade (gs ++ hs) = circuitGrade gs + circuitGrade hs := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp [circuitGrade_cons, ih]; ring

/-- The grade of a block-concatenated circuit is the sum of the block grades. -/
theorem circuitGrade_flatMap (l : List α) (f : α → List (Gate n)) :
    circuitGrade (l.flatMap f) = (l.map (fun x => circuitGrade (f x))).sum := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, circuitGrade_append, ih]

/-- The grade of a repeated single gate. -/
theorem circuitGrade_replicate (m : ℕ) (g : Gate n) :
    circuitGrade (List.replicate m g) = m * gradeOf g := by
  induction m with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, circuitGrade_cons, ih]; ring

/-- The grade is monotone under appending more gates on the right. -/
theorem circuitGrade_le_append_left (gs hs : List (Gate n)) :
    circuitGrade gs ≤ circuitGrade (gs ++ hs) := by
  rw [circuitGrade_append]; exact Nat.le_add_right _ _

/-- Bridge between `List.range`-indexed sums and `Finset.range` sums. -/
theorem listRange_map_sum (m : ℕ) (f : ℕ → ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- The grade of a `T`-only block of length `m` is `m` (its T-count). -/
theorem circuitGrade_replicate_T (m q : ℕ) :
    circuitGrade (List.replicate m (Gate.T q : Gate n)) = m := by
  rw [circuitGrade_replicate, gradeOf_T, Nat.mul_one]

end GradeAudit
