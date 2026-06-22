import StabilizerBW.Roots.Filtration

/-!
# Priority 4 — `T`-count ≥ grade, for the integral fragment

We carry out the syntactic induction of Priority 4 for words over the *integral*
single-qubit generators `{S, X, T}` (the Clifford generators `S`, `X` are lattice
automorphisms of grade `0`; the non-Clifford `T` has grade `1`).  Using the
sub-multiplicativity `g(M·N) ≤ g(M) + g(N)` (Priority 2(a)) we prove, by induction on
the word,

  `g(⟦w⟧) ≤ #T(w)`,

and we exhibit the sharp instance `g(⟦[T]⟧) = #T([T]) = 1`.

The half-integral Hadamard `H` is excluded here because the present `grade`/`MapsToL`
machinery is for integral `2×2` matrices; the `H`-inclusive statement is discussed in
`Proofs/ArithmeticOfRoots.md`.
-/

namespace Roots
open Z8 Mat2

/-! ## Grades of the integral generators -/

theorem S_gradeLE_zero : gradeLE S 0 := by
  unfold gradeLE; simp only [pow_zero, smul_one_mat]
  apply mapsToL_of_gens <;> decide

theorem X_gradeLE_zero : gradeLE X 0 := by
  unfold gradeLE; simp only [pow_zero, smul_one_mat]
  apply mapsToL_of_gens <;> decide

theorem II_gradeLE_zero : gradeLE II 0 := by
  unfold gradeLE; simp only [pow_zero, smul_one_mat]
  apply mapsToL_of_gens <;> decide

theorem grade_S : grade S = 0 := grade_eq_zero S_gradeLE_zero
theorem grade_X : grade X = 0 := grade_eq_zero X_gradeLE_zero
theorem grade_II : grade II = 0 := grade_eq_zero II_gradeLE_zero

/-! ## Words over the integral generators `{S, X, T}` -/

/-- The integral single-qubit generators. -/
inductive Gen | S | X | T
deriving DecidableEq, Repr

/-- Matrix semantics of a generator. -/
def Gen.toMat : Gen → Mat2
  | .S => Mat2.S
  | .X => Mat2.X
  | .T => Mat2.T

/-- The `T`-count of a generator. -/
def Gen.tcount : Gen → ℕ
  | .T => 1
  | _ => 0

/-- Each generator's grade is bounded by its `T`-count. -/
theorem Gen.grade_le : ∀ g : Gen, grade g.toMat ≤ g.tcount
  | .S => by simp [Gen.toMat, Gen.tcount, grade_S]
  | .X => by simp [Gen.toMat, Gen.tcount, grade_X]
  | .T => by simp [Gen.toMat, Gen.tcount, grade_T]

/-- Matrix semantics of a word (left-to-right product). -/
def denote : List Gen → Mat2
  | [] => II
  | g :: w => g.toMat * denote w

/-- The `T`-count of a word. -/
def tcount : List Gen → ℕ
  | [] => 0
  | g :: w => g.tcount + tcount w

/-- **Priority 4 (integral fragment): `g(⟦w⟧) ≤ #T(w)`.** -/
theorem grade_denote_le : ∀ w : List Gen, grade (denote w) ≤ tcount w
  | [] => by simp [denote, tcount, grade_II]
  | g :: w => by
      simp only [denote, tcount]
      calc grade (g.toMat * denote w)
          ≤ grade g.toMat + grade (denote w) := grade_mul _ _
        _ ≤ g.tcount + tcount w := Nat.add_le_add (Gen.grade_le g) (grade_denote_le w)

/-- Sharpness: the single-`T` word has grade exactly equal to its `T`-count. -/
theorem grade_denote_T_sharp : grade (denote [Gen.T]) = tcount [Gen.T] := by
  simp only [denote, tcount, Gen.tcount, Gen.toMat]
  rw [show Mat2.T * II = Mat2.T by decide]
  exact grade_T

end Roots
