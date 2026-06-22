import StabilizerBW.Grade.Comparisons.Incomparability.PauliMatrices

/-!
# The Pauli commutant cardinality and the Jiang–Wang nullity

For an `n`-qubit **diagonal** unitary `U = diagonal d`, conjugation by `U` fixes the
column-support of every Pauli, so the projective Pauli group element `U · P · U†` is
again a projective Pauli **iff** the entrywise conjugate `conjDiag d P` equals a phase
multiple `φ · Q` of some Pauli `Q` (`φ ∈ {±1, ±i}`).  By `conjDiag_eq` this entrywise
form is the genuine matrix triple product, so the predicate `IsInPauliImage` below is an
honest statement about matrix conjugation.

`pauliCommutantCard U` enumerates the `4^n` projective Paulis `P` and counts those whose
genuine conjugate `U · P · U†` is again a projective Pauli.  By the bijectivity of
`P ↦ U P U†` this is exactly `|U·𝒫ₙ·U† ∩ 𝒫ₙ|`, the order of the stabilised Pauli
subgroup entering the Jiang–Wang nullity.

`jiangWangNullity n c = 2n − log₂ c` is the literal Jiang–Wang unitary
stabilizer-nullity (`= GradeAudit.stabilizerNullity n c` definitionally).
-/

namespace GradeNullityComparison

open Roots

/-- `U · P · U†` (for `U = diagonal d`, `d = diag U`) is a projective Pauli, i.e. equals a
phase multiple `φ · (X^a Z^b)` with `φ ∈ {±1, ±i}`.  By `conjDiag_eq` the left-hand side
is the genuine matrix triple product `diagonal d * P * diagonal (conj ∘ d)`. -/
def IsInPauliImage {N : ℕ} (U P : Matrix (Fin N) (Fin N) Z8) : Prop :=
  ∃ a b : ℕ, ∃ φ ∈ phasesZ,
    conjDiag N (fun k => U k k) P = smulM N φ (pauliMat N a b)

/-- Boolean (kernel-computable) test that the conjugate of the `i`-th Pauli by the diagonal
of `U` is again a projective Pauli (phase multiple of some enumerated Pauli). -/
def inPauliImageB {N : ℕ} (U : Matrix (Fin N) (Fin N) Z8) (i : Fin (N * N)) : Bool :=
  let d : Fin N → Z8 := fun k => U k k
  let R := conjDiag N d (pauliMat N (i.val / N) (i.val % N))
  (List.finRange (N * N)).any (fun j => phasesZ.any (fun φ =>
     decide (R = smulM N φ (pauliMat N (j.val / N) (j.val % N)))))

/-- The Pauli-image commutant cardinality of a diagonal unitary `U` on dimension `N = 2^n`:
the number of projective Paulis `P` (out of `4^n = N·N`) whose genuine conjugate
`U · P · U†` is again a projective Pauli.  Equals `|U·𝒫ₙ·U† ∩ 𝒫ₙ|`. -/
def pauliCommutantCard {N : ℕ} (U : Matrix (Fin N) (Fin N) Z8) : ℕ :=
  (Finset.univ.filter (fun i : Fin (N * N) => inPauliImageB U i = true)).card

/-- The literal Jiang–Wang / Beverland unitary stabilizer-nullity
`ν(U) = 2n − log₂ c`, `c = |U·𝒫ₙ·U† ∩ 𝒫ₙ|`.  Identical formula to
`GradeAudit.stabilizerNullity`. -/
def jiangWangNullity (n c : ℕ) : ℕ := 2 * n - Nat.log2 c

end GradeNullityComparison
