import Mathlib
import StabilizerBW.Roots.Core

/-!
# T1 — Concrete Pauli matrices over the computable ring `ℤ[ζ₈]`

This file gives concrete, **computable** matrix representations of the `n`-qubit
projective Pauli group (the Pauli group modulo the phase subgroup `{±1, ±i}`),
realised over the ring `R = ℤ[ζ₈]` (`Roots.Z8`).

## Why `ℤ[ζ₈]` and not `ℂ`?

Every matrix entry that appears in the Pauli-image computation of this development is
a root of unity living in `ℤ[ζ₈]`:

* single-qubit Pauli entries are `0, ±1, ±i` (here `i = ζ₈²`);
* the diagonal of the controlled-`T` gate is `1, 1, 1, ζ₈`;
* the diagonal of `CCZ` is `1, …, 1, -1`;
* the global phases `{±1, ±i}` modded out by the projective group.

Since the inclusion `ℤ[ζ₈] ↪ ℂ` is an injective ring homomorphism, a matrix
equation `U · P · U† = φ · Q` holds over `ℤ[ζ₈]` **iff** it holds over `ℂ`.  Hence
the Pauli-image cardinalities computed here over `ℤ[ζ₈]` are exactly the genuine
complex Pauli-image cardinalities.  Working over `ℤ[ζ₈]` (which has decidable
equality and a kernel-reducible `CommRing` structure) is what makes the one-by-one
enumeration **`decide`-checkable without `native_decide`**.

## Encoding

A projective Pauli on `n` qubits (dimension `N = 2^n`) is encoded by a symplectic
pair `(a, b)` of bit-masks `< N`:

  `pauliMat N a b = X^a Z^b`,  with entry `(r, c) = [c = r ⊕ a] · (-1)^{b·c}`.

As `(a, b)` range over `{0,…,N-1}²` this enumerates the `4^n` projective Paulis
(note `Y ≡ X Z` modulo phase, so no separate `i`-phase is needed in the entries:
every nonzero entry is `±1`).
-/

namespace GradeAuditIncomparable

open Roots

/-- Parity of the set bits of `x` (enough bits for all `n ≤ 7` here). -/
def bitParity (x : ℕ) : Bool :=
  (List.range 16).foldr (fun k acc => xor (Nat.testBit x k) acc) false

/-- The `±1` sign `(-1)^{b·c}` of the `Z`-part `b` against column `c`. -/
def zsign (b c : ℕ) : Z8 := if bitParity (b &&& c) then (-1) else 1

/-- The projective Pauli matrix `X^a Z^b` on dimension `N = 2^n`, with entry
`(r, c) = [c = r ⊕ a] · (-1)^{b·c}`.  All nonzero entries are `±1`. -/
def pauliMat (N a b : ℕ) : Matrix (Fin N) (Fin N) Z8 :=
  fun r c => if c.val = r.val ^^^ a then zsign b c.val else 0

/-! ## Single-qubit Paulis (dimension `2`) -/

/-- The single-qubit identity `I = X⁰ Z⁰`. -/
def pauliI : Matrix (Fin 2) (Fin 2) Z8 := pauliMat 2 0 0
/-- The single-qubit `X = X¹ Z⁰`. -/
def pauliX : Matrix (Fin 2) (Fin 2) Z8 := pauliMat 2 1 0
/-- The single-qubit `Z = X⁰ Z¹`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) Z8 := pauliMat 2 0 1
/-- The single-qubit `Y`, represented modulo phase by `X Z = X¹ Z¹`
(`Y = i · X Z`, equal mod the phase subgroup). -/
def pauliY : Matrix (Fin 2) (Fin 2) Z8 := pauliMat 2 1 1

example : pauliI = !![1, 0; 0, 1] := by decide
example : pauliX = !![0, 1; 1, 0] := by decide
example : pauliZ = !![1, 0; 0, (-1)] := by decide
example : pauliY = !![0, (-1); 1, 0] := by decide

/-- Kronecker (tensor) product of two Pauli matrices, the standard way to build
multi-qubit Paulis from single-qubit ones. -/
def pauliTensor {m n : ℕ} (A : Matrix (Fin m) (Fin m) Z8)
    (B : Matrix (Fin n) (Fin n) Z8) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) Z8 :=
  Matrix.kroneckerMap (· * ·) A B

/-- The `16` projective Paulis on `n = 2` qubits (dimension `4`). -/
def enumeratePauli2 (i : Fin 16) : Matrix (Fin 4) (Fin 4) Z8 :=
  pauliMat 4 (i.val / 4) (i.val % 4)

/-- The `64` projective Paulis on `n = 3` qubits (dimension `8`). -/
def enumeratePauli3 (i : Fin 64) : Matrix (Fin 8) (Fin 8) Z8 :=
  pauliMat 8 (i.val / 8) (i.val % 8)

/-! ## Diagonal conjugation as a genuine matrix triple product

For a *diagonal* unitary `diagonal d`, conjugation acts entrywise:
`(diagonal d · P · (diagonal d)†)_{r,c} = d_r · P_{r,c} · conj(d_c)`.
`conjDiag` packages this entrywise form (which is cheap to `decide`), and
`conjDiag_eq` proves it equals the genuine Mathlib matrix triple product
`diagonal d * P * diagonal (conj ∘ d)` — i.e. honest matrix conjugation by the
diagonal unitary, whose conjugate-transpose is `diagonal (conj ∘ d)`. -/

/-- Entrywise diagonal conjugation `(diag d · P · (diag d)†)_{r,c} = d_r P_{r,c} conj(d_c)`. -/
def conjDiag (N : ℕ) (d : Fin N → Z8) (P : Matrix (Fin N) (Fin N) Z8) :
    Matrix (Fin N) (Fin N) Z8 :=
  fun r c => d r * P r c * Z8.conj (d c)

/-- **Honesty bridge:** the entrywise `conjDiag` is *exactly* the genuine matrix
triple product `diagonal d * P * diagonal (conj ∘ d)`, the conjugation of `P` by
the diagonal unitary `diagonal d` (whose conjugate-transpose is
`diagonal (conj ∘ d)`). -/
theorem conjDiag_eq (N : ℕ) (d : Fin N → Z8) (P : Matrix (Fin N) (Fin N) Z8) :
    conjDiag N d P
      = Matrix.diagonal d * P * Matrix.diagonal (fun i => Z8.conj (d i)) := by
  apply Matrix.ext; intro r c
  simp only [conjDiag, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- Scalar (phase) multiple of a matrix, `(φ • Q)_{r,c} = φ · Q_{r,c}`. -/
def smulM (N : ℕ) (φ : Z8) (Q : Matrix (Fin N) (Fin N) Z8) :
    Matrix (Fin N) (Fin N) Z8 :=
  fun r c => φ * Q r c

/-- The four global phases of the projective Pauli group: `1, -1, i, -i`. -/
def phasesZ : List Z8 := [1, -1, ⟨0, 0, 1, 0⟩, ⟨0, 0, -1, 0⟩]

end GradeAuditIncomparable
