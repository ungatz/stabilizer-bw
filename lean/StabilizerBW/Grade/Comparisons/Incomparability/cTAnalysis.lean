import StabilizerBW.Grade.Comparisons.Incomparability.PauliCommutant

/-!
# First witness: the controlled-`T` gate `cT` at `n = 2`

`cT = diag(1, 1, 1, ζ₈)` on `2` qubits.  We compute, by one-by-one enumeration of all
`16` projective Paulis at `n = 2` and direct (matrix) conjugation, that

  `|cT · 𝒫₂ · cT† ∩ 𝒫₂| = 4`,

i.e. exactly the four diagonal (`Z`-only) Paulis `{I, Z₁, Z₂, Z₁Z₂}` survive conjugation;
every Pauli with an `X`/`Y` component leaves the Pauli group (it picks up a `ζ₈`-phase off
the diagonal).  Hence the Jiang–Wang nullity is

  `ν(cT) = 2·2 − log₂ 4 = 4 − 2 = 2`.

The enumeration is `decide`-checked over `ℤ[ζ₈]` (no `native_decide`); by the injection
`ℤ[ζ₈] ↪ ℂ` it is the genuine complex value.
-/

namespace GradeNullityComparison

open Roots

/-- The diagonal of the controlled-`T` gate on `2` qubits: `(1, 1, 1, ζ₈)`. -/
def dCT : Fin 4 → Z8 := fun i => if i = 3 then Z8.zeta else 1

/-- The controlled-`T` unitary `cT = diag(1, 1, 1, ζ₈)` on `2` qubits, over `ℤ[ζ₈]`. -/
def cTMatrix : Matrix (Fin 4) (Fin 4) Z8 := Matrix.diagonal dCT

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The commutant cardinality of `cT` is exactly `4`**, derived by direct one-by-one
conjugation of all `16` projective Paulis at `n = 2`. -/
theorem cT_commutantCard : pauliCommutantCard cTMatrix = 4 := by
  decide

/-- **Jiang–Wang nullity of `cT` equals `2`.** -/
theorem cT_nullity : jiangWangNullity 2 (pauliCommutantCard cTMatrix) = 2 := by
  rw [cT_commutantCard]; decide

end GradeNullityComparison
