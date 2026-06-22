import StabilizerBW.Grade.Comparisons.Incomparability.PauliCommutant

/-!
# T4 — Second witness: the Toffoli-`Z` gate `CCZ` at `n = 3`

`CCZ = diag(1, 1, 1, 1, 1, 1, 1, -1)` on `3` qubits.  We compute, by one-by-one
enumeration of all `64` projective Paulis at `n = 3` and direct (matrix) conjugation, that

  `|CCZ · 𝒫₃ · CCZ† ∩ 𝒫₃| = 8`,

i.e. exactly the eight diagonal (`Z`-only) Paulis survive conjugation; every Pauli with an
`X`/`Y` component leaves the Pauli group.  (Concretely `CCZ · X₁ · CCZ† = X₁ · CZ₂₃`, which
is Clifford but **not** a single Pauli: its sign pattern `(-1)^{q₂q₃}` is quadratic, not the
affine `(-1)^{b·c}` of a Pauli.)  Hence the Jiang–Wang nullity is

  `ν(CCZ) = 2·3 − log₂ 8 = 6 − 3 = 3`.

The enumeration is `decide`-checked over `ℤ[ζ₈]` (no `native_decide`); by the injection
`ℤ[ζ₈] ↪ ℂ` it is the genuine complex value.
-/

namespace GradeAuditIncomparable

open Roots

/-- The diagonal of the `CCZ` (Toffoli-`Z`) gate on `3` qubits: `(1,…,1,-1)`. -/
def dCCZ : Fin 8 → Z8 := fun i => if i = 7 then (-1) else 1

/-- The `CCZ` unitary `diag(1,1,1,1,1,1,1,-1)` on `3` qubits, over `ℤ[ζ₈]`. -/
def CCZMatrix : Matrix (Fin 8) (Fin 8) Z8 := Matrix.diagonal dCCZ

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The commutant cardinality of `CCZ` is exactly `8`**, derived by direct one-by-one
conjugation of all `64` projective Paulis at `n = 3`. -/
theorem CCZ_commutantCard : pauliCommutantCard CCZMatrix = 8 := by
  decide

/-- **Jiang–Wang nullity of `CCZ` equals `3`.** -/
theorem CCZ_nullity : jiangWangNullity 3 (pauliCommutantCard CCZMatrix) = 3 := by
  rw [CCZ_commutantCard]; decide

end GradeAuditIncomparable
