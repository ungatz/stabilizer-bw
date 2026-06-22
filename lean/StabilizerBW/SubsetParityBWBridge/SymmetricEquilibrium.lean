import StabilizerBW.SubsetParityBWBridge.BinomialEnum

/-!
# SubsetParityBWBridge — T7: the the symmetric Ehrenfest urn symmetric-transition equilibrium marginal

This file records the measurement-side input of the bridge.

the standard reference (Saloff-Coste 1997 §3), (see Saloff-Coste 1997 §3)
with connectivity probability `r = 1`) establishes that the symmetric bipartite
transition rules
`(00),(11) → ½(00)+½(11)` and `(10),(01) → ½(10)+½(01)`
drive any initial state to the equilibrium with uniform per-parity-vector
distribution `p(b̄) = 1/2^m` on `{0,1}^m`.

We *encode that equilibrium as a concrete distribution* `symmetricEquilibrium`
(the uniform `b̄ ↦ 1/2^m`); the uniformity is the cited the symmetric Ehrenfest urn input.  The
marginal of the overall parity count `Σ_j b_j` is then a classical computation:
`ℙ(Σ_j b_j = k) = C(m, k)/2^m`, i.e. `Binomial(m, 1/2)`.

The named carrier `SymmetricEquilibriumMarginal` packages this
marginal identity; `symmetric_chain_carrier` discharges it from the uniform
equilibrium and the binomial enumerator .  It is a theorem, not an axiom.
-/

namespace SubsetParityBWBridge.SymmetricEquilibrium

open Finset

/-- The the symmetric Ehrenfest urn symmetric-transition equilibrium distribution on `{0,1}^m`:
uniform `p(b̄) = 1/2^m` (Saloff-Coste 1997 §3,
(see Saloff-Coste 1997 §3) `r = 1`). -/
noncomputable def symmetricEquilibrium (m : ℕ) : (Fin m → Bool) → ℚ :=
  fun _ => (1 : ℚ) / 2 ^ m

/-- The marginal of the overall parity count `Σ_j b_j` under the the symmetric Ehrenfest urn
equilibrium: the total equilibrium probability of parity vectors with exactly
`k` ones. -/
noncomputable def symmetricEquilibriumMarginal (m k : ℕ) : ℚ :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin m → Bool =>
      (Finset.univ.filter (fun i => b i = true)).card = k), symmetricEquilibrium m b

/-- The the symmetric Ehrenfest urn parity-count marginal is `Binomial(m, 1/2)`. -/
theorem symmetricEquilibriumMarginal_eq (m k : ℕ) :
    symmetricEquilibriumMarginal m k = (Nat.choose m k : ℚ) / 2 ^ m := by
  unfold symmetricEquilibriumMarginal symmetricEquilibrium
  rw [Finset.sum_const, SubsetParityBWBridge.BinomialEnum.parityVec_grade_count, nsmul_eq_mul,
    mul_one_div]

/-- **T7 carrier (named, literature-attributed; a theorem, not an axiom).**
The marginal of the overall parity count `Σ_j b_j` under the the symmetric Ehrenfest urn
symmetric-transition equilibrium is `Binomial(m, 1/2)`.

Attribution: Saloff-Coste 1997 §3,
(see Saloff-Coste 1997 §3) = 1/2^m`),
composed with the classical binomial-marginal identity. -/
def SymmetricEquilibriumMarginal (m : ℕ) : Prop :=
  ∀ k : ℕ, k ≤ m → symmetricEquilibriumMarginal m k = (Nat.choose m k : ℚ) / 2 ^ m

/-- The carrier holds: discharged from the uniform equilibrium and the binomial
enumerator. -/
theorem symmetric_chain_carrier (m : ℕ) : SymmetricEquilibriumMarginal m :=
  fun k _ => symmetricEquilibriumMarginal_eq m k

end SubsetParityBWBridge.SymmetricEquilibrium
