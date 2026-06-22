import StabilizerBW.SubsetParityBWBridge.BinomialEnum

/-!
# SubsetParityBWBridge — T7: the LaRacuente symmetric-transition equilibrium marginal

This file records the measurement-side input of the bridge.

LaRacuente, *Subset Parities* (Folder 3, Prop. `prop:symmetric-transitions`,
with connectivity probability `r = 1`) establishes that the symmetric bipartite
transition rules
`(00),(11) → ½(00)+½(11)` and `(10),(01) → ½(10)+½(01)`
drive any initial state to the equilibrium with uniform per-parity-vector
distribution `p(b̄) = 1/2^m` on `{0,1}^m`.

We *encode that equilibrium as a concrete distribution* `laracuenteEquilibrium`
(the uniform `b̄ ↦ 1/2^m`); the uniformity is the cited LaRacuente input.  The
marginal of the overall parity count `Σ_j b_j` is then a classical computation:
`ℙ(Σ_j b_j = k) = C(m, k)/2^m`, i.e. `Binomial(m, 1/2)`.

The named carrier `LaRacuenteSymmetricEquilibriumMarginal` packages this
marginal identity; `laracuente_carry` discharges it from the uniform
equilibrium and the binomial enumerator (T4).  It is a theorem, not an axiom.
-/

namespace SubsetParityBWBridge.LaRacuenteCarry

open Finset

/-- The LaRacuente symmetric-transition equilibrium distribution on `{0,1}^m`:
uniform `p(b̄) = 1/2^m` (LaRacuente, *Subset Parities*, Folder 3,
Prop. `prop:symmetric-transitions`, `r = 1`). -/
noncomputable def laracuenteEquilibrium (m : ℕ) : (Fin m → Bool) → ℚ :=
  fun _ => (1 : ℚ) / 2 ^ m

/-- The marginal of the overall parity count `Σ_j b_j` under the LaRacuente
equilibrium: the total equilibrium probability of parity vectors with exactly
`k` ones. -/
noncomputable def laracuenteMarginal (m k : ℕ) : ℚ :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin m → Bool =>
      (Finset.univ.filter (fun i => b i = true)).card = k), laracuenteEquilibrium m b

/-- The LaRacuente parity-count marginal is `Binomial(m, 1/2)`. -/
theorem laracuenteMarginal_eq (m k : ℕ) :
    laracuenteMarginal m k = (Nat.choose m k : ℚ) / 2 ^ m := by
  unfold laracuenteMarginal laracuenteEquilibrium
  rw [Finset.sum_const, SubsetParityBWBridge.BinomialEnum.parityVec_grade_count, nsmul_eq_mul,
    mul_one_div]

/-- **T7 carrier (named, literature-attributed; a theorem, not an axiom).**
The marginal of the overall parity count `Σ_j b_j` under the LaRacuente
symmetric-transition equilibrium is `Binomial(m, 1/2)`.

Attribution: LaRacuente, *Subset Parities*, Folder 3,
Prop. `prop:symmetric-transitions` (uniform equilibrium `p(b̄) = 1/2^m`),
composed with the classical binomial-marginal identity. -/
def LaRacuenteSymmetricEquilibriumMarginal (m : ℕ) : Prop :=
  ∀ k : ℕ, k ≤ m → laracuenteMarginal m k = (Nat.choose m k : ℚ) / 2 ^ m

/-- The carrier holds: discharged from the uniform equilibrium and the binomial
enumerator. -/
theorem laracuente_carry (m : ℕ) : LaRacuenteSymmetricEquilibriumMarginal m :=
  fun k _ => laracuenteMarginal_eq m k

end SubsetParityBWBridge.LaRacuenteCarry
