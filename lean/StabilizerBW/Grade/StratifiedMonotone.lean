import StabilizerBW.Grade.StratifiedMonotone.PhysicalDensity
import StabilizerBW.Grade.StratifiedMonotone.PauliWeightEnumerator
import StabilizerBW.Grade.StratifiedMonotone.PauliWeightSupportStratum
import StabilizerBW.Grade.StratifiedMonotone.UpperBound
import StabilizerBW.Grade.StratifiedMonotone.Headline
import StabilizerBW.Grade.StratifiedMonotone.MagicStateCheck
import StabilizerBW.Grade.StratifiedMonotone.ComparisonBCHK
import StabilizerBW.Grade.StratifiedMonotone.FalsifiedBranch
import StabilizerBW.Grade.StratifiedMonotone.AxiomProbe

/-!
# StratifiedMonotone — corrected Pauli-weight-stratified upper bound on `C(ρ)`

Aggregator for the **corrected** module: a physical-density-operator, closed-form,
Pauli-weight-stratified upper bound on Dutta–Tushar's magic functional `C(ρ)`.

## Two corrections

1. **Wrong enumerator.**  the original draft transported the *linear-phase* grade GF `8·4^m·(1+z)^m`.  The correct
   object the Pauli `ℓ¹` functional sees is the **Pauli-weight enumerator** `(1 + 3z)^m`
   (`pauliWeightEnumerator_factorises`), with weight-`g` stratum cardinality `C(m,g)·3^g`
   (`pauliWeightStratumCardinality`).

2. **Vacuous carrier.**  the original unrestricted `QubitState` admitted `ρ_X = 1000`.  Here the state space
   is the **physical density operator** `PhysicalDensity m` (bounded characteristic coefficients
   `|χ_P| ≤ 1`, trace-one `χ_I = 1`), and the original falsifier is provably excluded
   (`r1_counterexample_excluded`).

## Headline

`C_ub_PauliWeight` : for every weight-`≤ g` stratified physical density operator,
`C(ρ) ≤ cUB_pw m g = (#{P : wt P ≤ g}) − 1 = (∑_{j≤g} C(m,j)·3^j) − 1`.

The proposed constant `C(m,g)·3^g / 2^m` is **not** a valid upper bound (it is strictly
smaller than the achievable value and false already for the identity contribution); the corrected
constant is the cumulative weight-stratum cardinality `cUB_pw`.  The single load-bearing carrier
`DensityPauliCoefficientBound` (the per-coefficient `ℓ^∞` bound) is *proved* unconditionally
(`densityPauliCoefficientBound_holds`), so the headline is unconditional.

## Contents

* `PhysicalDensity` : state space, `duttaTusharC`, Bloch–Pauli bridge, `|a_P| ≤ 1/2^m`.
* `PauliWeightEnumerator` : `(1+3z)^m` and stratum cardinality `C(m,g)·3^g`.
* `PauliWeightSupportStratum` : the weight-`≤ g` support stratification.
* `UpperBound` : `cUB_pw`, closed form, the Heisenberg–Weyl carriers.
* `Headline` : `C_ub_PauliWeight` (+ conditional `_via_HW`).
* `MagicStateCheck` : T-, GHZ-, W-state and a strict-stratum example.
* `ComparisonBCHK` : sharper than the unstratified BCHK dyadic bound.
* `FalsifiedBranch` : refutation hook and the naive-counterexample exclusion.
* `AxiomProbe` : axiom hygiene.
-/
