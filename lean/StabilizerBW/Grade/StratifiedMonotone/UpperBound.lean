import StabilizerBW.Grade.StratifiedMonotone.PauliWeightSupportStratum

/-!
# T4 — the closed-form upper-bound constant and the Heisenberg–Weyl carriers

## The corrected upper-bound constant

The original construction proposed the constant `C(m,g)·3^g / 2^m`.  This is **dimensionally wrong** and is
NOT a valid upper bound on the Dutta–Tushar functional (it is *strictly smaller* than the achievable
value, and is in fact false already for the identity contribution; see the structural note below).

The correct, honest, *provable* upper bound on `C(ρ) = ∑_{P} |χ_P| − 1` for a weight-`≤ g`
stratified physical density operator is the **cumulative weight-stratum cardinality minus the
identity baseline**:
```
  cUB_pw m g  =  (#{P : wt(P) ≤ g})  −  1
             =  (∑_{j=0}^{g} C(m,j)·3^j)  −  1 ,
```
each non-identity coefficient contributing at most `|χ_P| ≤ 1`.

## The carrier

`DensityPauliCoefficientBound` packages the single load-bearing fact — the per-coefficient bound
`|χ_P| ≤ 1` — as a named `Prop` strictly smaller than the headline (an `ℓ^∞` bound, not the
weight-stratified `ℓ¹` sum).  It is *proved* unconditionally (`densityPauliCoefficientBound_holds`),
so the conditional headline is, in fact, also unconditional.  `DensityPauliCoefficientBoundHW`
records the equivalent Heisenberg–Weyl normalisation `|a_P| ≤ 1/2^m` on the genuine expansion
coefficients.
-/

namespace BWGradeStratifiedMonotoneR2

open Finset

/-- **The corrected closed-form upper-bound constant.** -/
noncomputable def cUB_pw (m g : ℕ) : ℝ :=
  (pauliWeightLECard m g : ℝ) - 1

theorem cUB_pw_nonneg (m g : ℕ) : 0 ≤ cUB_pw m g := by
  unfold cUB_pw
  have := one_le_pauliWeightLECard m g
  have : (1 : ℝ) ≤ (pauliWeightLECard m g : ℝ) := by exact_mod_cast this
  linarith

/-
**Closed form for the cumulative stratum cardinality**: `#{P : wt(P) ≤ g} = ∑_{j≤g} C(m,j)·3^j`.
Follows from the per-stratum cardinality `pauliWeightStratumCardinality`.
-/
theorem pauliWeightLECard_closed_form (m g : ℕ) :
    pauliWeightLECard m g = ∑ j ∈ Finset.range (g + 1), Nat.choose m j * 3 ^ j := by
  unfold pauliWeightLECard;
  rw [ show ( Finset.univ.filter fun P : Fin m → Fin 4 => BWGradeOfPauli m P ≤ g ) = Finset.biUnion ( Finset.range ( g + 1 ) ) fun j => Finset.univ.filter fun P : Fin m → Fin 4 => BWGradeOfPauli m P = j from ?_, Finset.card_biUnion ];
  · exact Finset.sum_congr rfl fun i hi => pauliWeightStratumCardinality m i;
  · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x => by aesop;
  · ext; simp +decide ;

/-- **The load-bearing carrier** (Heisenberg–Weyl per-coefficient `ℓ^∞` bound): every characteristic
coefficient of a physical density operator is bounded by `1`.  Strictly smaller than the headline. -/
def DensityPauliCoefficientBound : Prop :=
  ∀ (m : ℕ) (ρ : PhysicalDensity m) (P : PauliIdx m), |ρ.1 P| ≤ 1

/-- The carrier is **proved** (it is exactly the physicality constraint). -/
theorem densityPauliCoefficientBound_holds : DensityPauliCoefficientBound :=
  fun _ ρ P => ρ.2.1 P

/-- **Heisenberg–Weyl form** of the carrier on the genuine expansion coefficients `a_P = χ_P/2^m`. -/
def DensityPauliCoefficientBoundHW : Prop :=
  ∀ (m : ℕ) (ρ : PhysicalDensity m) (P : PauliIdx m),
    P ≠ pauliId m → |blochPauliCoeff ρ P| ≤ 1 / 2 ^ m

/-- The Heisenberg–Weyl form of the carrier is **proved** (Aaronson–Gottesman normalisation). -/
theorem densityPauliCoefficientBoundHW_holds : DensityPauliCoefficientBoundHW :=
  fun _ ρ P _ => pauli_coefficient_le_one_over_d ρ P

end BWGradeStratifiedMonotoneR2