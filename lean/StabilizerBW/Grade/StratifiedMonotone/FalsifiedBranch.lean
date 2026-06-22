import StabilizerBW.Grade.StratifiedMonotone.Headline

/-!
# refutation hook and the exclusion of the original counterexample

The **refutation hook** `C_ub_PauliWeight_refuted_of_witness` records that no physical density
operator can violate the headline bound: any purported violating witness yields `False`.  This is the
falsification interface (the development/77 pattern) — a publishable separation would instantiate it, but
the headline proves it can never be instantiated on `PhysicalDensity`.

We also record explicitly that the **the naive counterexample** (`ρ_X = 1000` at `m = 1`), which falsified
the unrestricted naive carrier, is *excluded* by the physical-density encoding: no `PhysicalDensity`
has a coefficient of absolute value exceeding `1`.
-/

namespace StratifiedMonotone

open Finset

/-- **Refutation hook.**  A witness violating the headline bound is impossible: it yields `False`.
This certifies the bound cannot be separated on the physical-density state space. -/
theorem C_ub_PauliWeight_refuted_of_witness (m g : ℕ) (ρ : PhysicalDensity m)
    (hs : PauliWeightSupportLE m g ρ) (hgt : cUB_pw m g < duttaTusharC ρ) : False :=
  absurd (C_ub_PauliWeight m g ρ hs) (not_le.2 hgt)

/-- **The the naive counterexample is excluded.**  No physical density operator can carry an arbitrarily
large coefficient such as the original falsifier `ρ_X = 1000`: every coefficient satisfies `|χ_P| ≤ 1`. -/
theorem r1_counterexample_excluded {m : ℕ} (ρ : PhysicalDensity m) (P : PauliIdx m) :
    |ρ.1 P| ≤ 1 := ρ.2.1 P

/-- Consequently no physical density operator realises the original falsifier's coefficient value. -/
theorem no_density_with_coeff_1000 {m : ℕ} (ρ : PhysicalDensity m) (P : PauliIdx m) :
    ρ.1 P ≠ 1000 := by
  intro h
  have := r1_counterexample_excluded ρ P
  rw [h] at this
  norm_num at this

end StratifiedMonotone
