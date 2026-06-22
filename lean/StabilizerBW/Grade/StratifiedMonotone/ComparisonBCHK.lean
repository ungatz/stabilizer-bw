import StabilizerBW.Grade.StratifiedMonotone.Headline

/-!
# T7 — comparison with the unstratified BCHK dyadic monotone bound

The Beverland–Campbell–Howard–Kliuchnikov dyadic monotone (= Pauli-spectrum `ℓ¹` at `d = 2`) gives,
without any weight stratification, the bound `C(ρ) ≤ 4^m − 1` (all `4^m` Paulis can contribute, each
with `|χ_P| ≤ 1`, minus the identity baseline).  The Pauli-weight-stratified bound `cUB_pw m g` is
**sharper**: it only counts the `≤ g`-weight strata.
-/

namespace BWGradeStratifiedMonotoneR2

open Finset

/-- The unstratified **BCHK dyadic monotone upper bound** `4^m − 1`. -/
noncomputable def bchkDyadicUB (m : ℕ) : ℝ := (4 : ℝ) ^ m - 1

/-- The cumulative weight-`≤ g` stratum cardinality never exceeds the total `4^m` Paulis. -/
theorem pauliWeightLECard_le (m g : ℕ) : pauliWeightLECard m g ≤ 4 ^ m := by
  unfold pauliWeightLECard
  calc (Finset.univ.filter (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g)).card
      ≤ (Finset.univ : Finset (PauliIdx m)).card := Finset.card_filter_le _ _
    _ = 4 ^ m := by simp [PauliIdx]

/-- **The Pauli-weight-stratified bound is sharper than the BCHK dyadic bound.**  (The hypothesis
`g ≤ m` is from the structural strawman's requested signature; the inequality in fact holds for all `g`.) -/
theorem cUB_pw_sharper_than_BCHK (m g : ℕ) (_h : g ≤ m) :
    cUB_pw m g ≤ bchkDyadicUB m := by
  unfold cUB_pw bchkDyadicUB
  have h := pauliWeightLECard_le m g
  have : (pauliWeightLECard m g : ℝ) ≤ (4 : ℝ) ^ m := by
    have : ((4 : ℕ) ^ m : ℝ) = (4 : ℝ) ^ m := by push_cast; ring
    rw [← this]; exact_mod_cast h
  linarith

/-- Combined: every weight-`≤ g` stratified physical density operator also satisfies the (weaker)
BCHK dyadic bound, via the sharper Pauli-weight bound. -/
theorem C_le_BCHK_via_PauliWeight (m g : ℕ) (ρ : PhysicalDensity m)
    (hs : PauliWeightSupportLE m g ρ) (h : g ≤ m) :
    duttaTusharC ρ ≤ bchkDyadicUB m :=
  le_trans (C_ub_PauliWeight m g ρ hs) (cUB_pw_sharper_than_BCHK m g h)

end BWGradeStratifiedMonotoneR2
