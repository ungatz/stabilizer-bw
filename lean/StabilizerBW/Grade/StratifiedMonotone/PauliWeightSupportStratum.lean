import StabilizerBW.Grade.StratifiedMonotone.PauliWeightEnumerator

/-!
# T3 — the Pauli-weight-support stratification

A physical density operator `ρ` lies in the **weight-`≤ g` stratum** when every Pauli string in the
support of its characteristic vector has weight `≤ g`.
-/

namespace BWGradeStratifiedMonotoneR2

open Finset

/-- `ρ` has **Pauli-weight support `≤ g`**: every Pauli with non-zero characteristic coefficient has
weight at most `g`. -/
def PauliWeightSupportLE (m g : ℕ) (ρ : PhysicalDensity m) : Prop :=
  ∀ P, ρ.1 P ≠ 0 → BWGradeOfPauli m P ≤ g

/-- The support stratum is **monotone** in `g`. -/
theorem PauliWeightSupportLE.mono {m g g' : ℕ} (h : g ≤ g') {ρ : PhysicalDensity m}
    (hρ : PauliWeightSupportLE m g ρ) : PauliWeightSupportLE m g' ρ :=
  fun P hP => le_trans (hρ P hP) h

/-- Every state has support `≤ m` (no Pauli has weight exceeding `m`). -/
theorem PauliWeightSupportLE.top {m : ℕ} (ρ : PhysicalDensity m) :
    PauliWeightSupportLE m m ρ := by
  intro P _
  unfold BWGradeOfPauli
  calc (Finset.univ.filter (fun i => P i ≠ 0)).card
      ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by simp

/-- **Grade-0 characterisation.** A state has support `≤ 0` iff its only non-zero coefficient is at
the identity Pauli. -/
theorem PauliWeightSupportLE_zero_iff {m : ℕ} (ρ : PhysicalDensity m) :
    PauliWeightSupportLE m 0 ρ ↔ ∀ P, P ≠ pauliId m → ρ.1 P = 0 := by
  constructor
  · intro h P hP
    by_contra hne
    have := h P hne
    have hw : BWGradeOfPauli m P = 0 := Nat.le_zero.1 this
    apply hP
    unfold BWGradeOfPauli at hw
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hw
    funext i
    have := hw (Finset.mem_univ i)
    simpa [pauliId] using this
  · intro h P hP
    by_contra hgt
    have hne : P ≠ pauliId m := by
      rintro rfl
      simp at hgt
    exact hP (h P hne)

/-- Cardinality of the cumulative weight-`≤ g` stratum. -/
def pauliWeightLECard (m g : ℕ) : ℕ :=
  (Finset.univ.filter (fun P : PauliIdx m => BWGradeOfPauli m P ≤ g)).card

/-- The identity Pauli is always in the cumulative stratum, so its cardinality is at least `1`. -/
theorem one_le_pauliWeightLECard (m g : ℕ) : 1 ≤ pauliWeightLECard m g := by
  unfold pauliWeightLECard
  apply Finset.card_pos.2
  exact ⟨pauliId m, by simp [BWGradeOfPauli, pauliId]⟩

end BWGradeStratifiedMonotoneR2
