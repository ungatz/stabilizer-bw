import Mathlib

/-!
# the physical-density-operator state space (Pauli-coefficient encoding)

This is the **corrected** state space for the Pauli-weight-stratified upper bound on the
Dutta–Tushar magic functional `C(ρ)`.

## The the corrected correction (vs the rejected the naive carrier)

The original construction used `QubitState m := PauliIdx m → ℝ` with NO constraint, which made the carrier
vacuously falsifiable (take `ρ_X = 1000` at `m = g = 1`).  Here we restrict to a genuine
**physical-density-operator** encoding: a density operator `ρ` on `m` qubits is represented by its
Pauli **characteristic vector** `χ_P := Tr(ρ · P)`, which for any density operator satisfies

* the **trace-one** normalisation `χ_I = Tr(ρ) = 1` at the identity Pauli, and
* the **Heisenberg–Weyl coefficient bound** `|χ_P| = |Tr(ρ · P)| ≤ ‖ρ‖₁ · ‖P‖_op = 1`
  (each single Pauli is a unitary, hence `‖P‖_op = 1`, and `‖ρ‖₁ = 1` for a density operator).

These two conditions are *necessary* for physicality and are exactly the load-bearing facts for
the upper bound; full positivity (the Bloch-ball constraint `∑_{P≠I} a_P² ≤ a_I²`) is a strictly
stronger condition that turns out **not** to be needed for the bound, so we do not impose it (a
cleaner, more general statement).

The genuine *expansion* coefficients in `ρ = (1/2^m) ∑_P χ_P · P` are `a_P = χ_P / 2^m`, recorded
by `blochPauliCoeff`; the bridge `Bloch_to_Pauli_coefficient_bridge` connects the two encodings and
yields the Aaronson–Gottesman / MacWilliams–Sloane per-coefficient bound `|a_P| ≤ 1/2^m`.
-/

namespace StratifiedMonotone

open Finset

/-- A Pauli index on `m` qubits: a tensor factor in `{I, X, Y, Z}` for each qubit, encoded as
`Fin 4` per site with `0 = I`, `1 = X`, `2 = Y`, `3 = Z`. -/
abbrev PauliIdx (m : ℕ) : Type := Fin m → Fin 4

/-- The identity Pauli `I^{⊗m}` (all sites `I`). -/
def pauliId (m : ℕ) : PauliIdx m := fun _ => 0

/-- The **Barnes–Wall / Pauli weight** of a Pauli string: the number of non-identity tensor
factors. -/
def BWGradeOfPauli (m : ℕ) (P : PauliIdx m) : ℕ :=
  (Finset.univ.filter (fun i => P i ≠ 0)).card

@[simp] theorem BWGradeOfPauli_id (m : ℕ) : BWGradeOfPauli m (pauliId m) = 0 := by
  simp [BWGradeOfPauli, pauliId]

/-- A **physical density operator** on `m` qubits, encoded by its Pauli characteristic vector
`χ_P = Tr(ρ · P)`: bounded coefficients (`|χ_P| ≤ 1`) and trace-one normalisation (`χ_I = 1`). -/
def PhysicalDensity (m : ℕ) : Type :=
  {coeff : PauliIdx m → ℝ // (∀ P, |coeff P| ≤ 1) ∧ coeff (pauliId m) = 1}

namespace PhysicalDensity

/-- The characteristic vector `χ_P = Tr(ρ · P)`. -/
def coeff {m : ℕ} (ρ : PhysicalDensity m) : PauliIdx m → ℝ := ρ.1

theorem abs_coeff_le_one {m : ℕ} (ρ : PhysicalDensity m) (P : PauliIdx m) :
    |ρ.1 P| ≤ 1 := ρ.2.1 P

theorem coeff_id {m : ℕ} (ρ : PhysicalDensity m) : ρ.1 (pauliId m) = 1 := ρ.2.2

end PhysicalDensity

/-- The **maximally mixed state** `I/2^m`: `χ_I = 1`, all other coefficients `0`.  Witnesses that
`PhysicalDensity m` is inhabited (the carrier is NOT vacuous). -/
def maximallyMixed (m : ℕ) : PhysicalDensity m :=
  ⟨fun P => if P = pauliId m then 1 else 0, by
    refine ⟨fun P => ?_, by simp⟩
    by_cases h : P = pauliId m <;> simp [h]⟩

instance (m : ℕ) : Inhabited (PhysicalDensity m) := ⟨maximallyMixed m⟩

/-- The genuine **Bloch–Pauli expansion coefficient** `a_P = χ_P / 2^m` in
`ρ = (1/2^m) ∑_P χ_P · P`. -/
noncomputable def blochPauliCoeff {m : ℕ} (ρ : PhysicalDensity m) (P : PauliIdx m) : ℝ :=
  ρ.1 P / 2 ^ m

/-- **Bridge.**  The Bloch–Pauli expansion coefficient is the characteristic coefficient divided by
the Hilbert-space dimension `2^m`. -/
theorem Bloch_to_Pauli_coefficient_bridge {m : ℕ} (ρ : PhysicalDensity m) (P : PauliIdx m) :
    blochPauliCoeff ρ P = ρ.1 P / 2 ^ m := rfl

/-- **Heisenberg–Weyl per-coefficient bound** (Aaronson–Gottesman / MacWilliams–Sloane): every
expansion coefficient of a density operator is bounded by `1/2^m`.  Proved unconditionally at `d = 2`
from `|χ_P| ≤ 1`. -/
theorem pauli_coefficient_le_one_over_d {m : ℕ} (ρ : PhysicalDensity m) (P : PauliIdx m) :
    |blochPauliCoeff ρ P| ≤ 1 / 2 ^ m := by
  rw [Bloch_to_Pauli_coefficient_bridge, abs_div,
    abs_of_pos (show (0 : ℝ) < 2 ^ m by positivity)]
  gcongr
  exact ρ.2.1 P

/-- The **Dutta–Tushar magic functional** `C(ρ) = ‖ρ‖₁^{Pauli} − 1`, where the Pauli `ℓ¹` norm is
`∑_P |Tr(ρ · P)| = ∑_P |χ_P|` and the `−1` removes the maximally-mixed baseline (which contributes
exactly the identity term `|χ_I| = 1`). -/
noncomputable def duttaTusharC {m : ℕ} (ρ : PhysicalDensity m) : ℝ :=
  (∑ P : PauliIdx m, |ρ.1 P|) - 1

/-- `C(ρ)` equals the sum of the absolute values of the **non-identity** characteristic
coefficients (the identity term `|χ_I| = 1` cancels the baseline). -/
theorem duttaTusharC_eq_sum_nonId {m : ℕ} (ρ : PhysicalDensity m) :
    duttaTusharC ρ = ∑ P ∈ Finset.univ.filter (fun P => P ≠ pauliId m), |ρ.1 P| := by
  unfold duttaTusharC
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun P => P ≠ pauliId m) (fun P => |ρ.1 P|)]
  have hfilter : (Finset.univ.filter (fun P : PauliIdx m => ¬ P ≠ pauliId m))
      = {pauliId m} := by
    ext P; simp
  rw [hfilter, Finset.sum_singleton, ρ.2.2]
  simp

/-- `C(ρ) ≥ 0`: the magic functional is non-negative. -/
theorem duttaTusharC_nonneg {m : ℕ} (ρ : PhysicalDensity m) : 0 ≤ duttaTusharC ρ := by
  rw [duttaTusharC_eq_sum_nonId]
  apply Finset.sum_nonneg
  intro P _
  exact abs_nonneg _

/-- The maximally mixed state has zero magic. -/
@[simp] theorem duttaTusharC_maximallyMixed (m : ℕ) :
    duttaTusharC (maximallyMixed m) = 0 := by
  rw [duttaTusharC_eq_sum_nonId]
  apply Finset.sum_eq_zero
  intro P hP
  simp only [Finset.mem_filter] at hP
  simp [maximallyMixed, hP.2]

end StratifiedMonotone
