import StabilizerBW.Grade.StratifiedMonotone.Headline

/-!
# T6 — finite-`m` magic-state verification

We instantiate the headline bound on three standard families plus one genuinely weight-stratified
example, encoded by their Pauli characteristic vectors `χ_P = Tr(ρ · P)`:

* **T-state** `|T⟩` at `m = 1`: `χ = (I:1, X:√2/2, Y:√2/2, Z:0)`
  (from `|T⟩⟨T| = (I + cos(π/4)·X + sin(π/4)·Y)/2`, `cos(π/4) = sin(π/4) = √2/2`).
* **GHZ-state** `|GHZ₂⟩ = (|00⟩+|11⟩)/√2` at `m = 2`: `χ = (II:1, XX:1, YY:−1, ZZ:1)`.
* **W-state** `|W₂⟩ = (|01⟩+|10⟩)/√2` at `m = 2`: `χ = (II:1, XX:1, YY:1, ZZ:−1)`.
* A **genuinely stratified** density `(II + ½·ZI)/…` at `m = 2` with support `≤ 1 < 2 = m`.

For the three named states the natural Pauli-weight support is the full `g = m` (each contains a
maximal-weight Pauli term — e.g. `XX`, `YY`, `ZZ` for the Bell/GHZ/W families, `X^{⊗m}` for the
T-tensor), so the check is run at `g = m`; the stratified example exercises a strict `g < m` stratum.
Each check applies the unconditional headline `C_ub_PauliWeight`.
-/

namespace BWGradeStratifiedMonotoneR2

open Finset

theorem sqrt2_div_two_le_one : Real.sqrt 2 / 2 ≤ 1 := by
  have h : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-! ## T-state at `m = 1` -/

/-- The single-qubit T-magic-state characteristic vector. -/
noncomputable def tStateCoeff : PauliIdx 1 → ℝ := fun P =>
  if P = pauliId 1 then 1
  else if P = ![1] then Real.sqrt 2 / 2
  else if P = ![2] then Real.sqrt 2 / 2
  else 0

/-- The T-state as a physical density operator. -/
noncomputable def tState : PhysicalDensity 1 :=
  ⟨tStateCoeff, by
    refine ⟨fun P => ?_, ?_⟩
    · unfold tStateCoeff
      split_ifs
      · norm_num
      · rw [abs_of_nonneg (by positivity)]; exact sqrt2_div_two_le_one
      · rw [abs_of_nonneg (by positivity)]; exact sqrt2_div_two_le_one
      · norm_num
    · simp [tStateCoeff]⟩

/-- **T-state check** (`m = 1`, `g = 1`): the bound holds. -/
theorem tState_satisfies_bound : duttaTusharC tState ≤ cUB_pw 1 1 :=
  C_ub_PauliWeight 1 1 tState (PauliWeightSupportLE.top tState)

/-! ## GHZ-state at `m = 2` -/

/-- The 2-qubit GHZ (Bell `Φ⁺`) characteristic vector. -/
def ghzCoeff : PauliIdx 2 → ℝ := fun P =>
  if P = pauliId 2 then 1
  else if P = ![1, 1] then 1
  else if P = ![2, 2] then -1
  else if P = ![3, 3] then 1
  else 0

/-- The GHZ state as a physical density operator. -/
def ghzState : PhysicalDensity 2 :=
  ⟨ghzCoeff, by
    refine ⟨fun P => ?_, ?_⟩
    · unfold ghzCoeff; split_ifs <;> norm_num
    · simp [ghzCoeff]⟩

/-- **GHZ-state check** (`m = 2`, `g = 2`): the bound holds. -/
theorem ghzState_satisfies_bound : duttaTusharC ghzState ≤ cUB_pw 2 2 :=
  C_ub_PauliWeight 2 2 ghzState (PauliWeightSupportLE.top ghzState)

/-! ## W-state at `m = 2` -/

/-- The 2-qubit W (Bell `Ψ⁺`) characteristic vector. -/
def wCoeff : PauliIdx 2 → ℝ := fun P =>
  if P = pauliId 2 then 1
  else if P = ![1, 1] then 1
  else if P = ![2, 2] then 1
  else if P = ![3, 3] then -1
  else 0

/-- The W state as a physical density operator. -/
def wState : PhysicalDensity 2 :=
  ⟨wCoeff, by
    refine ⟨fun P => ?_, ?_⟩
    · unfold wCoeff; split_ifs <;> norm_num
    · simp [wCoeff]⟩

/-- **W-state check** (`m = 2`, `g = 2`): the bound holds. -/
theorem wState_satisfies_bound : duttaTusharC wState ≤ cUB_pw 2 2 :=
  C_ub_PauliWeight 2 2 wState (PauliWeightSupportLE.top wState)

/-! ## A genuinely weight-stratified example (`g < m`) -/

/-- A density on `m = 2` with support `{II, ZI}`, i.e. Pauli-weight support `≤ 1 < 2 = m`. -/
noncomputable def stratCoeff : PauliIdx 2 → ℝ := fun P =>
  if P = pauliId 2 then 1
  else if P = ![3, 0] then (1 : ℝ) / 2
  else 0

noncomputable def stratState : PhysicalDensity 2 :=
  ⟨stratCoeff, by
    refine ⟨fun P => ?_, ?_⟩
    · unfold stratCoeff; split_ifs <;> norm_num
    · simp [stratCoeff]⟩

/-- The stratified example has Pauli-weight support `≤ 1`. -/
theorem stratState_support : PauliWeightSupportLE 2 1 stratState := by
  intro P hP
  unfold stratState stratCoeff at hP
  simp only at hP
  by_cases h2 : P = pauliId 2
  · subst h2; simp [BWGradeOfPauli, pauliId]
  · by_cases h1 : P = ![3, 0]
    · subst h1; decide
    · simp [h2, h1] at hP

/-- **Stratified-example check** (`m = 2`, `g = 1 < m`): the bound holds on a strict stratum. -/
theorem stratState_satisfies_bound : duttaTusharC stratState ≤ cUB_pw 2 1 :=
  C_ub_PauliWeight 2 1 stratState stratState_support

end BWGradeStratifiedMonotoneR2
