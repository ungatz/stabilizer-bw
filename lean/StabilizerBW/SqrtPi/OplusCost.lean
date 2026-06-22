import StabilizerBW.SqrtPi.Lattice

/-!
# The local cost of `⊕`

For a single-qubit conditional phase `id₁ ⊕ a = diag(1, A)` with `A = ⟦a⟧ ∈ ℤ[ζ₈]`,
the lattice grade is governed by the `λ`-adic valuation of `A - 1`:
$$ g(\mathrm{id}_1 \oplus a) = \max\bigl(0,\ 2 - \nu_\lambda(A - 1)\bigr). $$

The headline theorem `Headline_T2` states exactly this (in `ℕ∞`, where truncated
subtraction realises the `max(0, ·)`).  The corollary `Headline_T2_zeta_table`
computes the grade of `diag(1, ζ₈ʲ)` for all `j`, giving the periodic pattern
`(0,1,0,1,0,1,0,1)`: every odd power of `ζ₈` costs one grade, every even power is free.
-/

set_option maxRecDepth 4000

namespace Pi3
open Z8

/-- The single-qubit conditional phase `id₁ ⊕ a = diag(1, A)`. -/
def diag1 (A : Z8) : Matrix (Fin 2) (Fin 2) Z8 := Matrix.diagonal ![1, A]

lemma diag1_mulVec (A : Z8) (v : Fin 2 → Z8) :
    (diag1 A).mulVec v = ![v 0, A * v 1] := by
  funext i
  fin_cases i <;>
    simp [diag1, Matrix.mulVec_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Characterisation of the `λ^k`-pushforward condition for the diagonal phase. -/
lemma mapsInto_diag1_iff (A : Z8) (k : ℕ) :
    (∀ v ∈ L3, (lam ^ k • (diag1 A).mulVec v) ∈ L3) ↔ divLam2 (lam ^ k * (A - 1)) := by
  rw [← dvd_onePlusI_iff]
  constructor
  · intro h
    have hv : (![1, -1] : Fin 2 → Z8) ∈ L3 := by
      simp [mem_L3]
    have := h _ hv
    simp only [mem_L3, diag1_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one] at this
    have heq : lam ^ k * (1 : Z8) + lam ^ k * (A * -1) = -(lam ^ k * (A - 1)) := by ring
    rw [heq] at this
    exact (dvd_neg).mp this
  · intro h v hv
    simp only [mem_L3] at hv ⊢
    rw [diag1_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    have heq : lam ^ k * v 0 + lam ^ k * (A * v 1)
        = lam ^ k * (v 0 + v 1) + lam ^ k * (A - 1) * v 1 := by ring
    rw [heq]
    exact dvd_add (hv.mul_left (lam ^ k)) (h.mul_right (v 1))

/-- The grade of `diag(1, A)` equals the clamped cost of `A - 1`. -/
lemma latGrade_diag1 (A : Z8) : latGrade (diag1 A) = cost (A - 1) := by
  unfold latGrade
  have : { k : ℕ | ∀ v ∈ L3, (lam ^ k • (diag1 A).mulVec v) ∈ L3 }
       = { k : ℕ | divLam2 (lam ^ k * (A - 1)) } := by
    ext k; exact mapsInto_diag1_iff A k
  rw [this, sInf_divLam2_pow]

/-- `cost x = max(0, 2 - ν_λ x)` as elements of `ℕ∞`. -/
lemma cost_eq_two_sub_nuLam (x : Z8) : (cost x : ℕ∞) = 2 - nuLam x := by
  unfold cost
  by_cases h2 : divLam2 x
  · simp only [h2, if_true, Nat.cast_zero]
    have : (2 : ℕ∞) ≤ nuLam x := (two_le_nuLam_iff x).mpr h2
    exact (tsub_eq_zero_of_le this).symm
  · simp only [h2, if_false]
    by_cases h1 : divLam x
    · simp only [h1, if_true, Nat.cast_one]
      have hge : (1 : ℕ∞) ≤ nuLam x := (one_le_nuLam_iff x).mpr h1
      have hlt : ¬ (2 : ℕ∞) ≤ nuLam x := fun h => h2 ((two_le_nuLam_iff x).mp h)
      have heq : nuLam x = 1 := by
        cases hx : nuLam x with
        | top => rw [hx] at hlt; exact absurd le_top hlt
        | coe n =>
          rw [hx] at hge hlt
          have h1n : 1 ≤ n := by exact_mod_cast hge
          have h2n : ¬ 2 ≤ n := by
            intro hh; exact hlt (by exact_mod_cast hh)
          have : n = 1 := by omega
          rw [this]; rfl
      rw [heq]; rfl
    · simp only [h1, if_false]
      have hlt : ¬ (1 : ℕ∞) ≤ nuLam x := fun h => h1 ((one_le_nuLam_iff x).mp h)
      have heq : nuLam x = 0 := by
        cases hx : nuLam x with
        | top => rw [hx] at hlt; exact absurd le_top hlt
        | coe n =>
          rw [hx] at hlt
          have : n = 0 := by
            by_contra hn
            exact hlt (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
          rw [this]; rfl
      rw [heq]; rfl

/-- **T2 (Headline).** The local cost of `⊕`:
`g(diag(1, A)) = max(0, 2 - ν_λ(A - 1))` (in `ℕ∞`, truncated subtraction).

No hypothesis on `A` is required; in particular it holds for every unit `A`,
which is the form stated above. -/
theorem Headline_T2 (A : Z8) : (latGrade (diag1 A) : ℕ∞) = 2 - nuLam (A - 1) := by
  rw [latGrade_diag1, cost_eq_two_sub_nuLam]

/-! ### The four verification cases of T2 -/

/-- `a = id₁`, i.e. `A = 1`: grade `0` (the identity `diag(1,1) = I`). -/
theorem T2_case_id : latGrade (diag1 1) = 0 := by rw [latGrade_diag1]; decide

/-- `a = ζ₈⁴ = -1`, i.e. `A = -1`: grade `0` (matches `Z = diag(1,-1)`). -/
theorem T2_case_negOne : latGrade (diag1 (-1)) = 0 := by rw [latGrade_diag1]; decide

/-- `a = ζ₈² = i`, i.e. `A = i`: grade `0` (matches `S = diag(1,i)`). -/
theorem T2_case_S : latGrade (diag1 Z8.imag) = 0 := by rw [latGrade_diag1]; decide

/-- `a = ζ₈`, i.e. `A = ζ₈`: grade `1` (matches `T = diag(1,ζ₈)`). -/
theorem T2_case_T : latGrade (diag1 Z8.zeta) = 1 := by rw [latGrade_diag1]; decide

/-- **T2 (Corollary).** The map `j ↦ g(id₁ ⊕ ζ₈ʲ)` on `ℤ/8ℤ` is `(0,1,0,1,0,1,0,1)`:
every odd power of `ζ₈` costs one grade, every even power is free. -/
theorem Headline_T2_zeta_table (j : Fin 8) :
    latGrade (diag1 (Z8.zeta ^ (j : ℕ))) = ![0, 1, 0, 1, 0, 1, 0, 1] j := by
  fin_cases j <;> (rw [latGrade_diag1]; decide)

end Pi3
