import StabilizerBW.ReedMuller.Leaves

/-!
# ReedMuller — the pure-linear Barnes–Wall grade equals the T-count

The Barnes–Wall grade `graden m (D_P)` of a linear phase polynomial
`P = c₀ + Σᵢ cᵢ xᵢ` equals its per-monomial T-count
`Σᵢ [cᵢ odd]`.  At degree `≤ 1` all monomials have disjoint supports, so the
grade is additive and the per-monomial T-count is exact.

The proof routes through the kernel-checked Möbius closed form
`Roots.MoebiusClosed.mobius_eq_grade_allN`:
```
  (graden m D_P : ℕ∞) = ⨆_{∅ ≠ U} (2|U| − ν_λ(m_U(D_P))),
```
combined with the Möbius factorisation `mob_lin_eq` and the per-coefficient
`λ`-valuation `factor_eq`.
-/

namespace ReedMuller

open Roots Roots.MoebiusClosed Roots.MoebiusAllN Z8
open scoped Classical
open Finset

/-- The per-coefficient odd-indicator. -/
def oddIndic (c : ZMod 8) : ℕ := if c.val % 2 = 1 then 1 else 0

/-- The Barnes–Wall grade of a linear phase polynomial's operator. -/
noncomputable def gradeOf {m : ℕ} (P : LinPhase m) : ℕ := graden m (toBWVec P)

/-- The per-monomial T-count of a linear phase polynomial: the number of odd
linear coefficients. -/
def tCountLin {m : ℕ} (P : LinPhase m) : ℕ := ∑ i, oddIndic (P.2 i)

/-! ## Units -/

theorem isUnit_zeta : IsUnit (Z8.zeta) :=
  IsUnit.of_mul_eq_one (Z8.zeta ^ 7) (by decide)

theorem zpow8_isUnit (c : ZMod 8) : IsUnit (zpow8 c) := (isUnit_zeta).pow _

/-! ## Per-coefficient arithmetic facts (finite, by `decide`) -/

/-- `ecoef c = 1` for odd `c`. -/
theorem ecoef_odd : ∀ c : ZMod 8, c.val % 2 = 1 → ecoef c = 1 := by decide

/-- An odd coefficient is nonzero. -/
theorem ne_zero_of_odd : ∀ c : ZMod 8, c.val % 2 = 1 → c ≠ 0 := by decide

/-- `ecoef c + [c odd] ≥ 2` for `c ≠ 0`. -/
theorem ecoef_add_odd_ge : ∀ c : ZMod 8, c ≠ 0 → 2 ≤ ecoef c + oddIndic c := by decide

/-! ## The `λ`-valuation of a Möbius coefficient -/

/-
**Möbius valuation, all-nonzero case.** If every coefficient in `U` is
nonzero, `ν_λ(m_U(D_P)) = Σ_{i∈U} ecoef cᵢ`.
-/
theorem valLam_mob_allNonzero {m : ℕ} (P : LinPhase m) (U : Finset (Fin m))
    (h : ∀ i ∈ U, P.2 i ≠ 0) :
    valLam (mob (leafVal m (toBWVec P)) U) = ((∑ i ∈ U, ecoef (P.2 i) : ℕ) : ℕ∞) := by
  convert ReedMuller.emult_lam_pow_mul_unit _ _ _ using 1;
  rotate_left;
  exact zpow8 P.1 * ∏ i ∈ U, unitOf ( P.2 i );
  · refine' IsUnit.mul _ _;
    · exact ReedMuller.zpow8_isUnit _;
    · exact IsUnit.prod_iff.mpr fun i hi => ReedMuller.unitOf_isUnit _ ( h i hi );
  · rw [ ReedMuller.mob_lin_eq ];
    rw [ Finset.prod_congr rfl fun i hi => ReedMuller.factor_eq _ ( h i hi ) ];
    rw [ Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum ] ; ring;
    rfl

/-
**Möbius valuation, has-zero case.** If some coefficient in `U` is zero,
the Möbius coefficient is `0` and its valuation is `⊤`.
-/
theorem valLam_mob_hasZero {m : ℕ} (P : LinPhase m) (U : Finset (Fin m))
    (h : ∃ i ∈ U, P.2 i = 0) :
    valLam (mob (leafVal m (toBWVec P)) U) = ⊤ := by
  obtain ⟨ i, hi, hi' ⟩ := h; simp_all +decide [ mob_lin_eq ] ;
  rw [ Finset.prod_eq_zero hi ] <;> simp +decide [ hi' ];
  unfold valLam; norm_num;

/-! ## The two-sided bound on `mobBound` -/

/-
Each Möbius term is `≤` the T-count.
-/
theorem term_le_tCount {m : ℕ} (P : LinPhase m) (U : Finset (Fin m)) :
    (2 * U.card : ℕ∞) - valLam (mob (leafVal m (toBWVec P)) U) ≤ (tCountLin P : ℕ∞) := by
  by_cases h : ∃ i ∈ U, P.2 i = 0;
  · rw [ ReedMuller.valLam_mob_hasZero P U h ] ; norm_num;
  · rw [ valLam_mob_allNonzero ];
    · simp +zetaDelta at *;
      -- Since each term in the sum is at least 2, we have $2 * U.card \leq \sum_{i \in U} (ecoef (P.2 i) + oddIndic (P.2 i))$.
      have h_sum : 2 * U.card ≤ ∑ i ∈ U, (ecoef (P.2 i) + oddIndic (P.2 i)) := by
        exact le_trans ( by norm_num; linarith ) ( Finset.sum_le_sum fun i hi => ecoef_add_odd_ge _ ( h i hi ) );
      norm_cast ; simp_all +decide [ Finset.sum_add_distrib ];
      linarith [ show ∑ x ∈ U, oddIndic ( P.2 x ) ≤ tCountLin P from Finset.sum_le_sum_of_subset ( Finset.subset_univ U ) ];
    · aesop

/-- The odd-support set `U* = {i : cᵢ odd}`. -/
def oddSet {m : ℕ} (P : LinPhase m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => (P.2 i).val % 2 = 1)

theorem oddSet_card {m : ℕ} (P : LinPhase m) : (oddSet P).card = tCountLin P := by
  unfold tCountLin oddSet oddIndic; simp +decide [ Finset.sum_ite ] ;

/-
On the odd-support set, the Möbius term equals the T-count.
-/
theorem term_oddSet {m : ℕ} (P : LinPhase m) :
    (2 * (oddSet P).card : ℕ∞) - valLam (mob (leafVal m (toBWVec P)) (oddSet P))
      = (tCountLin P : ℕ∞) := by
  rw [ ← oddSet_card, valLam_mob_allNonzero ];
  · rw [ Finset.sum_congr rfl fun i hi => ecoef_odd _ <| by simpa using ( Finset.mem_filter.mp hi ).2 ] ; norm_num;
    -- This follows by simplifying the expression.
    norm_cast
    ring;
    exact Nat.sub_eq_of_eq_add <| by ring;
  · exact fun i hi => ne_zero_of_odd _ <| Finset.mem_filter.mp hi |>.2

/-! ## `mobBound = tCount` and the grade identity -/

theorem mobBound_eq_tCount {m : ℕ} (P : LinPhase m) :
    mobBound m (toBWVec P) = (tCountLin P : ℕ∞) := by
  refine' le_antisymm ( Finset.sup_le _ ) _;
  · exact fun U _ => ReedMuller.term_le_tCount P U;
  · by_cases h : tCountLin P = 0;
    · aesop;
    · refine' le_trans _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.subset_univ _, _ ⟩ );
      convert term_oddSet P |> ge_of_eq using 1;
      exact Finset.card_pos.mp ( by rw [ oddSet_card ] ; positivity )

/-- **Sub-lemma 3 (pure-linear case).** The Barnes–Wall grade equals the
per-monomial T-count. -/
theorem gradeOf_eq_tCount {m : ℕ} (P : LinPhase m) : gradeOf P = tCountLin P := by
  have h := mobius_eq_grade_allN m (toBWVec P)
  rw [mobBound_eq_tCount] at h
  have : (gradeOf P : ℕ∞) = (tCountLin P : ℕ∞) := h
  exact_mod_cast this

end ReedMuller