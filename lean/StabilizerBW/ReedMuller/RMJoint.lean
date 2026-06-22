import StabilizerBW.ReedMuller.GradeEnumerator

/-!
# ReedMuller — the RM(1, m) bivariate (weight, grade) joint enumerator (stretch target 3)

Each linear phase polynomial `P` reduces mod 2 to an RM(1, m) codeword
`x ↦ (c₀ + Σᵢ cᵢ xᵢ) mod 2`; its Hamming weight is `0` (zero function),
`2^m` (constant 1), or `2^{m-1}` (non-constant affine).  Tracking jointly the
codeword weight and the Barnes–Wall grade gives the bivariate enumerator.

**Correction.**  The strawman's stated closed form
`8·4^m·(x^{2^m} + y^{2^m} + 2·(Σ_k C(m,k) z^k)·x^{2^{m-1}} y^{2^{m-1}})` is
**off by a global factor of 2** (verified numerically at `m = 1, 2`: it equals
twice the true left-hand side).  This is exactly the "constant-offset factor of 2"
bookkeeping flagged in `refs/03-rm-weight-enumerator-refinement.md`.  The correct
identity, proved here, is
```
  ∑_P x^{2^m − w} y^w z^{g} =
      4·4^m·(x^{2^m} + y^{2^m})
    + 8·4^m·(Σ_{k=1}^m C(m,k) z^k)·x^{2^{m-1}}·y^{2^{m-1}} .
```
-/

namespace ReedMuller

open scoped Classical
open Finset

/-- Reduction `ℤ/8 → ℤ/2`. -/
def red : ZMod 8 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

/-- The RM(1, m) codeword of a linear phase polynomial (over the Boolean points
`Fin m → Bool`, of which there are `2^m`). -/
def rmCodeword {m : ℕ} (P : LinPhase m) (b : Fin m → Bool) : ZMod 2 :=
  red P.1 + ∑ i, if b i then red (P.2 i) else 0

/-- The Hamming weight of the codeword. -/
def hammingWeight {m : ℕ} (P : LinPhase m) : ℕ :=
  (Finset.univ.filter (fun b : Fin m → Bool => rmCodeword P b = 1)).card

/-- The "all linear coefficients even" predicate (zero RM-linear part). -/
def allEvenLin {m : ℕ} (P : LinPhase m) : Prop := ∀ i, red (P.2 i) = 0

instance {m : ℕ} (P : LinPhase m) : Decidable (allEvenLin P) := by
  unfold allEvenLin; infer_instance

/-! ## Weight classes -/

/-
**Affine weight = half.** A non-constant affine form over `𝔽₂^m` takes the
value `1` on exactly `2^{m-1}` of the `2^m` Boolean points.
-/
theorem count_affine_eq_one {m : ℕ} (c0 : ZMod 2) (a : Fin m → ZMod 2)
    (hj : ∃ j, a j = 1) :
    (Finset.univ.filter (fun b : Fin m → Bool =>
        c0 + ∑ i, (if b i then a i else 0) = 1)).card = 2 ^ (m - 1) := by
  rcases m with ( _ | m ) <;> simp_all +decide [ pow_succ' ];
  -- Let `j` be an index such that `a j = 1`.
  obtain ⟨j, hj⟩ : ∃ j, a j = 1 := hj;
  have h_flip : ∀ b : Fin (m + 1) → Bool, (c0 + ∑ i, if b i then a i else 0) = 1 ↔ (c0 + ∑ i, if (Function.update b j (¬b j)) i then a i else 0) = 0 := by
    intro b
    have h_flip : ∑ i, (if b i then a i else 0) + ∑ i, (if (Function.update b j (¬b j)) i then a i else 0) = a j := by
      rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.sum_eq_single j ] <;> simp +decide [ Function.update_apply ] ;
      · cases b j <;> simp +decide [ * ];
      · grind;
    grind +ring;
  have h_flip_card : Finset.card (Finset.filter (fun b : Fin (m + 1) → Bool => (c0 + ∑ i, if b i then a i else 0) = 1) Finset.univ) = Finset.card (Finset.filter (fun b : Fin (m + 1) → Bool => (c0 + ∑ i, if b i then a i else 0) = 0) Finset.univ) := by
    apply Finset.card_bij (fun b _ => Function.update b j (¬b j));
    · aesop;
    · intro b₁ hb₁ b₂ hb₂ h; ext i; by_cases hi : i = j <;> replace h := congr_fun h i <;> aesop;
    · intro b hb; use Function.update b j (¬b j); aesop;
  have h_total_card : Finset.card (Finset.filter (fun b : Fin (m + 1) → Bool => (c0 + ∑ i, if b i then a i else 0) = 1) Finset.univ) + Finset.card (Finset.filter (fun b : Fin (m + 1) → Bool => (c0 + ∑ i, if b i then a i else 0) = 0) Finset.univ) = 2 ^ (m + 1) := by
    rw [ ← Finset.card_union_of_disjoint ];
    · convert Finset.card_univ ( α := Fin ( m + 1 ) → Bool ) using 2 ; ext b ; have := Fin.exists_fin_two.mp ⟨ c0 + ∑ i, if b i = true then a i else 0, rfl ⟩ ; aesop;
      norm_num [ Fintype.card_pi ];
    · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by aesop;
  grind

/-
Weight in the non-constant (some odd linear coefficient) case.
-/
theorem weight_someOdd {m : ℕ} (P : LinPhase m) (h : ¬ allEvenLin P) :
    hammingWeight P = 2 ^ (m - 1) := by
  convert ReedMuller.count_affine_eq_one ( red P.1 ) ( fun i => red ( P.2 i ) ) _ using 1;
  exact not_forall_not.mp fun h' => h fun i => by have := h' i; have := Fin.exists_fin_two.mp ⟨ red ( P.2 i ), rfl ⟩ ; aesop;

/-
Weight in the constant (all even linear coefficients) case.
-/
theorem weight_allEven {m : ℕ} (P : LinPhase m) (h : allEvenLin P) :
    hammingWeight P = if red P.1 = 0 then 0 else 2 ^ m := by
  split_ifs <;> simp_all +decide [ allEvenLin ];
  · exact Finset.card_eq_zero.mpr ( Finset.filter_eq_empty_iff.mpr fun x hx => by unfold rmCodeword; aesop );
  · unfold hammingWeight; simp +decide [ *, rmCodeword ] ;
    rw [ if_pos ];
    · norm_num [ Finset.card_univ ];
    · exact Or.resolve_left ( Fin.exists_fin_two.mp ( by aesop ) ) ‹_›

/-! ## tCount facts -/

/-
`allEvenLin` is equivalent to having T-count `0`.
-/
theorem allEvenLin_iff_tCount_zero {m : ℕ} (P : LinPhase m) :
    allEvenLin P ↔ tCountLin P = 0 := by
  -- By definition of `oddIndic`, we know that `red c = 0` if and only if `oddIndic c = 0`.
  have h_oddIndic : ∀ c : ZMod 8, red c = 0 ↔ oddIndic c = 0 := by decide
  simp +decide [ allEvenLin, tCountLin, Finset.sum_eq_zero_iff_of_nonneg, h_oddIndic ]

/-- The grade GF headline as a T-count statement: `∑_P z^{tCount} = 8·4^m·(1+z)^m`. -/
theorem tcount_GF_headline (m : ℕ) (z : ℤ) :
    (∑ P : LinPhase m, z ^ tCountLin P) = 8 * 4 ^ m * (1 + z) ^ m := by
  rw [← grade_GF_linear_headline]
  exact Finset.sum_congr rfl (fun P _ => by rw [gradeOf_eq_tCount])

/-
The number of phase polynomials with all-even linear part is `8·4^m`.
-/
theorem card_allEven (m : ℕ) :
    (Finset.univ.filter (fun P : LinPhase m => allEvenLin P)).card = 8 * 4 ^ m := by
  convert ReedMuller.tcount_GF m 0 using 1;
  norm_num [ zero_pow_eq ];
  grind +suggestions

/-
`∑_{k=1}^m C(m,k) z^k = (1+z)^m − 1`.
-/
theorem binom_Icc (m : ℕ) (z : ℤ) :
    (∑ k ∈ Finset.Icc 1 m, (Nat.choose m k : ℤ) * z ^ k) = (1 + z) ^ m - 1 := by
  erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num;
  rw [ add_comm 1 z, add_pow ] ; congr ; ext ; ring

/-
The T-count GF restricted to phase polynomials with a non-trivial RM-linear
part.
-/
theorem sum_notAllEven_tcount (m : ℕ) (z : ℤ) :
    (∑ P ∈ Finset.univ.filter (fun P : LinPhase m => ¬ allEvenLin P), z ^ tCountLin P)
      = 8 * 4 ^ m * ((1 + z) ^ m - 1) := by
  have h_split : ∑ P : LinPhase m, z ^ tCountLin P = ∑ P ∈ Finset.filter (fun P : LinPhase m => allEvenLin P) Finset.univ, z ^ tCountLin P + ∑ P ∈ Finset.filter (fun P : LinPhase m => ¬allEvenLin P) Finset.univ, z ^ tCountLin P := by
    rw [ Finset.sum_filter_add_sum_filter_not ];
  -- On `filter allEvenLin`, `tCountLin P = 0` (by `allEvenLin_iff_tCount_zero`), so each summand is `z^0 = 1` and the sum is the cardinality `card_allEven = 8*4^m`.
  have h_even : ∑ P ∈ Finset.filter (fun P : LinPhase m => allEvenLin P) Finset.univ, z ^ tCountLin P = 8 * 4 ^ m := by
    rw [ Finset.sum_congr rfl fun P hP => by rw [ allEvenLin_iff_tCount_zero P |>.1 <| Finset.mem_filter.mp hP |>.2 ] ] ; norm_num [ ReedMuller.card_allEven ];
  linarith [ ReedMuller.tcount_GF_headline m z ]

/-
The number of phase polynomials with all-even linear part and a fixed
constant parity `v` is `4·4^m`.
-/
theorem card_allEven_redConst (m : ℕ) (v : ZMod 2) :
    (Finset.univ.filter (fun P : LinPhase m => allEvenLin P ∧ red P.1 = v)).card = 4 * 4 ^ m := by
  -- The filtered set is a product of two sets, so we can apply the cardinality product formula.
  have h_filter_prod : Finset.filter (fun P : LinPhase m => allEvenLin P ∧ red P.1 = v) Finset.univ = Finset.product (Finset.filter (fun c : ZMod 8 => red c = v) Finset.univ) (Finset.filter (fun f : Fin m → ZMod 8 => ∀ i, red (f i) = 0) Finset.univ) := by
    ext ⟨c, f⟩; simp [allEvenLin, red];
    tauto;
  -- The cardinality of the set of functions from `Fin m` to `ZMod 8` where each function value reduces to `0` is `4^m`.
  have h_card_pi : (Finset.filter (fun f : Fin m → ZMod 8 => ∀ i, red (f i) = 0) Finset.univ).card = 4 ^ m := by
    have h_card_pi : (Finset.filter (fun f : Fin m → ZMod 8 => ∀ i, red (f i) = 0) Finset.univ).card = Finset.card (Fintype.piFinset (fun _ : Fin m => Finset.filter (fun c : ZMod 8 => red c = 0) Finset.univ)) := by
      congr with f ; simp +decide [ funext_iff ];
    rw [ h_card_pi, Fintype.card_piFinset ] ; norm_num;
    exact congr_arg ( · ^ m ) ( by rfl );
  erw [ h_filter_prod, Finset.card_product ] ; norm_num [ h_card_pi ];
  fin_cases v <;> trivial

/-! ## The joint enumerator -/

/-
**Stretch target 3 (corrected).** The bivariate (weight, grade) joint
enumerator factorisation.
-/
theorem joint_enumerator (m : ℕ) (x y z : ℤ) :
    (∑ P : LinPhase m,
       x ^ (2 ^ m - hammingWeight P) * y ^ hammingWeight P * z ^ gradeOf P)
      = 4 * 4 ^ m * (x ^ (2 ^ m) + y ^ (2 ^ m))
        + 8 * 4 ^ m * (∑ k ∈ Finset.Icc 1 m, (Nat.choose m k : ℤ) * z ^ k)
            * x ^ (2 ^ (m - 1)) * y ^ (2 ^ (m - 1)) := by
  revert x y z;
  -- Split the sum into two parts: one where all coefficients are even and one where at least one coefficient is odd.
  have h_split : ∀ (x y z : ℤ),
    (∑ P : LinPhase m, x ^ (2 ^ m - hammingWeight P) * y ^ hammingWeight P * z ^ gradeOf P) =
    (∑ P ∈ Finset.filter (fun P : LinPhase m => allEvenLin P) Finset.univ, x ^ (2 ^ m - hammingWeight P) * y ^ hammingWeight P * z ^ gradeOf P) +
    (∑ P ∈ Finset.filter (fun P : LinPhase m => ¬allEvenLin P) Finset.univ, x ^ (2 ^ m - hammingWeight P) * y ^ hammingWeight P * z ^ gradeOf P) := by
      exact fun x y z => by rw [ Finset.sum_filter_add_sum_filter_not ] ;
  intro x y z
  rw [h_split];
  congr 1;
  · have h_even : ∀ P : LinPhase m, allEvenLin P → x ^ (2 ^ m - hammingWeight P) * y ^ hammingWeight P * z ^ gradeOf P = if red P.1 = 0 then x ^ (2 ^ m) else y ^ (2 ^ m) := by
      intros P hP
      have h_even : hammingWeight P = if red P.1 = 0 then 0 else 2 ^ m := by
        exact ReedMuller.weight_allEven P hP
      have h_grade : gradeOf P = 0 := by
        rw [ gradeOf_eq_tCount, allEvenLin_iff_tCount_zero P |>.1 hP ]
      rw [h_even, h_grade]
      simp [pow_zero];
      split_ifs <;> simp +decide [ * ];
    rw [ Finset.sum_congr rfl fun P hP => h_even P <| Finset.mem_filter.mp hP |>.2 ];
    rw [ Finset.sum_ite ] ; norm_num [ ReedMuller.card_allEven_redConst ] ; ring;
    rw [ show ( Finset.filter ( fun P : LinPhase m => red P.1 = 0 ) ( Finset.filter allEvenLin Finset.univ ) ) = Finset.filter ( fun P : LinPhase m => allEvenLin P ∧ red P.1 = 0 ) Finset.univ by ext; aesop, show ( Finset.filter ( fun P : LinPhase m => ¬red P.1 = 0 ) ( Finset.filter allEvenLin Finset.univ ) ) = Finset.filter ( fun P : LinPhase m => allEvenLin P ∧ red P.1 = 1 ) Finset.univ by ext; have := Fin.exists_fin_two.mp ⟨ red ‹LinPhase m›.1, rfl ⟩ ; aesop ] ; norm_num [ ReedMuller.card_allEven_redConst ] ; ring;
  · by_cases hm : m = 0;
    · subst hm; simp +decide [ allEvenLin ] ;
    · have h_sum_notAllEven : (∑ P ∈ Finset.univ.filter (fun P : LinPhase m => ¬allEvenLin P), x ^ (2 ^ m - hammingWeight P) * y ^ hammingWeight P * z ^ gradeOf P) = x ^ (2 ^ (m - 1)) * y ^ (2 ^ (m - 1)) * (∑ P ∈ Finset.univ.filter (fun P : LinPhase m => ¬allEvenLin P), z ^ tCountLin P) := by
        rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun P hP => _ ; rw [ gradeOf_eq_tCount ] ; rw [ weight_someOdd P ( by aesop ) ] ; rcases m with ( _ | m ) <;> simp_all +decide [ pow_succ' ] ;
        norm_num [ two_mul ];
      rw [ h_sum_notAllEven, sum_notAllEven_tcount ];
      rw [ binom_Icc ] ; ring

end ReedMuller