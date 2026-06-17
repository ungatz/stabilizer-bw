import Mathlib

/-!
# Binary Reed–Muller codes `RM(r, m)`

This module develops the binary Reed–Muller code family from scratch as
submodules of `Fin (2 ^ m) → ZMod 2`, following the standard textbook
treatment (MacWilliams–Sloane Ch. 13).

## Convention

A Reed–Muller code is defined only up to a permutation of the `2 ^ m`
evaluation points; all of its intrinsic invariants (dimension, minimum
distance, dual) are permutation-invariant. We therefore develop the
theory on the **Boolean-function model** `BoolFun m := (Fin m → ZMod 2) → ZMod 2`,
where the recursive coordinate structure is genuine, and transport the results
to `Fin (2 ^ m) → ZMod 2` along an explicit linear equivalence `ptEquiv`
(a relabelling of evaluation points).

`RM' r m` is the order-`r` Reed–Muller code in the Boolean-function model,
spanned by the evaluations of the multilinear monomials `∏_{i ∈ S} x_i`
with `|S| ≤ r`. `RM r m` is its image in `Fin (2 ^ m) → ZMod 2`.
-/

open scoped BigOperators
open Classical

namespace BWCss

/-- Boolean functions `F₂^m → F₂`, the evaluation-point model of length `2^m`. -/
abbrev BoolFun (m : ℕ) := (Fin m → ZMod 2) → ZMod 2

/-- The multilinear monomial `χ_S(x) = ∏_{i ∈ S} x_i` as a Boolean function. -/
def mono (m : ℕ) (S : Finset (Fin m)) : BoolFun m := fun x => ∏ i ∈ S, x i

/-- The indicator point `1_T : F₂^m`, equal to `1` on `T` and `0` elsewhere. -/
def ind {m : ℕ} (T : Finset (Fin m)) : Fin m → ZMod 2 := fun i => if i ∈ T then 1 else 0

/-- The order-`r` Reed–Muller code in the Boolean-function model: the span of
the multilinear monomials of degree `≤ r`. -/
def RM' (r m : ℕ) : Submodule (ZMod 2) (BoolFun m) :=
 Submodule.span (ZMod 2) (mono m '' {S | S.card ≤ r})

/-
Evaluating the monomial `χ_S` at an indicator point `1_T` gives `[S ⊆ T]`.
-/
theorem mono_ind {m : ℕ} (S T : Finset (Fin m)) :
 mono m S (ind T) = if S ⊆ T then 1 else 0 := by
 split_ifs <;> simp_all +decide [ Finset.prod_eq_one, Finset.subset_iff, mono, ind ];
 rw [ Finset.prod_eq_zero_iff ] ; aesop

/-
The full family of multilinear monomials is linearly independent (it is in
fact a basis of `BoolFun m`). Proof by Möbius inversion over the subset
lattice.
-/
theorem mono_linearIndependent (m : ℕ) : LinearIndependent (ZMod 2) (mono m) := by
 refine' Fintype.linearIndependent_iff.2 _;
 intro g hg T;
 induction' T using Finset.strongInduction with T ih;
 replace hg := congr_fun hg ( ind T ) ; simp_all +decide [ mono_ind ] ;
 rw [ Finset.sum_eq_single T ] at hg;
 · aesop;
 · grind;
 · grind +splitIndPred

/-
The Reed–Muller chain (Boolean-function model).
-/
theorem RM'_chain (r m : ℕ) : RM' r m ≤ RM' (r + 1) m := by
 exact Submodule.span_mono ( Set.image_mono ( fun x hx => by simp_all +decide [ Nat.le_succ_of_le ] ) )

/-
Counting subsets of `Fin m` of cardinality `≤ r`.
-/
theorem card_subsets_card_le (m r : ℕ) :
 Fintype.card {S : Finset (Fin m) // S.card ≤ r} = ∑ i ∈ Finset.Iic r, Nat.choose m i := by
 rw [ Fintype.card_subtype ];
 rw [ show ( Finset.filter ( fun x => Finset.card x ≤ r ) Finset.univ : Finset ( Finset ( Fin m ) ) ) = Finset.biUnion ( Finset.Iic r ) fun i => Finset.powersetCard i Finset.univ from ?_, Finset.card_biUnion ] ; aesop;
 · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by rw [ Finset.mem_powersetCard ] at hx₁ hx₂; aesop;
 · ext; aesop

/-
**Dimension formula (Boolean-function model).**
-/
theorem RM'_dim (r m : ℕ) :
 Module.finrank (ZMod 2) (RM' r m) = ∑ i ∈ Finset.Iic r, Nat.choose m i := by
 -- Define the restricted family `b : {S : Finset (Fin m) // S.card ≤ r} → BoolFun m := fun S => mono m S.1`, i.e. `b = mono m ∘ Subtype.val`.
 set b : {S : Finset (Fin m) // S.card ≤ r} → BoolFun m := fun S => mono m S.val;
 -- This is linearly independent: `mono_linearIndependent m` composed with the injective `Subtype.val` via `LinearIndependent.comp` (Subtype.val is injective).
 have h_lin_indep : LinearIndependent (ZMod 2) b := by
 convert mono_linearIndependent m |> fun h => h.comp _ _;
 exact Subtype.coe_injective;
 -- Its range equals `mono m '' {S | S.card ≤ r}`: `Set.range (fun S : {S // S.card ≤ r} => mono m S.1) = mono m '' {S | S.card ≤ r}` (standard `Set.range_comp` / `Subtype.range_val` rewriting).
 have h_range : Set.range b = mono m '' {S : Finset (Fin m) | S.card ≤ r} := by
 aesop;
 -- Hence `RM' r m = Submodule.span (ZMod 2) (Set.range b)` (unfold `RM'`).
 have h_RM'_span : RM' r m = Submodule.span (ZMod 2) (Set.range b) := by
 exact h_range ▸ rfl;
 rw [ h_RM'_span, finrank_span_eq_card ];
 · convert card_subsets_card_le m r using 1;
 · exact h_lin_indep

/-! ### The standard dot-product bilinear form -/

/-- The standard symmetric dot-product bilinear form `⟨x, y⟩ = ∑ i, x i * y i`. -/
noncomputable def dotBilin (ι : Type*) [Fintype ι] : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2) :=
 ∑ i, (LinearMap.proj i).smulRight (LinearMap.proj (R := ZMod 2) (φ := fun _ => ZMod 2) i)

theorem dotBilin_apply {ι : Type*} [Fintype ι] (x y : ι → ZMod 2) :
 dotBilin ι x y = ∑ i, x i * y i := by
 unfold dotBilin;
 simp +decide [ mul_comm ]

theorem dotBilin_isRefl (ι : Type*) [Fintype ι] : (dotBilin ι).IsRefl := by
 intro x y; simp +decide [ dotBilin_apply, mul_comm ] ;

/-
The dot-product form is non-degenerate: its right radical is trivial.
-/
theorem dotBilin_orthogonal_top (ι : Type*) [Fintype ι] :
 (dotBilin ι).orthogonal ⊤ = ⊥ := by
 simp +decide [ Submodule.eq_bot_iff ];
 intro x hx; ext i; have := hx ( Pi.single i 1 ) ; simp_all +decide [ LinearMap.BilinForm.IsOrtho ] ;
 specialize hx ( Pi.single i 1 ) ; simp_all +decide [ dotBilin_apply, Finset.sum_apply, Pi.single_apply ] ;

/-
The pairing of two monomials: `⟨χ_S, χ_T⟩ = [S ∪ T = univ]`.
-/
theorem dotBilin_mono (m : ℕ) (S T : Finset (Fin m)) :
 dotBilin (Fin m → ZMod 2) (mono m S) (mono m T) =
 if S ∪ T = Finset.univ then 1 else 0 := by
 -- The product of two monomials is the monomial of the union of their supports.
 have h_prod : ∀ (S T : Finset (Fin m)), (mono m S) * (mono m T) = mono m (S ∪ T) := by
 intros S T; ext x; simp [mono, Finset.prod_union_inter];
 rw [ ← Finset.prod_union_inter ];
 rw [ ← Finset.prod_sdiff ( Finset.inter_subset_union ) ];
 simp +decide [ mul_assoc, Finset.prod_eq_zero_iff ];
 exact Or.inl ( by rw [ ← Finset.prod_mul_distrib ] ; exact Finset.prod_congr rfl fun _ _ => by rcases x _ with ( _ | _ | n ) <;> trivial );
 -- The sum of a monomial over the hypercube is $2^{m - |S|}$ when $S \neq \text{univ}$ and $1$ when $S = \text{univ}$.
 have h_sum : ∀ (S : Finset (Fin m)), ∑ x : Fin m → ZMod 2, mono m S x = if S = Finset.univ then 1 else 0 := by
 intro S
 have h_sum : ∑ x : Fin m → ZMod 2, mono m S x = ∏ i : Fin m, (∑ x_i : ZMod 2, if i ∈ S then x_i else 1) := by
 rw [ Finset.prod_sum ];
 refine' Finset.sum_bij ( fun x _ => fun i _ => x i ) _ _ _ _ <;> simp +decide [ mono ];
 · simp +decide [ funext_iff ];
 · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
 split_ifs <;> simp_all +decide [ Finset.prod_ite ];
 exact not_forall.mp fun h => ‹¬S = Finset.univ› <| Finset.eq_univ_of_forall h;
 convert h_sum ( S ∪ T ) using 1;
 simp +decide [ ← h_prod, dotBilin_apply ]

/-
Complementary binomial sum identity: the dimensions of `RM'(r,m)` and its
dual `RM'(m-r-1,m)` add up to `2 ^ m`.
-/
theorem Iic_choose_add (r m : ℕ) (h : r + 1 ≤ m) :
 (∑ i ∈ Finset.Iic r, Nat.choose m i) + (∑ i ∈ Finset.Iic (m - r - 1), Nat.choose m i)
 = 2 ^ m := by
 rw [ ← Nat.sum_range_choose m, ← Finset.card_range ( m + 1 ), eq_comm ];
 rw [ show ( Finset.Iic r : Finset ℕ ) = Finset.range ( r + 1 ) by ext; simp +decide [ Nat.lt_succ_iff ], show ( Finset.Iic ( m - r - 1 ) : Finset ℕ ) = Finset.image ( fun i => m - i ) ( Finset.Ico ( r + 1 ) ( m + 1 ) ) from ?_, Finset.sum_image ] <;> norm_num [ Nat.sub_sub ];
 · rw [ ← Finset.sum_range_add_sum_Ico _ ( by linarith : r + 1 ≤ m + 1 ) ] ; simp +decide [ Nat.choose_symm ( by linarith : r + 1 ≤ m + 1 ) ] ;
 exact Finset.sum_congr rfl fun x hx => by rw [ Nat.choose_symm ( by linarith [ Finset.mem_Ico.mp hx ] ) ] ;
 · exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ hx.1, hx.2, hy.1, hy.2 ] ;
 · ext i
 simp [Finset.mem_Iic, Finset.mem_image];
 exact ⟨ fun hi => ⟨ m - i, ⟨ by omega, by omega ⟩, by omega ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; omega ⟩

/-
**Duality (Boolean-function model).**
-/
theorem RM'_dual (r m : ℕ) (h : r + 1 ≤ m) :
 (dotBilin (Fin m → ZMod 2)).orthogonal (RM' r m) = RM' (m - r - 1) m := by
 -- Now use the given lemmas to complete the proof.
 have h_orthogonal : ∀ T : Finset (Fin m), T.card ≤ m - r - 1 → mono m T ∈ (dotBilin (Fin m → ZMod 2)).orthogonal (RM' r m) := by
 intro T hT
 have h_ortho : ∀ S : Finset (Fin m), S.card ≤ r → dotBilin (Fin m → ZMod 2) (mono m S) (mono m T) = 0 := by
 intro S hS
 have h_union : (S ∪ T).card ≤ r + (m - r - 1) := by
 exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add hS hT );
 rw [ dotBilin_mono ];
 exact if_neg ( ne_of_apply_ne Finset.card ( by norm_num; omega ) );
 intro x hx;
 refine' Submodule.span_induction _ _ _ _ hx;
 · rintro _ ⟨ S, hS, rfl ⟩ ; exact h_ortho S hS;
 · simp +decide [ LinearMap.BilinForm.IsOrtho ];
 · simp +contextual [ LinearMap.BilinForm.IsOrtho ];
 · simp +contextual [ LinearMap.BilinForm.IsOrtho ];
 -- By definition of orthogonal complement, we have that any element in the orthogonal complement of RM' r m is in RM' (m - r - 1) m.
 have h_reverse : (dotBilin (Fin m → ZMod 2)).orthogonal (RM' r m) ≤ RM' (m - r - 1) m := by
 have h_finrank : Module.finrank (ZMod 2) (RM' r m) + Module.finrank (ZMod 2) (RM' (m - r - 1) m) = 2 ^ m := by
 convert Iic_choose_add r m h using 1;
 rw [ RM'_dim, RM'_dim ];
 have h_finrank_orthogonal : Module.finrank (ZMod 2) (RM' r m) + Module.finrank (ZMod 2) ((dotBilin (Fin m → ZMod 2)).orthogonal (RM' r m)) = 2 ^ m := by
 convert LinearMap.BilinForm.finrank_add_finrank_orthogonal ( dotBilin_isRefl ( Fin m → ZMod 2 ) ) ( RM' r m ) using 1;
 simp +decide [ dotBilin_orthogonal_top ];
 have h_subspace : RM' (m - r - 1) m ≤ (dotBilin (Fin m → ZMod 2)).orthogonal (RM' r m) := by
 exact Submodule.span_le.mpr ( Set.image_subset_iff.mpr fun T hT => h_orthogonal T hT );
 exact Submodule.eq_of_le_of_finrank_eq h_subspace ( by linarith ) ▸ le_rfl;
 refine' le_antisymm h_reverse _;
 exact Submodule.span_le.mpr ( Set.image_subset_iff.mpr fun T hT => h_orthogonal T hT )

/-! ### Minimum-distance infrastructure: head restriction and discrete derivative -/

/-- Restrict a Boolean function of `m+1` variables by fixing the 0th coordinate
to `a`; a linear map `BoolFun (m+1) →ₗ BoolFun m`. -/
def headLin (m : ℕ) (a : ZMod 2) : BoolFun (m + 1) →ₗ[ZMod 2] BoolFun m where
 toFun c := fun y => c (Fin.cons a y)
 map_add' _ _ := rfl
 map_smul' _ _ := rfl

theorem headLin_apply (m : ℕ) (a : ZMod 2) (c : BoolFun (m + 1)) (y : Fin m → ZMod 2) :
 headLin m a c y = c (Fin.cons a y) := rfl

/-- Push a subset of `Fin (m+1)` down to `Fin m` by deleting the 0th coordinate
and shifting (preimage under `Fin.succ`). -/
noncomputable def shiftDown (m : ℕ) (S : Finset (Fin (m + 1))) : Finset (Fin m) :=
 S.preimage Fin.succ (Fin.succ_injective m).injOn

theorem shiftDown_image (m : ℕ) (S : Finset (Fin (m + 1))) :
 (shiftDown m S).image Fin.succ = S.erase 0 := by
 ext x; simp [shiftDown];
 exact ⟨ fun ⟨ a, ha₁, ha₂ ⟩ => ⟨ by aesop_cat, by aesop_cat ⟩, fun hx => ⟨ Fin.pred x hx.1, by aesop_cat, by aesop_cat ⟩ ⟩

theorem card_shiftDown (m : ℕ) (S : Finset (Fin (m + 1))) :
 (shiftDown m S).card = (S.erase 0).card := by
 rw [ ← shiftDown_image, Finset.card_image_of_injective _ ( Fin.succ_injective _ ) ]

/-
The action of head restriction on a monomial.
-/
theorem headLin_mono (m : ℕ) (a : ZMod 2) (S : Finset (Fin (m + 1))) :
 headLin m a (mono (m + 1) S) =
 (if (0 : Fin (m + 1)) ∈ S then a else 1) • mono m (shiftDown m S) := by
 ext y;
 split_ifs <;> simp_all +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', headLin_apply, mono ];
 · rw [ ← Finset.mul_prod_erase _ _ ‹0 ∈ S› ];
 rw [ ← shiftDown_image ];
 rw [ Finset.prod_image ] <;> aesop;
 · refine' Finset.prod_bij ( fun i hi => Fin.pred i ( by aesop ) ) _ _ _ _ <;> simp_all +decide [ Fin.pred ];
 · intro a ha; refine' Finset.mem_preimage.mpr _; aesop;
 · simp +decide [ Fin.ext_iff, Fin.subNat ];
 grind +extAll;
 · intro b hb; use Fin.succ b; simp_all +decide [ shiftDown ] ;
 simp +decide [ Fin.ext_iff, Fin.subNat ];
 · intro i hi; induction i using Fin.inductionOn <;> simp_all +decide [ Fin.cons ] ;
 · contradiction;
 · congr! 1

/-
The 0-restriction of a degree-`≤ r` function stays degree `≤ r`.
-/
theorem headLin0_RM' (r m : ℕ) (c : BoolFun (m + 1)) (hc : c ∈ RM' r (m + 1)) :
 headLin m 0 c ∈ RM' r m := by
 refine' Submodule.span_induction _ _ _ _ hc;
 · simp +zetaDelta at *;
 intro S hS; rw [ headLin_mono ] ; split_ifs <;> simp_all +decide [ RM' ] ;
 exact Submodule.subset_span ⟨ _, by simp [ card_shiftDown, Finset.card_erase_of_mem, * ], rfl ⟩;
 · exact Submodule.zero_mem _;
 · aesop;
 · intro a x hx₁ hx₂; induction a using Fin.inductionOn <;> aesop;

/-
The discrete derivative w.r.t. the 0th coordinate drops the degree by one.
-/
theorem deriv_RM' (r m : ℕ) (c : BoolFun (m + 1)) (hc : c ∈ RM' r (m + 1)) :
 headLin m 0 c + headLin m 1 c ∈ RM' (r - 1) m := by
 refine' Submodule.span_induction _ _ _ _ hc;
 · rintro _ ⟨ S, hS, rfl ⟩ ; by_cases h0 : 0 ∈ S <;> simp_all +decide [ headLin_mono ] ;
 · refine' Submodule.subset_span ⟨ shiftDown m S, _, rfl ⟩;
 have := card_shiftDown m S; simp_all +decide [ Finset.card_erase_of_mem h0 ] ; omega;
 · convert Submodule.zero_mem _ using 1 ; ring!;
 ext; simp +decide [ two_mul ] ;
 · convert Submodule.zero_mem _;
 · exact fun x y hx hy hx' hy' => by simpa only [ add_add_add_comm ] using Submodule.add_mem _ hx' hy';
 · intro a x hx hx'; convert Submodule.smul_mem _ a hx' using 1; simp +decide [ headLin_apply ] ;

/-
Hamming weight splits over the value of the 0th coordinate.
-/
theorem hammingNorm_headLin_split (m : ℕ) (c : BoolFun (m + 1)) :
 hammingNorm c = hammingNorm (headLin m 0 c) + hammingNorm (headLin m 1 c) := by
 convert Set.ncard_eq_toFinset_card' ( { i : Fin ( m + 1 ) → ZMod 2 | c i ≠ 0 } ) using 1;
 · rw [ Set.ncard_eq_toFinset_card' ] ; aesop;
 · rw [ show ( { i : Fin ( m + 1 ) → ZMod 2 | c i ≠ 0 }.toFinset : Finset ( Fin ( m + 1 ) → ZMod 2 ) ) = Finset.image ( fun x : Fin m → ZMod 2 => Fin.cons 0 x ) ( Finset.filter ( fun x : Fin m → ZMod 2 => c ( Fin.cons 0 x ) ≠ 0 ) Finset.univ ) ∪ Finset.image ( fun x : Fin m → ZMod 2 => Fin.cons 1 x ) ( Finset.filter ( fun x : Fin m → ZMod 2 => c ( Fin.cons 1 x ) ≠ 0 ) Finset.univ ) from ?_, Finset.card_union_of_disjoint ];
 · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
 congr! 2;
 · norm_num [ Finset.disjoint_left ];
 · ext i; simp [Finset.mem_union, Finset.mem_image];
 rcases h : i 0 with ( _ | _ | a ) <;> simp_all +decide [ Fin.cons ];
 · rw [ show i = Fin.cons 0 ( fun j => i j.succ ) from by ext j; cases j using Fin.inductionOn <;> aesop ] ; aesop;
 · rw [ show i = Fin.cons 1 ( fun j => i j.succ ) from ?_ ];
 · simp +decide [ Fin.cons ];
 · funext x
 rcases Fin.eq_zero_or_eq_succ x with h0 | ⟨j, rfl⟩
 · subst h0; simpa using h
 · simp
 · grobner

/-
A function is determined by its two head restrictions; in particular if both
vanish then it vanishes.
-/
theorem eq_zero_of_headLin (m : ℕ) (c : BoolFun (m + 1))
 (h0 : headLin m 0 c = 0) (h1 : headLin m 1 c = 0) : c = 0 := by
 simp_all +decide [ funext_iff, headLin_apply ];
 intro x; rw [ show x = Fin.cons ( x 0 ) ( Fin.tail x ) from by ext i; cases i using Fin.inductionOn <;> rfl ] ; cases Fin.exists_fin_two.mp ⟨ x 0, rfl ⟩ <;> aesop;

/-
**Minimum-distance lower bound (Boolean-function model).** A nonzero
codeword of `RM'(r, m)` has Hamming weight at least `2 ^ (m - r)`.
-/
theorem RM'_min_dist (r m : ℕ) (hr : r ≤ m) :
 ∀ c ∈ RM' r m, c ≠ 0 → 2 ^ (m - r) ≤ hammingNorm c := by
 induction' m with m ih generalizing r;
 · intro c hc hc'; contrapose! hc'; aesop;
 · intro c hc hc_ne_zero
 by_cases hr_le_m : r ≤ m;
 · by_cases h_deriv_zero : headLin m 0 c + headLin m 1 c = 0;
 · -- If `c0 + c1 = 0`, then `c1 = c0`.
 have h_c1_eq_c0 : headLin m 1 c = headLin m 0 c := by
 grind;
 -- If `c0 = 0`, then `c1 = 0` too, so `c = 0` by `eq_zero_of_headLin`, contradiction; hence `c0 ≠ 0`.
 by_cases h_c0_zero : headLin m 0 c = 0;
 · exact False.elim <| hc_ne_zero <| eq_zero_of_headLin m c h_c0_zero <| h_c1_eq_c0.trans h_c0_zero;
 · convert mul_le_mul_of_nonneg_left ( ih r hr_le_m ( headLin m 0 c ) ( headLin0_RM' r m c hc ) h_c0_zero ) zero_le_two using 1;
 · rw [ ← pow_succ', Nat.sub_add_comm hr_le_m ];
 · rw [ hammingNorm_headLin_split, h_c1_eq_c0, two_mul ];
 · -- By the induction hypothesis, we have $2^{m - (r - 1)} \leq \text{hammingNorm}(\text{headLin } m 0 c + \text{headLin } m 1 c)$.
 have h_ind : 2 ^ (m - (r - 1)) ≤ hammingNorm (headLin m 0 c + headLin m 1 c) := by
 convert ih ( r - 1 ) ( Nat.sub_le_of_le_add <| by linarith ) _ ( deriv_RM' r ( m ) c hc ) h_deriv_zero using 1;
 -- By the subadditivity of the Hamming norm, we have $\text{hammingNorm}(c) \geq \text{hammingNorm}(\text{headLin } m 0 c + \text{headLin } m 1 c)$.
 have h_subadd : hammingNorm c ≥ hammingNorm (headLin m 0 c + headLin m 1 c) := by
 have h_subadd : ∀ (a b : BoolFun m), hammingNorm (a + b) ≤ hammingNorm a + hammingNorm b := by
 intros a b
 simp [hammingNorm];
 exact le_trans ( Finset.card_le_card fun x hx => by by_cases ha : a x = 0 <;> by_cases hb : b x = 0 <;> aesop ) ( Finset.card_union_le _ _ );
 exact le_trans ( h_subadd _ _ ) ( by rw [ hammingNorm_headLin_split ] );
 rcases r with ( _ | r ) <;> simp_all +decide [ Nat.succ_sub ];
 · -- Since $c \in RM' 0 (m + 1)$, we have $c = a \cdot \chi_\emptyset$ for some $a \in \mathbb{F}_2$.
 obtain ⟨a, ha⟩ : ∃ a : ZMod 2, c = a • mono (m + 1) ∅ := by
 rw [ show RM' 0 ( m + 1 ) = Submodule.span ( ZMod 2 ) { mono ( m + 1 ) ∅ } from ?_ ] at hc;
 · exact Submodule.mem_span_singleton.mp hc |> fun ⟨ a, ha ⟩ => ⟨ a, ha.symm ⟩;
 · refine' le_antisymm _ _ <;> simp +decide [ RM' ];
 refine absurd ?_ h_deriv_zero
 rw [ha]
 ext y
 simp only [map_smul, Pi.smul_apply, Pi.add_apply, Pi.zero_apply, headLin_apply, mono,
 Finset.prod_empty, smul_eq_mul, mul_one]
 exact CharTwo.add_self_eq_zero a
 · rw [ show m - r = m - ( r + 1 ) + 1 by omega ] at h_ind ; linarith;
 · contrapose! hc_ne_zero; aesop;

/-! ### Transport to `Fin (2 ^ m) → ZMod 2` -/

/-- A relabelling of the `2 ^ m` evaluation points. -/
noncomputable def idxEquiv (m : ℕ) : Fin (2 ^ m) ≃ (Fin m → ZMod 2) :=
 (Fintype.equivFinOfCardEq (by simp)).symm

/-- The induced linear equivalence of the two length-`2^m` coordinate spaces. -/
noncomputable def ptEquiv (m : ℕ) : BoolFun m ≃ₗ[ZMod 2] (Fin (2 ^ m) → ZMod 2) :=
 LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (idxEquiv m)

/-- The order-`r` Reed–Muller code as a subgroup of `Fin (2^m) → ZMod 2`,
defined via evaluation of low-degree monomials. -/
noncomputable def RM (r m : ℕ) : Submodule (ZMod 2) (Fin (2 ^ m) → ZMod 2) :=
 (RM' r m).map (ptEquiv m).toLinearMap

/-- The dual code (orthogonal complement) of a binary linear code in
`Fin n → ZMod 2` with respect to the standard dot product. -/
noncomputable def dualCode {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
 Submodule (ZMod 2) (Fin n → ZMod 2) :=
 (dotBilin (Fin n)).orthogonal C

/-- `ptEquiv` is precomposition with the relabelling `idxEquiv`. -/
theorem ptEquiv_apply (m : ℕ) (f : BoolFun m) (p : Fin (2 ^ m)) :
 ptEquiv m f p = f (idxEquiv m p) := rfl

/-
The relabelling preserves Hamming weight.
-/
theorem hammingNorm_ptEquiv (m : ℕ) (f : BoolFun m) :
 hammingNorm (ptEquiv m f) = hammingNorm f := by
 refine' Finset.card_bij ( fun a _ => idxEquiv m a ) _ _ _ <;> simp +decide [ hammingNorm ];
 · aesop;
 · exact fun b hb => ⟨ ( idxEquiv m ).symm b, by simpa [ ptEquiv_apply ] using hb, by simp +decide ⟩

/-
The relabelling preserves the dot-product bilinear form.
-/
theorem dotBilin_ptEquiv (m : ℕ) (x y : BoolFun m) :
 dotBilin (Fin (2 ^ m)) (ptEquiv m x) (ptEquiv m y) = dotBilin (Fin m → ZMod 2) x y := by
 simp +decide [ dotBilin_apply, hammingNorm ];
 convert Equiv.sum_comp ( idxEquiv m ) ( fun i => x i * y i ) using 1

/-
Transport of the orthogonal complement under the form-preserving equivalence.
-/
theorem dualCode_map (m : ℕ) (S : Submodule (ZMod 2) (BoolFun m)) :
 dualCode (S.map (ptEquiv m).toLinearMap) =
 ((dotBilin (Fin m → ZMod 2)).orthogonal S).map (ptEquiv m).toLinearMap := by
 ext y;
 constructor;
 · intro hy
 obtain ⟨w, hw⟩ : ∃ w : BoolFun m, y = (ptEquiv m) w := by
 exact ⟨ _, Eq.symm <| LinearEquiv.apply_symm_apply ( ptEquiv m ) y ⟩;
 use w; simp_all +decide [ dualCode ] ;
 intro n hn; specialize hy ( ( ptEquiv m ) n ) ; simp_all +decide [ LinearMap.BilinForm.IsOrtho ] ;
 rwa [ dotBilin_ptEquiv ] at hy;
 · rintro ⟨ x, hx, rfl ⟩;
 intro y hy; obtain ⟨ z, hz, rfl ⟩ := hy; simp_all +decide [ LinearMap.BilinForm.IsOrtho ] ;
 rw [ dotBilin_ptEquiv ] ; aesop

theorem RM_dim (r m : ℕ) (hr : r ≤ m) :
 Module.finrank (ZMod 2) (RM r m) = ∑ i ∈ Finset.Iic r, Nat.choose m i := by
 convert RM'_dim r m using 1;
 convert LinearEquiv.finrank_map_eq ( ptEquiv m ) ( RM' r m ) using 1

theorem RM_min_dist (r m : ℕ) (hr : r ≤ m) :
 ∀ c ∈ RM r m, c ≠ 0 → 2 ^ (m - r) ≤ hammingNorm c := by
 -- By definition of `RM`, if `c ∈ RM r m`, then there exists `f ∈ RM' r m` such that `c = ptEquiv m f`.
 intro c hc hc_nonzero
 obtain ⟨f, hf⟩ : ∃ f ∈ RM' r m, c = ptEquiv m f := by
 exact Exists.elim ( Submodule.mem_map.mp hc ) fun x hx => ⟨ x, hx.1, hx.2.symm ⟩;
 convert RM'_min_dist r m hr f hf.1 _ using 1;
 · rw [ hf.2, hammingNorm_ptEquiv ];
 · aesop

theorem RM_chain (r m : ℕ) (hr : r < m) : RM r m ≤ RM (r + 1) m := by
 exact Submodule.map_mono ( RM'_chain r m )

/-- Monotonicity of the Reed–Muller chain (Boolean-function model). -/
theorem RM'_mono {r r' m : ℕ} (h : r ≤ r') : RM' r m ≤ RM' r' m := by
 exact Submodule.span_mono (Set.image_mono (fun _ hx => le_trans hx h))

/-- Monotonicity of the Reed–Muller chain. -/
theorem RM_mono {r r' m : ℕ} (h : r ≤ r') : RM r m ≤ RM r' m := by
 exact Submodule.map_mono (RM'_mono h)

theorem RM_dual (r m : ℕ) (h : r + 1 ≤ m) :
 dualCode (RM r m) = RM (m - r - 1) m := by
 convert dualCode_map m ( RM' r m ) using 1;
 rw [ RM'_dual r m h ];
 rfl

end BWCss