import StabilizerBW.Roots.MoebiusGradeAllN
import StabilizerBW.Roots.Z8Valuation

/-!
# The general-`n` Möbius/grade closed form (R10 · T2, general-n closed form)

Building on:
* `MoebiusGradeAllN.lean` — `cond`, `mrung`, `cond_succ`, `graden_eq_cond` (Item 2);
* `MoebiusClosedFormAllN.lean` — the down-set Möbius transform `mob`, `mob_split`,
 `mob_congr`;
* `Z8Valuation.lean` — `IsDomain ℤ[ζ₈]` and the divisibility ↔ valuation bridge
 `lam_pow_dvd_lam_pow_mul_iff`,

this file proves the **headline general-`n` closed form**

```
 mobius_eq_grade_allN :
 (graden n D : ℕ∞)
 = ⨆_{∅ ≠ U ⊆ {0,…,n-1}} ( (2·|U| : ℕ∞) − ν_λ(m_U) ),
 m_U = mob (leafVal n D) U, ν_λ = emultiplicity λ.
```

## Proof architecture

The leaves of a depth-`n` Barnes–Wall vector are indexed by `Fin n → Bool`; `leafVal n v U`
is the leaf at the Boolean point with support `U`. The engine is the **master lemma**, a
per-`j`, per-rung characterisation proved by induction on `n`:

```
 inMuPow s n (λ^j • v) ↔ ∀ U, λ^{2|U|+2s} ∣ λ^j · m_U(v),
```

where `inMuPow s n` is membership in `μ^s · BW_n` (`μ^0·BW_n = BW_n`). The inductive step
uses the `(u,u+v)` split `inMuPow_succ : inMuPow s (n+1) D ↔ inMuPow s n D.1 ∧
inMuPow (s+1) n (D.1 − D.2)` together with the down-set Möbius identities
`mob_restrict`/`mob_extend` (restriction to / extension by the split coordinate, via
`mob_congr`/`mob_split`). Specialising at `s = 0` gives
`inBW n (λ^j • v) ↔ ∀ U, λ^{2|U|} ∣ λ^j m_U(v)`, and the conductor `cond n v` is the `sInf`
over such `j`; the divisibility ↔ valuation bridge turns this `sInf`-of-intersection into the
`sup`-of-deficits, and `graden_eq_cond` finishes.

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace Roots.MoebiusClosed

open Roots Roots.MoebiusGrade Roots.MoebiusAllN Z8 Finset
open scoped Classical

/-! ## Leaf values of a Barnes–Wall vector -/

/-- The leaf of `v : BWVec n` at the Boolean point `b : Fin n → Bool`. -/
def leafB : (n : ℕ) → BWVec n → (Fin n → Bool) → Z8
 | 0, v, _ => v
 | n + 1, D, b =>
 if b (Fin.last n) then leafB n D.2 (fun i => b i.castSucc)
 else leafB n D.1 (fun i => b i.castSucc)

/-- The leaf of `v : BWVec n` at the Boolean point with support `U`. -/
def leafVal (n : ℕ) (v : BWVec n) (U : Finset (Fin n)) : Z8 :=
 leafB n v (fun i => decide (i ∈ U))

theorem leafVal_zero (v : BWVec 0) (U : Finset (Fin 0)) : leafVal 0 v U = v := rfl

/-- The image of `U ⊆ Fin n` under `castSucc`, a subset of `Fin (n+1)` avoiding the last
coordinate. -/
def castSet {n : ℕ} (U : Finset (Fin n)) : Finset (Fin (n + 1)) := U.map Fin.castSuccEmb

theorem last_not_mem_castSet {n : ℕ} (U : Finset (Fin n)) :
 Fin.last n ∉ castSet U := by
 simp +decide [ castSet ]

theorem mem_castSet {n : ℕ} (U : Finset (Fin n)) (i : Fin n) :
 i.castSucc ∈ castSet U ↔ i ∈ U := by
 rw [ Roots.MoebiusClosed.castSet ];
 simp +decide [ Finset.mem_map ]

theorem card_castSet {n : ℕ} (U : Finset (Fin n)) : (castSet U).card = U.card := by
 exact Finset.card_map _

/-
`leafVal` of the low slice: restricting to `x_n = 0`.
-/
theorem leafVal_castSet {n : ℕ} (D : BWVec (n + 1)) (V : Finset (Fin n)) :
 leafVal (n + 1) D (castSet V) = leafVal n D.1 V := by
 have h_if : (fun i => decide (i ∈ castSet V)) (Fin.last n) = false := by
 simp +decide [ last_not_mem_castSet ];
 exact if_neg ( by simpa [ Fin.ext_iff ] using h_if ) |> fun h => h.trans ( by congr; ext i; simp +decide [ mem_castSet ] ) ;

/-
`leafVal` of the high slice: restricting to `x_n = 1`.
-/
theorem leafVal_insert_castSet {n : ℕ} (D : BWVec (n + 1)) (V : Finset (Fin n)) :
 leafVal (n + 1) D (insert (Fin.last n) (castSet V)) = leafVal n D.2 V := by
 unfold leafVal;
 rw [ leafB ];
 simp +decide [ Fin.ext_iff, mem_castSet ];
 grind

/-
`leafVal` is additive on `bwSub`.
-/
theorem leafVal_bwSub (n : ℕ) (a b : BWVec n) (U : Finset (Fin n)) :
 leafVal n (bwSub n a b) U = leafVal n a U - leafVal n b U := by
 have h_base : ∀ (n : ℕ) (a b : BWVec n) (b' : Fin n → Bool), leafB n (bwSub n a b) b' = leafB n a b' - leafB n b b' := by
 intro n
 induction' n with n ih;
 · intro a b b'; rfl;
 · intro a b b';
 by_cases h : b' (Fin.last n) <;> simp_all +decide [ leafB, bwSub ];
 exact h_base n a b _

/-! ## The down-set Möbius transform across the split coordinate -/

/-
A `mob` over `castSet U` that only sees the low slice collapses to a `mob` over `U`.
-/
theorem mob_castSet_congr {n : ℕ} (h : Finset (Fin (n + 1)) → Z8)
 (h' : Finset (Fin n) → Z8) (U : Finset (Fin n))
 (hyp : ∀ V ⊆ U, h (castSet V) = h' V) :
 mob h (castSet U) = mob h' U := by
 unfold mob;
 refine' Finset.sum_bij ( fun V _ => V.preimage Fin.castSucc ( by aesop ) ) _ _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
 · intro a ha x hx; specialize ha hx; simp_all +decide [ castSet ] ;
 · intro a₁ ha₁ a₂ ha₂ h; ext x; simp_all +decide [ Finset.ext_iff ] ;
 by_cases hx : x = Fin.last n <;> simp_all +decide [ Fin.ext_iff, castSet ];
 · grind;
 · convert h ⟨ x, lt_of_le_of_ne ( Fin.le_last _ ) hx ⟩ using 1;
 · intro b hb; use b.map Fin.castSuccEmb; simp_all +decide [ Finset.ext_iff ] ;
 exact fun x hx => Finset.mem_map.mpr ⟨ x, hb hx, rfl ⟩;
 · intro a ha; rw [ ← hyp _ ] ;
 · rw [ show a = castSet ( a.preimage Fin.castSucc ( by aesop ) ) from ?_ ];
 · simp +decide [ card_castSet, Finset.preimage ];
 simp +decide [ castSet, Finset.mem_map ];
 · simp +decide [ Finset.ext_iff, castSet ];
 intro x; exact ⟨ fun hx => by have := ha hx; unfold castSet at this; aesop, fun hx => by obtain ⟨ y, hy, rfl ⟩ := hx; exact hy ⟩ ;
 · intro x hx; specialize ha ( Finset.mem_preimage.mp hx ) ; unfold castSet at ha; aesop;

/-- **Restriction identity.** For `U ⊆ {0,…,n-1}` (i.e. `last ∉`), the Möbius transform of
the depth-`(n+1)` vector equals that of its low slice. -/
theorem mob_restrict {n : ℕ} (D : BWVec (n + 1)) (U : Finset (Fin n)) :
 mob (leafVal (n + 1) D) (castSet U) = mob (leafVal n D.1) U := by
 apply mob_castSet_congr
 intro V _
 exact leafVal_castSet D V

/-
**Extension identity.** For `U ⊆ {0,…,n-1}` extended by the last coordinate, the Möbius
transform of the depth-`(n+1)` vector equals that of the slice difference `D.2 − D.1`.
-/
theorem mob_extend {n : ℕ} (D : BWVec (n + 1)) (U : Finset (Fin n)) :
 mob (leafVal (n + 1) D) (insert (Fin.last n) (castSet U))
 = mob (leafVal n (bwSub n D.2 D.1)) U := by
 rw [ Roots.MoebiusAllN.mob_split ];
 case a => exact Fin.last n;
 · grind +suggestions;
 · exact Finset.mem_insert_self _ _

/-! ## The `μ^s · BW_n` tower and its `(u,u+v)` split -/

/-- Membership in `μ^s · BW_n` (with `μ = 1 + i = oneI`; `μ^0·BW_n = BW_n`). -/
def inMuPow (s n : ℕ) (v : BWVec n) : Prop :=
 ∃ w, inBW n w ∧ v = bwSmul n (oneI ^ s) w

theorem bwSmul_one (n : ℕ) (v : BWVec n) : bwSmul n 1 v = v := by
 induction n with
 | zero => rw [bwSmul_zero_eq, one_mul]
 | succ n ih => exact Prod.ext (ih _) (ih _)

theorem inMuPow_zero_iff (n : ℕ) (v : BWVec n) : inMuPow 0 n v ↔ inBW n v := by
 constructor;
 · rintro ⟨ w, hw, rfl ⟩;
 grind +suggestions;
 · exact fun h => ⟨ v, h, by simp +decide [ bwSmul_one ] ⟩

/-
**The `(u,u+v)` split of the `μ`-tower.** `μ^s·BW_{n+1}` decomposes into the low slice
in `μ^s·BW_n` and the slice difference in `μ^{s+1}·BW_n`.
-/
theorem inMuPow_succ (s n : ℕ) (D : BWVec (n + 1)) :
 inMuPow s (n + 1) D ↔
 inMuPow s n D.1 ∧ inMuPow (s + 1) n (bwSub n D.1 D.2) := by
 refine ⟨ fun ⟨ W, hW, hD ⟩ => ?_, fun ⟨ ⟨ w1, hw1, hw1' ⟩, ⟨ w2, hw2, hw2' ⟩ ⟩ => ?_ ⟩;
 · rcases W with ⟨ W1, W2 ⟩ ; simp_all +decide [ bwSmul_succ ] ;
 obtain ⟨ w, hw, hw' ⟩ := hW.2.2; simp_all +decide [ bwSmul_bwSub ] ;
 refine' ⟨ ⟨ W1, hW.1, rfl ⟩, ⟨ w, hw, _ ⟩ ⟩;
 convert bwSmul_bwSmul n ( oneI ^ s ) oneI w using 1;
 · refine' ⟨ ( w1, bwSub n w1 ( bwSmul n oneI w2 ) ), _, _ ⟩;
 · refine' ⟨ hw1, _, _ ⟩;
 · exact bwSub_inBW _ ( by solve_by_elim ) ( by solve_by_elim [ bwSmul_inBW ] );
 · use w2;
 have h_sub : ∀ n : ℕ, ∀ a b : BWVec n, bwSub n a (bwSub n a b) = b := by
 intro n a b; induction' n with n ih <;> simp_all +decide [ bwSub ] ;
 exact ⟨ hw2, h_sub _ _ _ ⟩;
 · -- By definition of `bwSmul`, we can split the equality into two parts.
 have h_split : D.1 = bwSmul n (oneI ^ s) w1 ∧ D.2 = bwSmul n (oneI ^ s) (bwSub n w1 (bwSmul n oneI w2)) := by
 have h_split : D.2 = bwSub n D.1 (bwSmul n (oneI ^ s) (bwSmul n oneI w2)) := by
 convert congr_arg ( fun x => bwSub n D.1 x ) hw2' using 1;
 · have h_sub : ∀ (n : ℕ) (a b : BWVec n), bwSub n a (bwSub n a b) = b := by
 intro n a b; induction' n with n ih <;> simp_all +decide [ bwSub ] ;
 rw [ h_sub ];
 · rw [ pow_succ, bwSmul_bwSmul ];
 simp_all +decide [ pow_succ, bwSmul_bwSub ];
 exact Prod.ext h_split.1 h_split.2

/-
`μ^s` and `λ^{2s}` are associates, so they have the same divisibility.
-/
theorem oneI_pow_dvd_iff (s : ℕ) (z : Z8) : oneI ^ s ∣ z ↔ lam ^ (2 * s) ∣ z := by
 rw [ pow_mul, Z8.lam_sq ];
 rw [ mul_pow, mul_comm ];
 constructor <;> intro h;
 · obtain ⟨ k, hk ⟩ := h;
 have h_unit : IsUnit (uu ^ s) := IsUnit.pow _ Z8.isUnit_uu;
 convert mul_dvd_mul_left ( oneI ^ s ) ( h_unit.dvd ) using 1 ; ring;
 · exact dvd_of_mul_left_dvd h

/-! ## The master lemma -/

/-
A `λ`-power divisibility is insensitive to negation of the target.
-/
theorem lam_dvd_neg_iff (a j : ℕ) (y : Z8) :
 lam ^ a ∣ lam ^ j * (-y) ↔ lam ^ a ∣ lam ^ j * y := by
 constructor <;> rintro ⟨ k, hk ⟩ <;> use -k <;> ring_nf at * <;> simp_all +decide [ mul_comm ] ;
 rw [ ← hk, neg_neg ]

/-
Decompose a universal over `Finset (Fin (n+1))` into the `last ∉` and `last ∈` parts.
-/
theorem forall_finset_fin_succ {n : ℕ} (P : Finset (Fin (n + 1)) → Prop) :
 (∀ U, P U) ↔
 (∀ U : Finset (Fin n), P (castSet U)) ∧
 (∀ U : Finset (Fin n), P (insert (Fin.last n) (castSet U))) := by
 refine' ⟨ fun h => ⟨ fun U => h _, fun U => h _ ⟩, fun h U => _ ⟩;
 by_cases h_last : Fin.last n ∈ U;
 · convert h.2 ( Finset.univ.filter ( fun i => Fin.castSucc i ∈ U ) ) using 1;
 ext i; by_cases hi : i = Fin.last n <;> simp_all +decide ;
 constructor <;> intro hi' <;> simp_all +decide [ Fin.ext_iff ] ;
 · exact Finset.mem_map.mpr ⟨ ⟨ i, lt_of_le_of_ne ( Fin.le_last _ ) hi ⟩, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by simpa [ Fin.ext_iff ] using hi' ⟩, rfl ⟩;
 · unfold castSet at hi'; aesop;
 · convert h.1 ( Finset.univ.filter fun i => Fin.castSucc i ∈ U ) using 1;
 ext i; simp [castSet];
 induction i using Fin.lastCases <;> aesop

/-
The `λ`-power divisibility of a Möbius coefficient is insensitive to swapping the two
slices of the difference vector (it only changes the overall sign).
-/
theorem dvd_mob_bwSub_swap (n a' j : ℕ) (x y : BWVec n) (U : Finset (Fin n)) :
 lam ^ a' ∣ lam ^ j * mob (leafVal n (bwSub n x y)) U ↔
 lam ^ a' ∣ lam ^ j * mob (leafVal n (bwSub n y x)) U := by
 have hmob : mob (leafVal n (bwSub n x y)) U = - mob (leafVal n (bwSub n y x)) U := by
 unfold mob;
 rw [ ← Finset.sum_neg_distrib ];
 refine' Finset.sum_congr rfl fun V hV => _;
 rw [ leafVal_bwSub, leafVal_bwSub ] ; ring
 rw [hmob, lam_dvd_neg_iff]

/-
**The master lemma.** For every rung `s` and shift `j`, membership of `λ^j·v` in
`μ^s·BW_n` is the conjunction over all subsets `U` of the `λ`-power divisibilities of the
Möbius coefficients `m_U(v)`.
-/
theorem master (n : ℕ) : ∀ (s j : ℕ) (v : BWVec n),
 inMuPow s n (bwSmul n (lam ^ j) v) ↔
 ∀ U : Finset (Fin n), lam ^ (2 * U.card + 2 * s) ∣ lam ^ j * mob (leafVal n v) U := by
 induction' n with n ih;
 · unfold inMuPow;
 intro s j v;
 constructor <;> intro h;
 · obtain ⟨ w, hw₁, hw₂ ⟩ := h;
 convert oneI_pow_dvd_iff s ( lam ^ j * v ) |>.1 ?_ using 1;
 · simp +decide [ Finset.eq_empty_of_forall_notMem, mob, leafVal ];
 rfl;
 · use w;
 convert hw₂ using 1;
 · convert h ∅;
 convert oneI_pow_dvd_iff s ( bwSmul 0 ( lam ^ j ) v ) using 1;
 · constructor <;> intro h;
 · exact h.elim fun w hw => hw.2.symm ▸ ⟨ w, rfl ⟩;
 · obtain ⟨ w, hw ⟩ := h;
 use w;
 exact ⟨ trivial, by rw [ hw ] ; rfl ⟩;
 · unfold mob leafVal; aesop;
 · intro s j v;
 rw [forall_finset_fin_succ];
 simp_all +decide [ inMuPow_succ, bwSmul_bwSub, mob_restrict, mob_extend ];
 simp +decide [ card_castSet, Finset.card_insert_of_notMem, last_not_mem_castSet ];
 simp +decide [ mul_add, add_assoc, add_comm, add_left_comm ];
 exact fun _ => forall_congr' fun U => dvd_mob_bwSub_swap _ _ _ _ _ _

/-
Specialisation of the master lemma at rung `s = 0`: lattice membership of `λ^j·v`.
-/
theorem inBW_lam_iff_mob (n : ℕ) (j : ℕ) (v : BWVec n) :
 inBW n (bwSmul n (lam ^ j) v) ↔
 ∀ U : Finset (Fin n), lam ^ (2 * U.card) ∣ lam ^ j * mob (leafVal n v) U := by
 convert master n 0 j v using 1;
 rw [ inMuPow_zero_iff ]

/-! ## From the conductor to the Möbius supremum -/

/-- The `λ`-adic valuation `ν_λ = emultiplicity λ`, valued in `ℕ∞`. -/
noncomputable def valLam (y : Z8) : ℕ∞ := emultiplicity lam y

/-- The Möbius supremum `⨆_{∅ ≠ U} (2|U| − ν_λ(m_U))` in `ℕ∞`. -/
noncomputable def mobBound (n : ℕ) (v : BWVec n) : ℕ∞ :=
 ((Finset.univ : Finset (Fin n)).powerset.filter (fun U => U.Nonempty)).sup
 (fun U => (2 * U.card : ℕ∞) - valLam (mob (leafVal n v) U))

/-
The conductor membership set, per-`U`, is up-closed with `sInf` given by the deficit.
-/
theorem cond_eq_mobBound (n : ℕ) (v : BWVec n) :
 (cond n v : ℕ∞) = mobBound n v := by
 -- By definition of `cond`, we know that `cond n v` is the infimum of `condSet n v`.
 have h_cond : ∀ j : ℕ, j ∈ condSet n v ↔ (mobBound n v : ℕ∞) ≤ (j : ℕ∞) := by
 intro j
 simp [condSet, mobBound];
 convert inBW_lam_iff_mob n j v using 1;
 constructor <;> intro h U <;> specialize h U <;> by_cases hU : U.Nonempty <;> simp_all +decide;
 · convert Z8.lam_pow_dvd_lam_pow_mul_iff ( 2 * U.card ) j ( mob ( leafVal n v ) U ) |>.2 h using 1;
 · have := Z8.lam_pow_dvd_lam_pow_mul_iff ( a := 2 * U.card ) ( j := j ) ( mob ( leafVal n v ) U ) ; aesop;
 -- Since `cond n v` is the infimum of `condSet n v`, and `condSet n v` is exactly `{j | mobBound n v ≤ j}`, we can conclude that `cond n v` is the infimum of `{j | mobBound n v ≤ j}`.
 have h_inf : sInf {j : ℕ | (mobBound n v : ℕ∞) ≤ (j : ℕ∞)} = mobBound n v := by
 by_cases h : mobBound n v = ⊤;
 · simp_all +decide;
 exact h_cond _ ( two_mul_mem_condSet n v );
 · cases' h' : mobBound n v with m hm;
 · contradiction;
 · norm_cast;
 exact le_antisymm ( Nat.sInf_le ( by norm_num ) ) ( le_csInf ⟨ m, by norm_num ⟩ fun x hx => hx );
 convert h_inf using 1;
 exact congr_arg _ ( congr_arg _ ( Set.ext h_cond ) )

/-- **The general-`n` Möbius/grade closed form (general-n closed form).** The Barnes–Wall grade of a
diagonal operator `D` on `n` qubits equals the Möbius/finite-difference maximum
`⨆_{∅ ≠ U} (2|U| − ν_λ(m_U(D)))`. -/
theorem mobius_eq_grade_allN (n : ℕ) (D : BWVec n) :
 (graden n D : ℕ∞) = mobBound n D := by
 rw [graden_eq_cond, cond_eq_mobBound]

end Roots.MoebiusClosed