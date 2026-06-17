import StabilizerBW.Roots.MoebiusClosedFormAllN

/-!
# The general-`n` conductor recursion over the canonical Barnes–Wall lattice (R10 · T2, step 4 core)

`MoebiusClosedFormAllN.lean` delivered steps 1–3 of the attack plan: the phase-vector split
(`bwSmul_lam_split`), the conductor decomposition (`inBW_succ_conductor_split`), and the
`μ`-rung count `ν_λ(μ) = 2` (`inOneIBW_lam_pow_iff`), combined into the level-`n` recursion
`inBW_succ_lam_iff`.

This file turns that membership recursion into a **numerical conductor recursion** over the
canonical lattice (`Roots/BWn.lean`). For an arbitrary `BW_n`-vector `v` we define the
`λ`-adic conductor

```
 cond n v := sInf { j | inBW n (λ^j · v) } (least j with λ^j·v ∈ BW_n)
 mrung n v := sInf { j | λ^j · v ∈ μ·BW_n } (the μ-conductor)
```

and prove the clean **conductor recursion** (the exact `max ⟺ AND` collapse that the
general-`n` Möbius induction consumes):

```
 cond_succ : cond (n+1) D = max (cond n D.1) (mrung n (D.1 − D.2)).
```

together with the supporting structural facts (`cond_le_top : cond n v ≤ 2n`, the conductor
is genuinely attained, `mrung` versus `cond` in the `j ≥ 2` regime, etc.). This is the
canonical-infrastructure form of the conductor side of the Möbius↔conductor synthesis: the
`U ∌ n` part of the Möbius maximum is governed by `cond n D.1`, the `U ∋ n` part by
`mrung n (D.1 − D.2)`, and `cond_succ` is the rung-for-rung collapse joining them.

Everything is kernel-clean (no `sorry`, `axiom`, `native_decide`, `@[implemented_by]`).
-/

namespace Roots.MoebiusGrade

open Roots Z8

/-! ## Up-closed subsets of `ℕ` and their `sInf` -/

/-- A set of naturals is *up-closed* if it is closed under `+1`. -/
def IsUpClosed (S : Set ℕ) : Prop := ∀ j, j ∈ S → (j + 1) ∈ S

theorem IsUpClosed.mem_of_le {S : Set ℕ} (hS : IsUpClosed S) {a b : ℕ}
 (ha : a ∈ S) (hab : a ≤ b) : b ∈ S := by
 induction hab with
 | refl => exact ha
 | step _ ih => exact hS _ ih

/-- For a nonempty up-closed set, membership is exactly being `≥ sInf`. -/
theorem IsUpClosed.mem_iff_sInf_le {S : Set ℕ} (hS : IsUpClosed S) (hne : S.Nonempty)
 {j : ℕ} : j ∈ S ↔ sInf S ≤ j := by
 constructor
 · intro hj; exact Nat.sInf_le hj
 · intro hj; exact hS.mem_of_le (Nat.sInf_mem hne) hj

/-
The `sInf` of an intersection of two nonempty up-closed sets is the `max` of the two
`sInf`s.
-/
theorem sInf_inter_eq_max {A B : Set ℕ} (hA : IsUpClosed A) (hB : IsUpClosed B)
 (hAne : A.Nonempty) (hBne : B.Nonempty) :
 sInf (A ∩ B) = max (sInf A) (sInf B) := by
 refine' le_antisymm _ _;
 · refine' Nat.sInf_le _;
 exact ⟨ hA.mem_of_le ( Nat.sInf_mem hAne ) ( le_max_left _ _ ), hB.mem_of_le ( Nat.sInf_mem hBne ) ( le_max_right _ _ ) ⟩;
 · refine' max_le _ _ <;> refine' le_csInf _ _ <;> norm_num;
 · exact ⟨ _, hA.mem_of_le hAne.choose_spec ( le_max_left _ _ ), hB.mem_of_le hBne.choose_spec ( le_max_right _ _ ) ⟩;
 · exact fun x hx hx' => Nat.sInf_le hx;
 · exact ⟨ _, hA.mem_of_le ( hAne.choose_spec ) ( le_max_left _ _ ), hB.mem_of_le ( hBne.choose_spec ) ( le_max_right _ _ ) ⟩;
 · exact fun x hx hx' => Nat.sInf_le hx'

/-! ## The conductor and the `μ`-conductor over `BW_n` -/

/-- The membership set `{ j | λ^j · v ∈ BW_n }`. -/
def condSet (n : ℕ) (v : BWVec n) : Set ℕ := {j | inBW n (bwSmul n (Z8.lam ^ j) v)}

/-- The membership set `{ j | λ^j · v ∈ μ·BW_n }`. -/
def mrungSet (n : ℕ) (v : BWVec n) : Set ℕ := {j | inOneIBW n (bwSmul n (Z8.lam ^ j) v)}

/-- The `λ`-adic conductor: least `j` with `λ^j · v ∈ BW_n`. -/
noncomputable def cond (n : ℕ) (v : BWVec n) : ℕ := sInf (condSet n v)

/-- The `μ`-conductor: least `j` with `λ^j · v ∈ μ·BW_n`. -/
noncomputable def mrung (n : ℕ) (v : BWVec n) : ℕ := sInf (mrungSet n v)

/-! ### Up-closure and nonemptiness -/

theorem condSet_upClosed (n : ℕ) (v : BWVec n) : IsUpClosed (condSet n v) := by
 intro j hj
 show inBW n (bwSmul n (Z8.lam ^ (j + 1)) v)
 have h : bwSmul n (Z8.lam ^ (j + 1)) v = bwSmul n Z8.lam (bwSmul n (Z8.lam ^ j) v) := by
 rw [bwSmul_bwSmul, pow_succ']
 rw [h]
 exact Roots.bwSmul_inBW n Z8.lam hj

theorem mrungSet_upClosed (n : ℕ) (v : BWVec n) : IsUpClosed (mrungSet n v) := by
 intro j hj
 obtain ⟨w, hw_inBW, hw_eq⟩ := hj
 use bwSmul n Z8.lam w;
 refine' ⟨ _, _ ⟩;
 · exact bwSmul_inBW _ _ hw_inBW;
 · have h_smul : bwSmul n (lam ^ (j + 1)) v = bwSmul n (lam * lam ^ j) v := by
 rw [ pow_succ' ];
 have h_smul : bwSmul n (lam * lam ^ j) v = bwSmul n lam (bwSmul n (lam ^ j) v) := by
 exact Eq.symm (bwSmul_bwSmul n lam (lam ^ j) v)
 simp_all +decide [ mul_comm, bwSmul_bwSmul ]

/-
`λ^{2n}·v ∈ BW_n` for every `v` (the conductor lemma in power form): `2n ∈ condSet`.
-/
theorem two_mul_mem_condSet (n : ℕ) (v : BWVec n) : (2 * n) ∈ condSet n v := by
 -- By definition of `bwSmul`, we have `bwSmul n (Z8.lam ^ (2 * n)) v = bwSmul n (oneI ^ n * uu ^ n) v`.
 have h_smul : bwSmul n (Z8.lam ^ (2 * n)) v = bwSmul n (oneI ^ n) (bwSmul n (uu ^ n) v) := by
 rw [ Roots.lam_pow_two_mul ];
 exact Eq.symm (bwSmul_bwSmul n (oneI ^ n) (uu ^ n) v)
 convert Roots.conductor n ( bwSmul n ( uu ^ n ) v ) using 1;
 exact h_smul ▸ Iff.rfl

theorem condSet_nonempty (n : ℕ) (v : BWVec n) : (condSet n v).Nonempty :=
 ⟨2 * n, two_mul_mem_condSet n v⟩

/-
`λ^{2n+2}·v ∈ μ·BW_n` for every `v`: the `μ`-conductor is finite.
-/
theorem mrungSet_nonempty (n : ℕ) (v : BWVec n) : (mrungSet n v).Nonempty := by
 have := @Roots.inOneIBW_lam_pow_iff n ( 2 * n + 2 ) ( by linarith ) v;
 exact ⟨ _, this.mpr ( by simpa using two_mul_mem_condSet n v ) ⟩

/-! ### Basic conductor facts -/

theorem cond_le_top (n : ℕ) (v : BWVec n) : cond n v ≤ 2 * n :=
 Nat.sInf_le (two_mul_mem_condSet n v)

theorem mem_condSet_iff (n : ℕ) (v : BWVec n) {j : ℕ} :
 j ∈ condSet n v ↔ cond n v ≤ j :=
 (condSet_upClosed n v).mem_iff_sInf_le (condSet_nonempty n v)

theorem mem_mrungSet_iff (n : ℕ) (v : BWVec n) {j : ℕ} :
 j ∈ mrungSet n v ↔ mrung n v ≤ j :=
 (mrungSet_upClosed n v).mem_iff_sInf_le (mrungSet_nonempty n v)

/-
`cond 0 v = 0`: `BW_0 = R` is the whole ring, so every scalar already lies in it.
-/
theorem cond_zero (v : BWVec 0) : cond 0 v = 0 := by
 exact le_antisymm ( Nat.sInf_le ( by tauto ) ) ( Nat.zero_le _ )

/-! ## The conductor recursion (the `max ⟺ AND` collapse) -/

/-
**The general-`n` conductor recursion.** For a depth-`(n+1)` vector `D` with halves
`D.1` (the `x_n = 0` slice) and `D.2` (the `x_n = 1` slice), the conductor splits as the
`max` of the outer conductor on `D.1` and the `μ`-conductor on the difference `D.1 − D.2`.
This is the canonical-lattice form of the `max ⟺ AND` collapse driving the general-`n`
Möbius induction: the `U ∌ n` part is `cond n D.1`, the `U ∋ n` part is the `μ`-rung
`mrung n (D.1 − D.2)`.
-/
theorem cond_succ (n : ℕ) (D : BWVec (n + 1)) :
 cond (n + 1) D = max (cond n D.1) (mrung n (bwSub n D.1 D.2)) := by
 rw [ show cond ( n + 1 ) D = sInf ( condSet ( n + 1 ) D ) from rfl, show condSet ( n + 1 ) D = condSet n D.1 ∩ mrungSet n ( bwSub n D.1 D.2 ) from ?_, sInf_inter_eq_max ];
 congr! 1;
 · exact condSet_upClosed n D.1;
 · exact mrungSet_upClosed _ _;
 · exact condSet_nonempty _ _;
 · exact mrungSet_nonempty _ _;
 · ext j; simp [condSet, mrungSet];
 convert Roots.inBW_succ_conductor_split n j D using 1

/-! ### The `μ`-conductor in terms of the conductor (`ν_λ(μ) = 2`) -/

/-
For `j ≥ 2`, the `μ`-conductor membership is the conductor membership two rungs down:
`λ^j·v ∈ μ·BW_n ⟺ cond n v + 2 ≤ j`. This is the `+2` rung shift that matches the
`2|U| = 2|U'| + 2` shift of the Möbius defect.
-/
theorem mem_mrungSet_iff_of_two_le (n : ℕ) (v : BWVec n) {j : ℕ} (hj : 2 ≤ j) :
 j ∈ mrungSet n v ↔ cond n v + 2 ≤ j := by
 convert inOneIBW_lam_pow_iff n j hj v using 1;
 convert mem_condSet_iff n v ( j := j - 2 ) |> Iff.symm using 1;
 omega

/-
The `μ`-conductor never exceeds `cond + 2`.
-/
theorem mrung_le_cond_add_two (n : ℕ) (v : BWVec n) : mrung n v ≤ cond n v + 2 := by
 convert Nat.sInf_le _;
 by_cases h : 2 ≤ cond n v + 2 <;> simp_all +decide [ mem_mrungSet_iff_of_two_le ]

/-! ## Item 2 — the grade equals the phase-vector conductor (`grade = phaseCond`)

A diagonal operator `D` on `n` qubits acts on a vector `v ∈ BW_n` by the pointwise product
`bwMul n D v`, and its phase vector is `D` itself (its leaf values are the phases
`ζ₈^{e(b)}`). The grade `graden n D` is the least `k` with `λ^k·D` mapping `BW_n` into
`BW_n`; the phase-vector conductor `cond n D` is the least `k` with `λ^k·D ∈ BW_n` (the
requirement of the all-ones generator column `𝟙 = bwId`, the hardest column).

The identification `graden n D = cond n D` is **Item 2** of the general-n synthesis. Its
engine is the ring-theoretic fact that `BW_n` is closed under the pointwise product
(`bwMul_inBW`): then `λ^k·D ∈ BW_n` already forces `λ^k·D` to map all of `BW_n` into
`BW_n`, and conversely the all-ones column `𝟙 ∈ BW_n` extracts `λ^k·D ∈ BW_n` from the
map condition. -/

/-
`bwMul` is commutative (pointwise product of `R`-leaves).
-/
theorem bwMul_comm (n : ℕ) (a b : BWVec n) : bwMul n a b = bwMul n b a := by
 induction' n with n ih;
 · grind +suggestions;
 · exact Prod.ext ( ih _ _ ) ( ih _ _ )

/-
Pointwise distributivity of `bwMul` over `bwSub` in the *value* slot:
`a·b − a·c = a·(b − c)`.
-/
theorem bwMul_bwSub (n : ℕ) (a b c : BWVec n) :
 bwSub n (bwMul n a b) (bwMul n a c) = bwMul n a (bwSub n b c) := by
 induction' n with n ih;
 · apply Eq.symm; exact (by
 have h_mul_sub : ∀ (x y z : Z8), (x * y) - (x * z) = x * (y - z) := by
 exact fun x y z => by rw [ mul_sub ] ;
 convert h_mul_sub a b c |> Eq.symm using 1);
 · exact Prod.ext ( ih _ _ _ ) ( ih _ _ _ )

/-
The scalar of a `bwSmul`-ed value pulls out of `bwMul` on the right.
-/
theorem bwSmul_bwMul_right (n : ℕ) (r : Z8) (a v : BWVec n) :
 bwMul n a (bwSmul n r v) = bwSmul n r (bwMul n a v) := by
 induction' n with n ih;
 · -- By definition of multiplication in Z8, we have a * (r * v) = r * (a * v).
 have h_mul_comm : ∀ (a v r : Z8), a * (r * v) = r * (a * v) := by
 grind;
 exact h_mul_comm _ _ _;
 · exact Prod.ext ( ih _ _ ) ( ih _ _ )

/-
**`BW_n` is closed under the pointwise product.** This is the order/ring closure of the
Barnes–Wall lattice: the lattice is a multiplicatively closed subset, so the all-ones column
is the hardest (the conductor of a diagonal operator equals that of its phase vector).
-/
theorem bwMul_inBW (n : ℕ) {a b : BWVec n} (ha : inBW n a) (hb : inBW n b) :
 inBW n (bwMul n a b) := by
 induction' n with n ih;
 · exact inBW_zero (bwMul 0 a b)
 · obtain ⟨wa, hwa⟩ := ha
 obtain ⟨wb, hwb⟩ := hb;
 refine' ⟨ _, _, _ ⟩;
 · exact ih wa wb;
 · exact ih hwa.1 hwb.1;
 · obtain ⟨wa', hwa'⟩ := hwa.2
 obtain ⟨wb', hwb'⟩ := hwb.2;
 refine' ⟨ bwAdd n ( bwMul n b.1 wa' ) ( bwMul n a.2 wb' ), _, _ ⟩;
 · exact bwAdd_inBW _ ( ih wb hwa'.1 ) ( ih hwa.1 hwb'.1 );
 · rw [ ← bwSmul_bwAdd ];
 rw [ ← bwSmul_bwMul_right, ← bwSmul_bwMul_right ];
 rw [ ← hwa'.2, ← hwb'.2 ];
 rw [ ← bwMul_bwSub, ← bwMul_bwSub ];
 rw [ show bwMul n b.1 a.1 = bwMul n a.1 b.1 from bwMul_comm _ _ _, show bwMul n b.1 a.2 = bwMul n a.2 b.1 from bwMul_comm _ _ _ ];
 exact Eq.symm (bwAdd_bwSub_telescope n (bwMul n a.1 b.1) (bwMul n a.2 b.1) (bwMul n a.2 b.2))

/-
`λ^k·D ∈ BW_n` is equivalent to `λ^k·D` mapping `BW_n` into `BW_n`: the conductor of a
diagonal operator is governed by its all-ones column.
-/
theorem mapsToBW_iff_inBW (n : ℕ) (E : BWVec n) :
 MapsToBW n E ↔ inBW n E := by
 constructor;
 · intro hE;
 convert hE ( bwId n ) ( Roots.bwId_inBW n ) using 1;
 rw [bwMul_comm, Roots.bwId_mul]
 · intro hE;
 exact fun v hv => bwMul_inBW n hE hv

/-
**Item 2 — grade `=` phase-vector conductor.** For every diagonal operator `D` on `n`
qubits, the lattice grade equals the `λ`-adic conductor of its phase vector.
-/
theorem graden_eq_cond (n : ℕ) (D : BWVec n) : graden n D = cond n D := by
 refine' congr_arg _ ( Set.ext fun k => _ );
 simp +decide [ gradeLEn, mapsToBW_iff_inBW ];
 rfl

/-- **The general-`n` grade recursion.** Combining Item 2 (`graden_eq_cond`) with the
conductor recursion (`cond_succ`), the lattice grade of a depth-`(n+1)` diagonal operator
splits as the `max` of the grade of its `x_n = 0` slice and the `μ`-conductor of the
difference of its two slices. This is the kernel-checked general-`n` form of the BW
`(u, u+v)` grade recursion. -/
theorem graden_succ_eq (n : ℕ) (D : BWVec (n + 1)) :
 graden (n + 1) D = max (graden n D.1) (mrung n (bwSub n D.1 D.2)) := by
 rw [graden_eq_cond, cond_succ, graden_eq_cond]

end Roots.MoebiusGrade