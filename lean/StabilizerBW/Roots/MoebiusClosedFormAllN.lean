import StabilizerBW.Roots.StrictSubsetLowerBoundAllN

/-!
# Towards the general-`n` Möbius closed form

The multi-monomial grade closed form was kernel-verified at `n ≤ 5` on the full
32-case table (`StabilizerBW/Roots/MultimonomialClosedForm.lean`):

```
 grade(D_e) = max_{∅ ≠ U ⊆ supp(e)} ( 2|U| − ν_λ(m_U(e)) ),
 m_U(e) = Σ_{V ⊆ U} (−1)^{|U|−|V|} · ζ₈^{σ_V}, σ_V = e(1_V) (mod 8).
```

The target here is to lift this to a general-`n` theorem. The proof route is the
Barnes–Wall `(u, u+v)` free-module recursion: splitting the coordinate set as
`{1,…,n−1} ⊔ {n}` the phase vector `w_e ∈ ℤ[ζ₈]^{2ⁿ}` decomposes as
`w_e = (w^{(0)}, w^{(1)})`, and the headline **structural** lemma is that the Möbius /
down-set transform `m_U` commutes with this split.

This file proves that headline structural lemma as a **pure combinatorial identity over an
arbitrary commutative ring** (`mob_split`), together with the supporting facts needed to
drive the induction (the `n ∉ U` congruence `mob_congr`, and Möbius inversion
`mob_inversion`). This is the **down-set / finite-difference transform** in full
generality.

It then closes **steps 1–3** of the attack plan over the canonical Barnes–Wall
infrastructure (`Roots/BWn.lean`), as the reusable theorems `bwSmul_lam_split` (phase-vector
split), `inBW_succ_conductor_split` (conductor decomposition), `inOneIBW_lam_pow_iff`
(`μ`-rung count `ν_λ(μ) = 2`), and the combined level-`n` conductor recursion
`inBW_succ_lam_iff` — the exact recursion the general-`n` Möbius induction (step 4) consumes.

## A correction to the naïve form of the lemma

One naïve form of the split lemma writes
`m_U(e) = m_{U'}(e^{(1)} − e^{(0)})`, i.e. as the Möbius transform of the *difference of
the phases*. Taken literally over `ℤ[ζ₈]` that is **false**: `ζ^a − ζ^b ≠ ζ^{a−b}`. The
correct down-set identity is the Möbius transform of the *difference of the phase-vector
values*:

```
 m_U(e) = Σ_{V' ⊆ U'} (−1)^{|U'|−|V'|} · ( ζ₈^{e^{(1)}(1_{V'})} − ζ₈^{e^{(0)}(1_{V'})} ).
```

This is exactly what the BW recursion needs: the inner half is built from the *difference
vector* `w^{(1)} − w^{(0)}` (the `v`-component of the `(u, u+v)` split), and `m_U` of the
full `e` is the inner Möbius transform of that difference vector. We prove this corrected
form; abstractly, `f V' ↦ ζ₈^{e(1_{V'},·)}` and the "difference phase" is the difference of
the two `R`-valued slices of `f`, not a subtraction inside the exponent.

## What this delivers

This is the partial general-n step: steps 1–3 (the conductor decomposition)
are delivered as usable theorems over the canonical lattice, alongside the
Möbius-commutes-with-`(u, u+v)` down-set core. Only step 4 (the Möbius↔conductor induction
synthesis, which additionally needs an all-`n` `grade = phaseCond` identification) remains
for the general-n closed form; it is documented in `Proofs/R10_T2_general_n.md`. Everything here is
kernel-clean (no `sorry`, `axiom`, `native_decide`, or `@[implemented_by]`).
-/

namespace Roots.MoebiusAllN

open Finset

variable {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]

/-- The **down-set (Möbius / finite-difference) transform** of `f : Finset α → R` at `U`:
`m_U(f) = Σ_{V ⊆ U} (−1)^{|U|−|V|} · f V`.

Instantiated at `f V = ζ₈^{σ_V}` (with `σ_V = e(1_V)`) over `R = ℤ[ζ₈]`, this is exactly
the `m_U(e)` of the closed form. -/
def mob (f : Finset α → R) (U : Finset α) : R :=
 ∑ V ∈ U.powerset, (-1 : R) ^ (U.card - V.card) * f V

/-
**Congruence:** the transform `mob f U` only depends on the values of `f` on subsets of
`U`. In the BW split this is the `n ∉ U` case: `m_U` only sees the `x_n = 0` slice.
-/
theorem mob_congr {f g : Finset α → R} {U : Finset α}
 (h : ∀ V ⊆ U, f V = g V) : mob f U = mob g U := by
 exact Finset.sum_congr rfl fun V hV => by aesop;

/-
**The headline structural lemma — Möbius commutes with the `(u, u+v)` split.**

For `a ∈ U` (the split coordinate, `a = n`) write `U' = U.erase a`. Then the Möbius
transform of `f` at `U` equals the Möbius transform, at `U'`, of the *finite difference*
`W ↦ f (insert a W) − f W` (the difference of the two `a`-slices of `f`).

Over `R = ℤ[ζ₈]` with `f V = ζ₈^{σ_V}`, the difference `f (insert a W) − f W` is exactly
the `v`-component `ζ₈^{e^{(1)}(1_W)} − ζ₈^{e^{(0)}(1_W)}` of the BW `(u, u+v)` split, so
`m_U(e) = m_{U'}(w^{(1)} − w^{(0)})`.
-/
theorem mob_split (f : Finset α → R) {a : α} {U : Finset α} (ha : a ∈ U) :
 mob f U = mob (fun W => f (insert a W) - f W) (U.erase a) := by
 unfold mob;
 rw [ show U = insert a ( U.erase a ) by rw [ Finset.insert_erase ha ], Finset.sum_powerset_insert ];
 · simp +decide [ ← Finset.sum_add_distrib, mul_sub ];
 rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Nat.sub_add_comm ( Finset.card_le_card <| Finset.mem_powerset.mp hx ) ] ; ring;
 grind;
 · simp +decide

/-
**Möbius inversion (reconstruction).** The down-set sum of the transform recovers `f`:
`f U = Σ_{V ⊆ U} mob f V`. This certifies that `mob` is a genuine invertible change of
basis (so no information is lost passing from the phase vector to its Möbius syndromes).
-/
theorem mob_inversion (f : Finset α → R) (U : Finset α) :
 ∑ V ∈ U.powerset, mob f V = f U := by
 induction' U using Finset.induction with a U ha ih generalizing f;
 · simp +decide [ mob ];
 · -- By the properties of the Möbius transform, we can split the sum into two parts: one over subsets containing $a$ and one over subsets not containing $a$.
 have h_split : ∑ V ∈ (insert a U).powerset, mob f V = ∑ V ∈ U.powerset, mob f V + ∑ V ∈ U.powerset, mob f (insert a V) :=
 Finset.sum_powerset_insert ha (mob f)
 -- By the properties of the Möbius transform, we can rewrite the second sum as $\sum_{V \subseteq U} mob (fun W => f (insert a W) - f W) V$.
 have h_rewrite : ∑ V ∈ U.powerset, mob f (insert a V) = ∑ V ∈ U.powerset, mob (fun W => f (insert a W) - f W) V := by
 refine' Finset.sum_congr rfl fun V hV => _;
 convert mob_split f _ using 1;
 rw [ Finset.erase_insert ( Finset.notMem_mono ( Finset.mem_powerset.mp hV ) ha ) ];
 exact Finset.mem_insert_self _ _;
 simp_all +decide [ mob ]

end Roots.MoebiusAllN

/-!
## The canonical Barnes–Wall conductor decomposition (Steps 1–3)

The combinatorial `mob_split` above is the *down-set* half of the general-`n` argument.
This section delivers the *conductor* half over the canonical Barnes–Wall infrastructure
(`Roots/BWn.lean`, `Roots/LowerBoundAllN.lean`), namely steps 1–3 of the attack
plan, as reusable theorems.

Throughout, a diagonal phase operator on `n+1` qubits is a `BWVec (n+1) = BWVec n × BWVec n`,
whose two halves `D.1` (the `x_n = 0` slice `w^{(0)}`) and `D.2` (the `x_n = 1` slice
`w^{(1)}`) are the *phase-vector split* of step 1. We write the inner `μ`-lattice
`μ·BW_n = (1+i)·BW_n` via the predicate `inOneIBW`.

* **Step 1 (`bwSmul_lam_split`)** — the phase-vector split: scaling by `λ^j` acts halfwise.
* **Step 2 (`inBW_succ_conductor_split`)** — the conductor decomposition: membership of
 `λ^j·w_e` in `BW_{n+1}` is equivalent to membership of the outer half `λ^j·w^{(0)}` in
 `BW_n` together with membership of the difference `λ^j·(w^{(0)}−w^{(1)})` in `μ·BW_n`.
* **Step 3 (`inOneIBW_lam_pow_iff`)** — the `μ`-rung count `ν_λ(μ) = 2`:
 `λ^j·v ∈ μ·BW_n ⇔ λ^{j−2}·v ∈ BW_n`.
* **Steps 2+3 combined (`inBW_succ_lam_iff`)** — the canonical phase-vector conductor
 recursion `λ^j·w_e ∈ BW_{n+1} ⇔ λ^j·w^{(0)} ∈ BW_n ∧ λ^{j−2}·(w^{(0)}−w^{(1)}) ∈ BW_n`
 (for `j ≥ 2`).

Sign note: the inner half can equivalently be written as `w^{(1)} − w^{(0)}`; the
canonical lattice is closed under negation, so we use `w^{(0)} − w^{(1)} = bwSub n D.1 D.2`
to match the direction of `Roots.inBW_succ_iff`.
-/

namespace Roots
open Z8

/-- Membership in the inner `μ`-lattice `μ·BW_n = (1+i)·BW_n`. -/
def inOneIBW (n : ℕ) (v : BWVec n) : Prop :=
 ∃ w, inBW n w ∧ v = bwSmul n oneI w

/-
`μ·BW_n ⊆ BW_n`: the inner lattice is contained in the full lattice.
-/
theorem inOneIBW_imp_inBW (n : ℕ) {v : BWVec n} (h : inOneIBW n v) : inBW n v := by
 obtain ⟨ w, hw, rfl ⟩ := h; exact Roots.bwSmul_inBW n Z8.oneI hw;

/-- **Step 1 — phase-vector split.** Scaling a depth-`(n+1)` phase vector by `λ^j` acts
halfwise on the two slices `w^{(0)} = D.1`, `w^{(1)} = D.2`. -/
theorem bwSmul_lam_split (n j : ℕ) (D : BWVec (n + 1)) :
 bwSmul (n + 1) (Z8.lam ^ j) D
 = (bwSmul n (Z8.lam ^ j) D.1, bwSmul n (Z8.lam ^ j) D.2) := rfl

/-
**Step 2 — conductor decomposition.** `λ^j·w_e ∈ BW_{n+1}` iff the outer half
`λ^j·w^{(0)} ∈ BW_n` and the difference `λ^j·(w^{(0)}−w^{(1)}) ∈ μ·BW_n`. This is the
canonical-lattice form of the model's `inBWb` `(u, u+v)` recursion, with the redundant
middle conjunct `w^{(1)} ∈ BW_n` of `inBW_succ_iff` absorbed (`μ·BW_n ⊆ BW_n`).
-/
theorem inBW_succ_conductor_split (n j : ℕ) (D : BWVec (n + 1)) :
 inBW (n + 1) (bwSmul (n + 1) (Z8.lam ^ j) D) ↔
 inBW n (bwSmul n (Z8.lam ^ j) D.1) ∧
 inOneIBW n (bwSmul n (Z8.lam ^ j) (bwSub n D.1 D.2)) := by
 constructor <;> intro H;
 · constructor;
 · cases H ; aesop;
 · convert H.2.2 using 1;
 simp +decide [ bwSmul_bwSub ];
 rfl;
 · -- By definition of `inBW`, we know that if `in BW n (bwSmul n (lam ^ j) D.1)` and `inOneIBW n (bwSmul n (lam ^ j) (bwSub n D.1 D.2))`, then `in BW n (bwSmul n (lam ^ j) D.2)`.
 have h_inBW_D2 : inBW n (bwSmul n (lam ^ j) D.2) := by
 convert bwSub_inBW n H.1 ( inOneIBW_imp_inBW n H.2 ) using 1;
 -- By induction on n, we can show that the difference of the two bwSmul terms is equal to the bwSmul of the difference.
 have h_ind : ∀ n (a b : BWVec n), bwSub n (bwSmul n (lam ^ j) a) (bwSmul n (lam ^ j) (bwSub n a b)) = bwSmul n (lam ^ j) b := by
 intro n a b; induction' n with n ih <;> simp_all +decide [ bwSub, bwSmul ] ;
 grind;
 rw [ h_ind ];
 exact ⟨ H.1, h_inBW_D2, by
 obtain ⟨ w, hw₁, hw₂ ⟩ := H.2;
 use w;
 exact ⟨ hw₁, by rw [ ← hw₂, bwSmul_lam_split, bwSmul_bwSub ] ⟩ ⟩

/-
**Step 3 — `μ`-rung count `ν_λ(μ) = 2`.** For `j ≥ 2`, `λ^j·v` lies in `μ·BW_n` iff
`λ^{j−2}·v` lies in `BW_n`; the `μ = (1+i)` factor consumes exactly two `λ`-rungs
(`λ² = μ·u` with `u` a unit).
-/
theorem inOneIBW_lam_pow_iff (n j : ℕ) (hj : 2 ≤ j) (v : BWVec n) :
 inOneIBW n (bwSmul n (Z8.lam ^ j) v) ↔ inBW n (bwSmul n (Z8.lam ^ (j - 2)) v) := by
 have h_lam_j : Z8.lam ^ j = Z8.oneI * Z8.uu * Z8.lam ^ (j - 2) := by
 rw [ show lam ^ j = lam ^ 2 * lam ^ ( j - 2 ) by rw [ ← pow_add, Nat.add_sub_of_le hj ], show lam ^ 2 = oneI * uu by exact Z8.lam_sq ];
 constructor <;> intro H;
 · obtain ⟨ w, hw, hw' ⟩ := H;
 have h_eq : w = bwSmul n (Z8.uu * Z8.lam ^ (j - 2)) v := by
 apply bwSmul_oneI_inj n;
 rw [ ← hw', h_lam_j, mul_assoc, bwSmul_bwSmul ];
 have h_eq : bwSmul n (Z8.uuInv) w = bwSmul n (Z8.lam ^ (j - 2)) v := by
 convert bwSmul_bwSmul n Z8.uuInv ( Z8.uu * Z8.lam ^ ( j - 2 ) ) v using 1;
 · rw [h_eq];
 · rw [ ← mul_assoc, show uuInv * uu = 1 from by decide, one_mul ];
 exact h_eq ▸ Roots.bwSmul_inBW n _ hw;
 · use bwSmul n Z8.uu (bwSmul n (Z8.lam ^ (j - 2)) v);
 simp_all +decide [ ← bwSmul_bwSmul ];
 exact bwSmul_inBW _ _ H

/-
**Steps 2 + 3 — the canonical phase-vector conductor recursion.** For `j ≥ 2`,
`λ^j·w_e ∈ BW_{n+1}` iff `λ^j·w^{(0)} ∈ BW_n` and `λ^{j−2}·(w^{(0)}−w^{(1)}) ∈ BW_n`. This is
the exact level-`n` conductor recursion the general-`n` Möbius induction consumes: the
`+2` rung shift on the difference vector matches the `2|U| = 2|U'| + 2` shift in the
Möbius `defect_U`.
-/
theorem inBW_succ_lam_iff (n j : ℕ) (hj : 2 ≤ j) (D : BWVec (n + 1)) :
 inBW (n + 1) (bwSmul (n + 1) (Z8.lam ^ j) D) ↔
 inBW n (bwSmul n (Z8.lam ^ j) D.1) ∧
 inBW n (bwSmul n (Z8.lam ^ (j - 2)) (bwSub n D.1 D.2)) := by
 rw [Roots.inBW_succ_conductor_split, Roots.inOneIBW_lam_pow_iff n j hj]

end Roots