import RequestProject.Roots.LowerBoundAllN

/-!
# The general-`n` strict-subset lower bound 

This file extends the corner-valuation lower bound of `LowerBoundAllN.lean` from the
maximal monomial `D_{x_{1⋯n}}` (support `S = {1,…,n}`, `d = n`) to **every** subset
`S ⊆ {1,…,n}` with `|S| = d`, including the strict-subset case `d < n`.

By Clifford bit-permutation symmetry the grade of a single monomial character depends
only on `d = |S|` and the corner-phase valuation `ν`, not on the particular bits in `S`.
We therefore work with the canonical leading-`d` placement `topMon n d s`
(from `UpperBoundAllN.lean`), which puts the monomial on the leading `d` qubits and the
identity on the trailing `n − d` qubits. This is exactly the `D_{c·x_S}` of the round
prompt with `|S| = d`.

## Main results

* `topProj_inBW_iff` — the **sub-coordinate conductor**: the leading-`d` projector
 scaled by `λ^j` lies in `BW_n` iff `2d ≤ j`. This is the `cornerS_inBW_iff` of the
 prompt; for `d = n` it is `corner_inBW_iff` (since `topProj n n = bwCorner n`).
* `topMon_subset_not_inBW`, `topMon_subset_graden_ge` — the valuation lower bound for
 the general single monomial.
* `topMon_subset_graden_eq` — the exact grade `g(D_{c·x_S}) = 2d − p` whenever
 `s − 1 = λ^p·u` with `u` a unit and `p < 2d`.
* `graden_subsetMon_zeta_eq`, `graden_subsetMon_iu_eq`, `graden_subsetMon_negOne_eq` —
 the named `ν ∈ {0,1,2}` instances:
 * `ν = 0`: `g(D_{x_S}) = 2d − 1` (`d ≥ 1`),
 * `ν = 1`: `g(D_{2·x_S}) = 2d − 2` (`d ≥ 2`),
 * `ν = 2`: `g(D_{4·x_S}) = 2d − 4` (`d ≥ 3`).

These close the single-monomial side of the linear closed form `w(d,ν) = 2d − 2^ν` at
every `n` and every `S ⊆ {1,…,n}`.
-/

namespace Roots
open Z8

/-! ## The corner coordinate of `bwId` and `topProj` -/

/-- The corner (all-ones) coordinate of the identity diagonal is `1`. -/
theorem cornerCoord_bwId (n : ℕ) : cornerCoord n (bwId n) = 1 := by
 induction n with
 | zero => rfl
 | succ m ih => exact ih

/-- The corner coordinate of the leading-`d` projector is `1` (when `d ≤ n`).
The corner functional follows the `.2` (the "qubit = 1") branch all the way down; the
leading `d` constrained qubits keep that branch alive and the trailing `bwId (n − d)`
contributes its corner coordinate `1`. -/
theorem cornerCoord_topProj (n d : ℕ) (hd : d ≤ n) :
 cornerCoord n (topProj n d) = 1 := by
 induction n generalizing d with
 | zero =>
 interval_cases d
 exact cornerCoord_bwId 0
 | succ m ih =>
 cases d with
 | zero => simpa using cornerCoord_bwId (m + 1)
 | succ k =>
 rw [topProj_succ_succ, cornerCoord_succ]
 exact ih k (by omega)

/-! ## The sub-coordinate conductor (the heart of T1)

We prove simultaneously, by induction on `d` (with `n`, `j` generalized):

* `inBW n (λ^j · topProj n d) ↔ 2d ≤ j` (the conductor),
* `(λ^j · topProj n d ∈ (1+i)·BW_n) ↔ 2d + 2 ≤ j` (the one-level-deeper conductor),

mirroring `corner_inBW_iff` / `corner_inOneIL_iff` from `LowerBoundAllN.lean` but with
`topProj n d` in place of `bwCorner n`. The base `d = 0` is the `bwId` case; the step
`d + 1` peels the outermost constrained qubit `(bwZero, topProj n d)`, where the syndrome
condition is exactly the inner one-level-deeper conductor at `d`. -/

/-
**The one-level-deeper conductor, conditional on the membership conductor.** Given
that `λ^{j'}·(topProj n d)` lies in `BW_n` iff `2d ≤ j'`, the same vector lies in
`(1+i)·BW_n` iff `2d + 2 ≤ j`. This is the `corner_inOneIL_iff` argument with
`topProj n d` for `bwCorner n` and the membership conductor supplied as a hypothesis.
No induction: it is a self-contained valuation argument via `cornerCoord_topProj`.
-/
theorem topProj_inOneIL_iff_of_inBW (n d : ℕ) (hd : d ≤ n)
 (hB : ∀ j', inBW n (bwSmul n (Z8.lam ^ j') (topProj n d)) ↔ 2 * d ≤ j') (j : ℕ) :
 (∃ w, inBW n w ∧
 bwSub n (bwZero n) (bwSmul n (Z8.lam ^ j) (topProj n d)) = bwSmul n oneI w)
 ↔ 2 * d + 2 ≤ j := by
 constructor;
 · intro h
 obtain ⟨w, hw₁, hw₂⟩ := h
 have h_oneI_div : oneI ∣ lam ^ j := by
 replace hw₂ := congr_arg ( fun x => cornerCoord n x ) hw₂ ; simp_all +decide [ cornerCoord_bwSub, cornerCoord_bwZero, cornerCoord_bwSmul, cornerCoord_topProj ];
 exact ⟨ -cornerCoord n w, by simpa using congr_arg Neg.neg hw₂ ⟩
 have h_j_ge_2 : 2 ≤ j := by
 exact two_le_of_oneI_dvd_lam_pow h_oneI_div
 have h_w : w = bwSmul n (-(uu) * lam ^ (j - 2)) (topProj n d) := by
 have h_w : -(lam ^ j) = oneI * (-uu * lam ^ (j - 2)) := by
 rw [ show lam ^ j = lam ^ 2 * lam ^ ( j - 2 ) by rw [ ← pow_add, Nat.add_sub_of_le h_j_ge_2 ] ] ; ring;
 rw [ show lam ^ 2 = oneI * uu by exact Z8.lam_sq ] ; ring!;
 apply bwSmul_oneI_inj n;
 grind +suggestions
 have h_w_inBW : inBW n (bwSmul n (lam ^ (j - 2)) (topProj n d)) := by
 convert bwSmul_inBW n ( -Z8.uuInv ) hw₁ using 1 ; ring;
 rw [h_w];
 rw [ bwSmul_bwSmul ] ; ring;
 rw [ mul_assoc, show uuInv * uu = 1 from by decide, mul_one ]
 have h_j_ge_2d : 2 * d ≤ j - 2 := by
 exact hB _ |>.1 h_w_inBW
 linarith [Nat.sub_add_cancel (by linarith : 2 ≤ j)];
 · intro hj
 use bwSmul n (-Z8.uu * Z8.lam ^ (j - 2)) (topProj n d);
 constructor;
 · convert bwSmul_inBW n ( -Z8.uu ) ( hB ( j - 2 ) |>.2 ( by omega ) ) using 1;
 rw [bwSmul_bwSmul];
 · rw [ ← Nat.add_sub_cancel' ( by linarith : 2 ≤ j ), pow_add ];
 rw [ Z8.lam_sq ] ; ring;
 simp +decide [ mul_assoc, mul_left_comm, bwSub_bwZero_left, bwSmul_bwSmul ]

/-
**Sub-coordinate conductor (T1, `cornerS_inBW_iff`).** The leading-`d` projector
scaled by `λ^j` lies in `BW_n` iff `2d ≤ j`. Generalizes `corner_inBW_iff` (`d = n`).
-/
theorem topProj_inBW_iff (d : ℕ) : ∀ (n j : ℕ), d ≤ n →
 (inBW n (bwSmul n (Z8.lam ^ j) (topProj n d)) ↔ 2 * d ≤ j) := by
 induction' d with k ih;
 · intro n j hn
 simp only [Nat.mul_zero, Nat.zero_le, iff_true];
 convert bwSmul_inBW n ( Z8.lam ^ j ) ( bwId_inBW n ) using 1;
 cases n <;> rfl;
 · intro n j hn;
 obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0);
 rw [ topProj_succ_succ, bwSmul_succ ];
 rw [ inBW_succ_iff, bwSmul_bwZero ];
 constructor <;> intro h;
 · have := topProj_inOneIL_iff_of_inBW m k ( by linarith ) ( fun j' => ih m j' ( by linarith ) ) j; simp_all +decide [ Nat.mul_succ ] ;
 · have := topProj_inOneIL_iff_of_inBW m k ( by linarith ) ( fun j' => ih m j' ( by linarith ) ) j;
 exact ⟨ bwZero_inBW m, ih m j ( by linarith ) |>.2 ( by linarith ), this.mpr ( by linarith ) ⟩

/-! ## The strict-subset lower bound -/

/-- The defect identity for the leading-`d` monomial:
`λ^k·D − λ^k·I = λ^k·(s−1)·Q` where `Q = topProj n d`. -/
theorem bwSub_topMon_bwId (n d k : ℕ) (s : Z8) :
 bwSub n (bwSmul n (Z8.lam ^ k) (topMon n d s)) (bwSmul n (Z8.lam ^ k) (bwId n))
 = bwSmul n (Z8.lam ^ k * (s - 1)) (topProj n d) := by
 unfold topMon
 rw [← bwSmul_bwAdd, bwSub_bwAdd_left_cancel, bwSmul_bwSmul]

/-
**General strict-subset lower bound (all `ν`).** If `s − 1 = λ^p·u` for a unit `u` and
`p < 2d ≤ 2n`, then `λ^{2d−p−1}·(topMon n d s)` does not preserve `BW_n`: the all-ones
witness `bwId` reduces it to `λ^{2d−1}·Q`, of valuation one short of the conductor depth
`2d`.
-/
theorem topMon_subset_not_inBW (n d p : ℕ) (s u : Z8) (hu : IsUnit u)
 (hs : s - 1 = Z8.lam ^ p * u) (hp : p < 2 * d) (hd : d ≤ n) :
 ¬ inBW n (bwSmul n (Z8.lam ^ (2 * d - p - 1)) (topMon n d s)) := by
 intro h_inBW
 have h_defect : inBW n (bwSmul n (lam ^ (2 * d - 1)) (topProj n d)) := by
 convert bwSmul_inBW n ( hu.unit⁻¹.val ) ( show inBW n ( bwSmul n ( u * lam ^ ( 2 * d - 1 ) ) ( topProj n d ) ) from ?_ ) using 1;
 · convert bwSmul_bwSmul n ( hu.unit⁻¹.val ) ( u * lam ^ ( 2 * d - 1 ) ) ( topProj n d ) |> Eq.symm using 1;
 simp +decide [ ← mul_assoc ];
 · convert bwSub_inBW n h_inBW ( bwSmul_inBW n ( lam ^ ( 2 * d - p - 1 ) ) ( bwId_inBW n ) ) using 1;
 rw [ bwSub_topMon_bwId ];
 rw [ hs ] ; ring;
 rw [ show d * 2 - 1 = d * 2 - p - 1 + p by omega, pow_add, mul_assoc ];
 grind +suggestions

/-- **General strict-subset lower bound on the grade (all `ν`).**
`graden n (topMon n d s) ≥ 2d − p`. -/
theorem topMon_subset_graden_ge (n d p : ℕ) (s u : Z8) (hu : IsUnit u)
 (hs : s - 1 = Z8.lam ^ p * u) (hp : p < 2 * d) (hd : d ≤ n) :
 2 * d - p ≤ graden n (topMon n d s) := by
 by_contra hlt
 push_neg at hlt
 have hmem : gradeLEn n (topMon n d s) (graden n (topMon n d s)) :=
 Nat.sInf_mem (gradeLEn_nonempty n (topMon n d s))
 have hg : gradeLEn n (topMon n d s) (2 * d - p - 1) := gradeLEn_of_le hmem (by omega)
 have := hg (bwId n) (bwId_inBW n)
 rw [bwSmul_bwMul_left, bwMul_bwId_right] at this
 exact topMon_subset_not_inBW n d p s u hu hs hp hd this

/-- **Exact grade (all `ν`), general single monomial.** `graden (topMon n d s) = 2d − p`
whenever `s − 1 = λ^p·u` with `u` a unit and `p < 2d ≤ 2n`. -/
theorem topMon_subset_graden_eq (n d p : ℕ) (s u : Z8) (hu : IsUnit u)
 (hs : s - 1 = Z8.lam ^ p * u) (hp : p < 2 * d) (hd : d ≤ n) :
 graden n (topMon n d s) = 2 * d - p :=
 le_antisymm (topMon_graden_le n d p s u hs) (topMon_subset_graden_ge n d p s u hu hs hp hd)

/-! ## The named `ν ∈ {0,1,2}` strict-subset grades -/

/-- **`ν = 0` exact grade:** `g(D_{x_S}) = 2d − 1` for every `S` with `|S| = d ≥ 1`
(and `d ≤ n`). -/
theorem graden_subsetMon_zeta_eq (n d : ℕ) (hd : d ≤ n) (hd1 : 1 ≤ d) :
 graden n (topMon n d Z8.zeta) = 2 * d - 1 := by
 apply topMon_subset_graden_eq n d 1 Z8.zeta (-1) isUnit_neg_one scalar_zeta (by omega) hd

/-- **`ν = 1` exact grade:** `g(D_{2·x_S}) = 2d − 2` for every `S` with `|S| = d ≥ 2`
(and `d ≤ n`; at `d = 1` the gate is the Clifford `S`, grade `0`). -/
theorem graden_subsetMon_iu_eq (n d : ℕ) (hd : d ≤ n) (hd2 : 2 ≤ d) :
 graden n (topMon n d Z8.iu) = 2 * d - 2 := by
 apply topMon_subset_graden_eq n d 2 Z8.iu (Z8.iu * Z8.uuInv) isUnit_iu_uuInv scalar_iu
 (by omega) hd

/-- **`ν = 2` exact grade:** `g(D_{4·x_S}) = 2d − 4` for every `S` with `|S| = d ≥ 3`
(and `d ≤ n`; at `d ≤ 2` the gate is Clifford, grade `0`). -/
theorem graden_subsetMon_negOne_eq (n d : ℕ) (hd : d ≤ n) (hd3 : 3 ≤ d) :
 graden n (topMon n d (-1)) = 2 * d - 4 := by
 apply topMon_subset_graden_eq n d 4 (-1) (Z8.iu * Z8.uuInv * Z8.uuInv) isUnit_iu_uuInv_sq
 scalar_negOne (by omega) hd

/-! ## Consistency with the corner case `d = n` -/

/-- For `d = n` the strict-subset conductor recovers the corner conductor. -/
theorem topProj_inBW_iff_corner (n j : ℕ) :
 inBW n (bwSmul n (Z8.lam ^ j) (bwCorner n)) ↔ 2 * n ≤ j := by
 rw [← topProj_eq_bwCorner]
 exact topProj_inBW_iff n n j (le_refl n)

end Roots