import Mathlib

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Barnes-Wall Lattice for One Qubit

We formalize the single-qubit Barnes-Wall lattice over the Gaussian integers ℤ[i],
and prove that its minimal vectors correspond to the six Pauli eigenstates
(stabilizer states) up to multiplication by units in ℤ[i].

The Barnes-Wall lattice BW₁ is the sublattice of ℤ[i]² consisting of pairs (a, b)
such that (1+i) divides (a+b). When viewed as a real lattice in ℝ⁴ via the
standard embedding ℤ[i] ↪ ℝ², this is isomorphic to the D₄ root lattice.

We also define the single-qubit Clifford group via its action on the six stabilizer
state orbits and show this action generates a group of order 24 ≅ S₄.
-/

open Zsqrtd

namespace BarnesWall

/-! ## Basic Definitions -/

/-- A vector in ℤ[i]². -/
abbrev GVec := GaussianInt × GaussianInt

/-- The Gaussian integer (1 + i). -/
abbrev oneI : GaussianInt := ⟨1, 1⟩

/-- The Gaussian integer i. -/
abbrev gi : GaussianInt := ⟨0, 1⟩

/-- The single-qubit Barnes-Wall lattice: pairs (a, b) ∈ ℤ[i]² with (1+i) | (a+b).
 This corresponds to the D₄ root lattice under the standard real embedding. -/
def InBW (v : GVec) : Prop :=
 oneI ∣ (v.1 + v.2)

/-- Squared Hermitian norm of a vector in ℤ[i]²: |a|² + |b|². -/
def hermNormSq (v : GVec) : ℤ :=
 v.1.norm + v.2.norm

/-- A minimal vector of BW₁: in the lattice, nonzero, with the minimum nonzero
 squared norm (which equals 2). -/
def IsMinimal (v : GVec) : Prop :=
 InBW v ∧ v ≠ (0, 0) ∧ hermNormSq v = 2

/-- Unit equivalence: w = u · v for some unit u ∈ ℤ[i]* = {1, -1, i, -i}. -/
def UnitEquiv (v w : GVec) : Prop :=
 ∃ u : GaussianInt, IsUnit u ∧ w = (u * v.1, u * v.2)

/-! ## The Six Stabilizer State Representatives -/

/-- The six Pauli eigenstate representatives as vectors in ℤ[i]².
 These are (unnormalized) representatives of the six stabilizer states:
 - 0: (1+i, 0) ~ |0⟩
 - 1: (0, 1+i) ~ |1⟩
 - 2: (1, 1) ~ |+⟩
 - 3: (1, -1) ~ |−⟩
 - 4: (1, i) ~ |i⟩
 - 5: (1, -i) ~ |−i⟩ -/
def stabState : Fin 6 → GVec
 | 0 => (⟨1, 1⟩, 0)
 | 1 => (0, ⟨1, 1⟩)
 | 2 => (1, 1)
 | 3 => (1, -1)
 | 4 => (1, ⟨0, 1⟩)
 | 5 => (1, ⟨0, -1⟩)

/-! ## Main Theorems -/

/-- Each stabilizer state representative is a minimal vector. -/
theorem stab_isMinimal (k : Fin 6) : IsMinimal (stabState k) := by
 fin_cases k <;> simp +decide [ IsMinimal ];
 all_goals unfold InBW; simp +decide [ oneI ] ;
 all_goals unfold stabState; simp +decide [ dvd_iff_exists_eq_mul_left ] ;
 · exists ⟨ 1, -1 ⟩;
 · exists ⟨ 1, 0 ⟩;
 · exists ⟨ 0, -1 ⟩

/-
**Main Theorem (Part 1)**: The minimal vectors of BW₁ are exactly the unit
 multiples of the six stabilizer states.
-/
theorem minimal_iff_unitEquiv_stab (v : GVec) :
 IsMinimal v ↔ ∃ k : Fin 6, UnitEquiv (stabState k) v := by
 -- Let's start with the forward direction: assume v is minimal, show ∃ k, UnitEquiv (stabState k) v.
 apply Iff.intro
 intro hv
 have h_inBW : oneI ∣ (v.1 + v.2) := hv.left
 have h_nonzero : v ≠ (0, 0) := hv.right.left
 have h_hermNorm : v.1.norm + v.2.norm = 2 := hv.right.right
 have h_cases : (v.1.norm = 2 ∧ v.2.norm = 0) ∨ (v.1.norm = 0 ∧ v.2.norm = 2) ∨ (v.1.norm = 1 ∧ v.2.norm = 1) := by
 have h_cases : v.1.norm ≥ 0 ∧ v.2.norm ≥ 0 := by
 exact ⟨ v.1.norm_nonneg, v.2.norm_nonneg ⟩;
 omega;
 · rcases h_cases with h_cases | h_cases | h_cases <;> simp_all +decide [ Zsqrtd.norm ];
 · -- Since $v.1$ has norm 2, it must be a unit multiple of $(1+i)$.
 obtain ⟨u, hu⟩ : ∃ u : GaussianInt, IsUnit u ∧ v.1 = u * oneI := by
 have h_cases : v.1 = ⟨1, 1⟩ ∨ v.1 = ⟨-1, -1⟩ ∨ v.1 = ⟨1, -1⟩ ∨ v.1 = ⟨-1, 1⟩ := by
 have h_cases : v.1.re ^ 2 + v.1.im ^ 2 = 2 := by
 linarith;
 have : v.1.re ≤ 1 := Int.le_of_lt_add_one ( by nlinarith only [ h_cases ] ) ; ( have : v.1.re ≥ -1 := Int.le_of_lt_add_one ( by nlinarith only [ h_cases ] ) ; interval_cases _ : v.1.re <;> ( have : v.1.im ≤ 1 := Int.le_of_lt_add_one ( by nlinarith only [ h_cases ] ) ; ( have : v.1.im ≥ -1 := Int.le_of_lt_add_one ( by nlinarith only [ h_cases ] ) ; interval_cases _ : v.1.im <;> simp_all +decide only ; ) ) );
 · exact Or.inr <| Or.inl <| by ext <;> simp +decide [ * ] ;
 · exact Or.inr <| Or.inr <| Or.inr <| by ext <;> simp +decide [ * ] ;
 · exact Or.inr <| Or.inr <| Or.inl <| by ext <;> simp +decide [ * ] ;
 · exact Or.inl <| by ext <;> simp +decide [ * ] ;
 rcases h_cases with ( h | h | h | h ) <;> simp_all +decide [ oneI ];
 · exact ⟨ -1, isUnit_one.neg, by ext <;> simp +decide ⟩;
 · exists ⟨ 0, -1 ⟩;
 simp +decide [ isUnit_iff_exists_inv ];
 exists ⟨ 0, 1 ⟩;
 · exists ⟨ 0, 1 ⟩;
 simp +decide [ isUnit_iff_exists_inv ];
 exists ⟨ 0, -1 ⟩;
 -- Since $v.2$ has norm 0, it must be 0.
 have h_v2_zero : v.2 = 0 := by
 exact Zsqrtd.ext ( by norm_num; nlinarith ) ( by norm_num; nlinarith );
 use 0; use u; aesop;
 · -- Since $v.1.re * v.1.re + v.1.im * v.1.im = 0$, we have $v.1 = 0$.
 have h_v1_zero : v.1 = 0 := by
 exact Zsqrtd.ext ( by norm_num; nlinarith ) ( by norm_num; nlinarith );
 -- Since $v.2.re * v.2.re + v.2.im * v.2.im = 2$, we have $v.2 = u * (1 + i)$ for some unit $u$.
 obtain ⟨u, hu⟩ : ∃ u : GaussianInt, IsUnit u ∧ v.2 = u * oneI := by
 obtain ⟨ u, hu ⟩ := h_inBW;
 simp_all +decide [ mul_comm ];
 exact isUnit_iff_exists_inv.mpr ⟨ ⟨ u.re, -u.im ⟩, by ext <;> norm_num <;> linarith ⟩;
 use 1; use u; aesop;
 · -- Since $v.1$ and $v.2$ are units, we can write $v.1 = u$ and $v.2 = uw$ for some unit $w$.
 obtain ⟨u, hu⟩ : ∃ u : GaussianInt, IsUnit u ∧ v.1 = u := by
 simp_all +decide [ isUnit_iff_exists_inv ];
 use ⟨v.1.re, -v.1.im⟩;
 ext <;> simp +decide [ Zsqrtd.ext ] <;> linarith
 obtain ⟨w, hw⟩ : ∃ w : GaussianInt, IsUnit w ∧ v.2 = u * w := by
 obtain ⟨w, hw⟩ : ∃ w : GaussianInt, v.2 = u * w := by
 exact hu.1.dvd;
 simp_all +decide [ Zsqrtd.norm ];
 exact ⟨ w, by rw [ isUnit_iff_exists_inv ] ; exact ⟨ ⟨ w.re, -w.im ⟩, by ext <;> norm_num <;> nlinarith ⟩, Or.inl rfl ⟩;
 -- Since $w$ is a unit, we have $w \in \{1, -1, i, -i\}$.
 have hw_cases : w = 1 ∨ w = -1 ∨ w = ⟨0, 1⟩ ∨ w = ⟨0, -1⟩ := by
 have hw_cases : w.re ^ 2 + w.im ^ 2 = 1 := by
 simp_all +decide [ sq ];
 grind;
 rcases w with ⟨ w_re, w_im ⟩ ; simp_all +decide;
 have : w_re ≤ 1 := Int.le_of_lt_add_one ( by nlinarith only [ hw_cases ] ) ; ( have : w_re ≥ -1 := Int.le_of_lt_add_one ( by nlinarith only [ hw_cases ] ) ; interval_cases w_re <;> ( have : w_im ≤ 1 := Int.le_of_lt_add_one ( by nlinarith only [ hw_cases ] ) ; ( have : w_im ≥ -1 := Int.le_of_lt_add_one ( by nlinarith only [ hw_cases ] ) ; interval_cases w_im <;> simp +decide at hw_cases ⊢; ) ) );
 grind +locals;
 · rintro ⟨ k, hk ⟩;
 -- By definition of UnitEquiv, we know that v is a unit multiple of stabState k.
 obtain ⟨u, hu, hv⟩ := hk;
 refine' ⟨ _, _, _ ⟩ <;> simp_all +decide [ InBW ];
 · fin_cases k <;> simp +decide [ ← mul_add ];
 all_goals norm_num [ oneI, stabState ];
 · exact dvd_mul_of_dvd_right ( by exact ⟨ ⟨ 1, -1 ⟩, by decide ⟩ ) _;
 · exact dvd_mul_of_dvd_right ⟨ 1, by simp +decide ⟩ _;
 · exact dvd_mul_of_dvd_right ⟨ ⟨ 0, -1 ⟩, by decide ⟩ _;
 · fin_cases k <;> simp +decide [ * ];
 all_goals intro H; simp_all +decide [ IsUnit ] ;
 · -- Since $u$ is a unit, we have $|u|^2 = 1$.
 have h_unit_norm : u.norm = 1 := by
 rw [ isUnit_iff_exists_inv ] at hu;
 rcases hu with ⟨ v, hv ⟩ ; replace hv := congr_arg Zsqrtd.norm hv ; simp_all +decide [ Zsqrtd.norm ] ;
 nlinarith [ show v.re * v.re + v.im * v.im > 0 from lt_of_le_of_ne ( by nlinarith ) ( Ne.symm <| by intro h; simp_all +decide [ add_eq_zero_iff_of_nonneg, mul_self_nonneg ] ) ];
 fin_cases k <;> simp_all +decide [ hermNormSq ]

/-
**Main Theorem (Part 2)**: The six stabilizer states are pairwise non-unit-equivalent.
-/
theorem stabs_pairwise_not_unitEquiv (i j : Fin 6) (hij : i ≠ j) :
 ¬ UnitEquiv (stabState i) (stabState j) := by
 contrapose! hij with h;
 obtain ⟨ u, hu, h ⟩ := h;
 fin_cases i <;> fin_cases j <;> simp +decide [ stabState ] at h ⊢;
 all_goals rcases h with ⟨ rfl, h ⟩ ; simp +decide at h;

/-
**Main Theorem (Part 3)**: Any nonzero vector in BW₁ has squared norm at least 2.
-/
theorem bw_norm_ge_two (v : GVec) (hbw : InBW v) (hne : v ≠ (0, 0)) :
 2 ≤ hermNormSq v := by
 -- By definition of $InBW$, we know that $(1 + i) \mid (v.1 + v.2)$.
 obtain ⟨k, hk⟩ : ∃ k : GaussianInt, v.1 + v.2 = (1 + ⟨0, 1⟩) * k := by
 exact hbw;
 by_contra h_contra;
 -- Since $v \neq (0, 0)$, at least one of $v.1$ or $v.2$ must be non-zero. Without loss of generality, assume $v.1 \neq 0$.
 by_cases hv1 : v.1 = 0;
 · -- Since $v.2 = (1 + ⟨0, 1⟩) * k$, we have $v.2.norm = (1 + ⟨0, 1⟩).norm * k.norm = 2 * k.norm$.
 have hv2_norm : v.2.norm = 2 * k.norm := by
 rw [ show v.2 = ( 1 + ⟨ 0, 1 ⟩ ) * k by simpa [ hv1 ] using hk ] ; simp +decide [ Zsqrtd.norm ] ; ring;
 unfold hermNormSq at h_contra; simp_all +decide [ Zsqrtd.norm ] ;
 exact hne ( Prod.ext hv1 ( by rw [ hk ] ; exact mul_eq_zero_of_right _ ( by ext <;> norm_num <;> nlinarith ) ) );
 · by_cases hv2 : v.2 = 0 <;> simp_all +decide [ hermNormSq ];
 · simp_all +decide [ Zsqrtd.norm ];
 exact hv1 ( by ext <;> norm_num <;> nlinarith );
 · exact hv2 ( by { exact Zsqrtd.ext ( by { norm_num [ Zsqrtd.norm ] at *; nlinarith [ sq_nonneg ( v.1.re - v.1.im ), sq_nonneg ( v.1.re + v.1.im ), show v.1.re ^ 2 + v.1.im ^ 2 > 0 from not_le.mp fun h => hv1 <| by { exact Zsqrtd.ext ( by { norm_num; nlinarith } ) ( by { norm_num; nlinarith } ) } ] } ) ( by { norm_num [ Zsqrtd.norm ] at *; nlinarith [ sq_nonneg ( v.1.re - v.1.im ), sq_nonneg ( v.1.re + v.1.im ), show v.1.re ^ 2 + v.1.im ^ 2 > 0 from not_le.mp fun h => hv1 <| by { exact Zsqrtd.ext ( by { norm_num; nlinarith } ) ( by { norm_num; nlinarith } ) } ] } ) } )

/-! ## Clifford Group: Gate Definitions -/

/-- The phase gate S acts on ℤ[i]² by (a, b) ↦ (a, ib). -/
def phaseGate (v : GVec) : GVec := (v.1, gi * v.2)

/-- The (unnormalized) Hadamard gate acts on ℤ[i]² by (a, b) ↦ (a+b, a-b). -/
def hadamardGate (v : GVec) : GVec := (v.1 + v.2, v.1 - v.2)

/-
The phase gate S preserves BW₁.
-/
theorem phaseGate_preserves_BW (v : GVec) (hv : InBW v) : InBW (phaseGate v) := by
 unfold phaseGate InBW at *;
 convert dvd_add hv ( dvd_mul_of_dvd_left ( show oneI ∣ gi - 1 from ?_ ) v.2 ) using 1 ; ring;
 exact ⟨ gi, by decide ⟩

/-
The Hadamard gate maps BW₁ into BW₁ (it maps BW₁ to (1+i)·BW₁ ⊆ BW₁).
-/
theorem hadamardGate_preserves_BW (v : GVec) (_hv : InBW v) : InBW (hadamardGate v) := by
 use v.1 * ⟨ 1, -1 ⟩;
 ext <;> simp +decide [ hadamardGate ] <;> ring

/-! ## Clifford Group Action on Stabilizer States -/

/-- The permutation of the 6 stabilizer state orbits induced by the phase gate S. -/
def cliffordS : Equiv.Perm (Fin 6) where
 toFun k := match k with
 | 0 => (0 : Fin 6) | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 3 | 5 => 2
 invFun k := match k with
 | 0 => (0 : Fin 6) | 1 => 1 | 2 => 5 | 3 => 4 | 4 => 2 | 5 => 3
 left_inv := by decide
 right_inv := by decide

/-- The permutation of the 6 stabilizer state orbits induced by the Hadamard gate H. -/
def cliffordH : Equiv.Perm (Fin 6) where
 toFun k := match k with
 | 0 => (2 : Fin 6) | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 4
 invFun k := match k with
 | 0 => (2 : Fin 6) | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 5 | 5 => 4
 left_inv := by decide
 right_inv := by decide

/-- One step of monoid closure: add all products of pairs already present. -/
def mulStep (S : Finset (Equiv.Perm (Fin 6))) : Finset (Equiv.Perm (Fin 6)) :=
 S ∪ (S ×ˢ S).image (fun p => p.1 * p.2)

/-- The generating set: identity, S, H and their inverses. -/
def cliffordGens : Finset (Equiv.Perm (Fin 6)) :=
 {1, cliffordS, cliffordS⁻¹, cliffordH, cliffordH⁻¹}

/-- The Clifford group as a computable finite set of permutations, obtained by
 iterating monoid closure to its fixed point. -/
@[irreducible] def cliffordSet : Finset (Equiv.Perm (Fin 6)) :=
 mulStep^[8] cliffordGens

/-- `cliffordSet` is a fixed point of one closure step (verified computationally). -/
theorem cliffordSet_fixpoint : mulStep cliffordSet = cliffordSet := by native_decide

/-- `cliffordSet` is closed under inversion (verified computationally). -/
theorem cliffordSet_image_inv : cliffordSet.image (fun g => g⁻¹) = cliffordSet := by
 native_decide

/-- **Main Theorem (Part 2)**: The Clifford group generators S and H produce a
 permutation group of order 24 acting on the 6 stabilizer state orbits.
 This is isomorphic to S₄ and is the single-qubit Clifford group modulo phase. -/
theorem clifford_card : cliffordSet.card = 24 := by native_decide

/-- The Clifford group acts transitively on the 6 stabilizer states. -/
theorem clifford_transitive :
 ∀ i j : Fin 6, ∃ g ∈ cliffordSet, g i = j := by native_decide

/-- The Clifford set is closed under multiplication. -/
theorem clifford_mul_closed :
 ∀ g h, g ∈ cliffordSet → h ∈ cliffordSet → g * h ∈ cliffordSet := by
 intro g h hg hh
 have hmem : g * h ∈ mulStep cliffordSet := by
 unfold mulStep
 apply Finset.mem_union_right
 rw [Finset.mem_image]
 exact ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩
 rwa [cliffordSet_fixpoint] at hmem

/-- The Clifford set is closed under inversion. -/
theorem clifford_inv_closed :
 ∀ g, g ∈ cliffordSet → g⁻¹ ∈ cliffordSet := by
 intro g hg
 rw [← cliffordSet_image_inv, Finset.mem_image]
 exact ⟨g, hg, rfl⟩

/-- The identity is in the Clifford set. -/
theorem clifford_one_mem : (1 : Equiv.Perm (Fin 6)) ∈ cliffordSet := by native_decide

end BarnesWall