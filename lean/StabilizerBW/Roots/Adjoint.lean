import StabilizerBW.Roots.Filtration

/-!
# Adjoint invariance of the grade (Priority 2(c) and 2(d), integral single-qubit case)

This file completes two of the previously-partial parts of Priority 2 for the
integral single-qubit fragment (operators acting on `L₃ ⊆ R²`):

* **(c)** `grade M = 0 ⟺ M ∈ Aut(L₃)`: concretely `grade M = 0 ↔ MapsToL M`
  (`grade_eq_zero_iff`).
* **(d)** `g(M†) = g(M)`: the grade is invariant under the Hermitian adjoint
  (`grade_adj`), *for every integral operator* — not merely isometries.

The engine is the **self-duality of `L₃` under the Hermitian form `h`**:
`inL w ↔ ∀ v ∈ L₃, (1+i) ∣ h(v, w)` (`inL_iff_herm`).  Combined with the adjunction
`h(M·v, w) = h(v, M†·w)` (`herm_adj`) this gives `MapsToL M ↔ MapsToL M†`
(`MapsToL_adj_iff`), and the scalar `λ` is handled by `conj λ = ζ³·λ` (`conj_lam`),
so `λ^k` and `conj(λ^k)` differ only by the unit `ζ^{3k}`.
-/

namespace Roots
open Z8 Mat2

/-! ## Conjugation is an involution of `L₃` -/

/-- Coordinatewise complex conjugation on column vectors. -/
def vconj (v : Z8 × Z8) : Z8 × Z8 := (Z8.conj v.1, Z8.conj v.2)

/-- `1+i` divides `z` iff it divides `conj z` (since `conj(1+i) = 1-i ∼ 1+i`). -/
theorem oneI_dvd_conj (z : Z8) : Z8.oneI ∣ z ↔ Z8.oneI ∣ Z8.conj z := by
  rw [← dvdOneI_iff, ← dvdOneI_iff]
  unfold Z8.dvdOneI
  simp only [Z8.conj_a, Z8.conj_b, Z8.conj_c, Z8.conj_d]
  omega

/-- Conjugation preserves membership in `L₃`. -/
theorem inL_conj (v : Z8 × Z8) : inL (vconj v) ↔ inL v := by
  unfold inL vconj
  simp only
  rw [← Z8.conj_add]
  exact (oneI_dvd_conj _).symm

/-! ## Self-duality of `L₃` under the Hermitian form -/

/-
**Self-duality of `L₃`.** A vector lies in `L₃` iff its Hermitian pairing with
every lattice vector is `(1+i)`-divisible.  (`L₃` is its own dual w.r.t. `h` and the
ideal `(1+i)`.)
-/
theorem inL_iff_herm (w : Z8 × Z8) : inL w ↔ ∀ v, inL v → Z8.oneI ∣ herm v w := by
  constructor;
  · intro hw v hv;
    rw [ ← dvdOneI_iff ] at *;
    obtain ⟨ k₁, hk₁ ⟩ := hw; obtain ⟨ k₂, hk₂ ⟩ := hv; simp_all +decide [ Z8.oneI, Z8.dvdOneI ] ;
    unfold herm; simp_all +decide [ Z8.mul_a, Z8.mul_b, Z8.mul_c, Z8.mul_d, Z8.add_a, Z8.add_b, Z8.add_c, Z8.add_d ] ;
    erw [ show v.2 = { a := 1, b := 0, c := 1, d := 0 } * k₂ - v.1 from eq_sub_of_add_eq' hk₂ ] ; simp +decide [ Z8.mul_a, Z8.mul_b, Z8.mul_c, Z8.mul_d ] ; ring_nf ;
    erw [ show w.2 = { a := 1, b := 0, c := 1, d := 0 } * k₁ - w.1 from eq_sub_of_add_eq' hk₁ ] ; simp +decide [ Z8.mul_a, Z8.mul_b, Z8.mul_c, Z8.mul_d ] ; ring_nf ;
    exact ⟨ by exact ⟨ v.1.a * w.1.a - v.1.a * w.1.c + v.1.a * k₁.c + w.1.a * v.1.c + ( w.1.c * v.1.c - k₁.a * v.1.c ) + ( v.1.b * w.1.b - v.1.b * w.1.d ) + v.1.b * k₁.d + w.1.b * v.1.d + ( w.1.d * v.1.d - k₁.b * v.1.d ), by ring ⟩, by exact ⟨ - ( v.1.a * w.1.b ) - v.1.a * w.1.d + v.1.a * k₁.b + w.1.a * v.1.b + ( w.1.a * v.1.d - w.1.c * v.1.b ) + ( w.1.c * v.1.d - k₁.a * v.1.d ) + k₁.c * v.1.b + ( v.1.c * w.1.b - v.1.c * w.1.d ) + v.1.c * k₁.d + w.1.d * k₂.a + ( - ( k₁.b * k₂.a ) - k₁.d * k₂.a ), by ring ⟩ ⟩;
  · intro hw
    have := hw (1, -1) (by
    exact Roots.inL_g1)
    simp +decide [ herm ] at this;
    obtain ⟨ k, hk ⟩ := this;
    -- Since $oneI \mid (w.1 - w.2)$, we have $oneI \mid (w.1 + w.2)$ because $oneI \mid 2$.
    have h_div : oneI ∣ (w.1 - w.2) := by
      convert oneI_dvd_conj _ |>.2 _ using 1;
      convert hk.symm ▸ dvd_mul_right _ _ using 1;
      ext <;> simp +decide [ Z8.conj ]; all_goals ring;
    have h_div : oneI ∣ (w.1 + w.2) := by
      have h_two : oneI ∣ (2 : Z8) := by
        exact ⟨ ⟨ 1, 0, -1, 0 ⟩, by decide ⟩
      convert dvd_add h_div ( h_two.mul_right w.2 ) using 1 ; ring;
    exact h_div

/-! ## The adjoint preserves `MapsToL` -/

/-- If `M` preserves `L₃`, so does its Hermitian adjoint `M†`. -/
theorem MapsToL_adj {M : Mat2} (h : MapsToL M) : MapsToL M.adj := by
  intro w hw
  rw [inL_iff_herm]
  intro v hv
  rw [← herm_adj]
  exact (inL_iff_herm w).1 hw _ (h v hv)

/-- `MapsToL` is invariant under the adjoint. -/
theorem MapsToL_adj_iff (M : Mat2) : MapsToL M ↔ MapsToL M.adj :=
  ⟨MapsToL_adj, fun h => by have := MapsToL_adj h; rwa [Mat2.adj_adj] at this⟩

/-! ## Scalar bookkeeping: `conj λ = ζ³·λ` and unit-scaling invariance -/

/-- `conj (smul r M) = smul (conj r) (adj M)`. -/
theorem adj_smul (r : Z8) (M : Mat2) :
    (Mat2.smul r M).adj = Mat2.smul (Z8.conj r) M.adj := by
  apply Mat2.ext' <;> simp [Mat2.smul, Mat2.adj, Z8.conj_mul]

/-- `smul` is associative in the scalar. -/
theorem smul_smul_mat (a b : Z8) (M : Mat2) :
    Mat2.smul a (Mat2.smul b M) = Mat2.smul (a * b) M := by
  apply Mat2.ext' <;> simp [Mat2.smul] <;> ring

/-- `conj λ = ζ³·λ`: the conjugate of the ramified prime is its associate. -/
theorem conj_lam : Z8.conj Z8.lam = Z8.zeta ^ 3 * Z8.lam := by decide

theorem zeta_pow_eight : Z8.zeta ^ 8 = 1 := by decide

/-- Scaling by a unit does not change whether an operator preserves `L₃`. -/
theorem MapsToL_smul_unit {r s : Z8} (hrs : s * r = 1) {N : Mat2} :
    MapsToL (Mat2.smul r N) ↔ MapsToL N := by
  constructor
  · intro h
    have h2 := mapsToL_smul s h
    rwa [smul_smul_mat, hrs, smul_one_mat] at h2
  · intro h; exact mapsToL_smul r h

/-! ## Priority 2(d): `g(M†) = g(M)` -/

/-- `gradeLE M† k ↔ gradeLE M k` for every `k`. -/
theorem gradeLE_adj (M : Mat2) (k : ℕ) : gradeLE M.adj k ↔ gradeLE M k := by
  have hconjpow : Z8.conj (Z8.lam ^ k) = (Z8.zeta ^ 3) ^ k * Z8.lam ^ k := by
    have h : Z8.conj (Z8.lam ^ k) = (Z8.zeta ^ 3 * Z8.lam) ^ k := by
      induction k with
      | zero => simp
      | succ n ih => rw [pow_succ, pow_succ, Z8.conj_mul, ih, conj_lam]
    rw [h, mul_pow]
  have hunit : (Z8.zeta ^ 5) ^ k * (Z8.zeta ^ 3) ^ k = 1 := by
    rw [← mul_pow, show Z8.zeta ^ 5 * Z8.zeta ^ 3 = Z8.zeta ^ 8 by ring,
      zeta_pow_eight, one_pow]
  unfold gradeLE
  rw [MapsToL_adj_iff (Mat2.smul (Z8.lam ^ k) M), adj_smul, hconjpow,
    ← smul_smul_mat, MapsToL_smul_unit hunit]

/-- **Priority 2(d): `g(M†) = g(M)`** (integral single-qubit operators). -/
theorem grade_adj (M : Mat2) : grade M.adj = grade M := by
  have : {k | gradeLE M.adj k} = {k | gradeLE M k} := by
    ext k; exact gradeLE_adj M k
  unfold grade
  rw [this]

/-! ## Priority 2(c): `g(M) = 0 ⟺ M ∈ Aut(L₃)` -/

/-- **Priority 2(c): `grade M = 0 ⟺ M` preserves `L₃`** (i.e. is a lattice
endomorphism; lies in the monoid `Endᵣ(L₃)` = `{M : M·L₃ ⊆ L₃}`). Note:
this is the endomorphism monoid, NOT the automorphism group — `M = 0` has
`grade = 0` but is not invertible. The automorphism group `Aut(L₃)` is the
subset of `Endᵣ(L₃)` consisting of invertible elements; the unitary
automorphism subgroup `Autᵁ(L₃) ⊆ Aut(L₃)` is the one identified with
the phased Clifford group at `n = 2` (see `aut_L3_unitary_is_phased_clifford`).
-/
theorem grade_eq_zero_iff (M : Mat2) : grade M = 0 ↔ MapsToL M := by
  constructor
  · intro h
    have hmem : gradeLE M (grade M) := gradeLE_grade M
    rw [h] at hmem
    unfold gradeLE at hmem
    simpa using hmem
  · intro h
    apply grade_eq_zero
    unfold gradeLE
    simpa using h

end Roots