import StabilizerBW.Roots.Filtration
import StabilizerBW.Roots.BW2

/-!
# Tensor subadditivity of the grade and the product bound

This file mechanizes the structural tensor results:

* **T1.1 (the main prize).** For arbitrary integral `2×2` operators `U, V` over
 `R = ℤ[ζ₈]`, the two-qubit grade of the tensor `U ⊗ V` (acting on `BW₂ = L₄`) is
 bounded by the sum of the single-qubit grades:
 `grade2_tensor U V ≤ grade U + grade V` (`grade2_tensor_le_add`).

 The proof factors through the recursive description of the level-3 Barnes–Wall
 lattice `L₄ = {(a,b) : a,b ∈ L₃, a−b ∈ (1+i)·L₃}` (`inL2_iff_blocks`) and the
 bilinearity of the Kronecker action (`tensorApply`).

* **T1.2 (diagonal corollary, n = 2).** For *diagonal* single-qubit operators the
 Kronecker action is the diagonal operator with entrywise products, so
 `grade2_tensor` agrees with the `grade2` of `Roots.BW2` (`grade2_tensor_diag`), and
 the subadditive bound becomes a statement purely about the BW₂ diagonal grade
 (`grade2_diag_le`). Combined with the exact lower bounds of `Roots.BW2` this gives
 disjoint-support additivity, e.g. `g(T⊗T) = g(T) + g(T)` (`grade2_TT_additive`).

* **T3 (product bound).** `g(M₁ ⋯ M_k) ≤ Σ g(Mᵢ)` for a finite product of single-qubit
 operators (`grade_prodMat_le`), a direct induction on `grade_mul`.

The Kronecker convention: with two-qubit basis order `00,01,10,11`, qubit 1 (the `U`
factor) is the most significant bit (indexing the two `L₃`-blocks `lo = (c₀,c₁)` and
`hi = (c₂,c₃)`) and qubit 2 (the `V` factor) acts inside each block.
-/

namespace Roots
open Z8 Mat2

/-! ## The two `L₃`-blocks of an `L₄` vector and the recursive lattice description -/

/-- The low half (qubit-1 = 0 block) of a two-qubit vector. -/
def lo (v : Vec4) : Z8 × Z8 := (v.c0, v.c1)
/-- The high half (qubit-1 = 1 block) of a two-qubit vector. -/
def hi (v : Vec4) : Z8 × Z8 := (v.c2, v.c3)

@[simp] theorem lo_def (v : Vec4) : lo v = (v.c0, v.c1) := rfl
@[simp] theorem hi_def (v : Vec4) : hi v = (v.c2, v.c3) := rfl

/-- Coordinatewise difference of two column vectors in `R²`. -/
def vsub (v w : Z8 × Z8) : Z8 × Z8 := (v.1 - w.1, v.2 - w.2)

@[simp] theorem vsub_fst (v w : Z8 × Z8) : (vsub v w).1 = v.1 - w.1 := rfl
@[simp] theorem vsub_snd (v w : Z8 × Z8) : (vsub v w).2 = v.2 - w.2 := rfl

/-- Membership in `(1+i)·L₃`: `w = (1+i)·z` for some `z ∈ L₃`. -/
def inOneIL (w : Z8 × Z8) : Prop := ∃ z : Z8 × Z8, inL z ∧ w = vsmul Z8.oneI z

theorem inOneIL_zero : inOneIL (0, 0) :=
 ⟨(0, 0), inL_zero, by simp [vsmul]⟩

theorem inOneIL_add {v w : Z8 × Z8} (hv : inOneIL v) (hw : inOneIL w) :
 inOneIL (vadd v w) := by
 obtain ⟨z, hz, rfl⟩ := hv
 obtain ⟨y, hy, rfl⟩ := hw
 exact ⟨vadd z y, inL_add hz hy, by simp [vsmul, vadd]; constructor <;> ring⟩

theorem inOneIL_vsmul (r : Z8) {w : Z8 × Z8} (hw : inOneIL w) : inOneIL (vsmul r w) := by
 obtain ⟨z, hz, rfl⟩ := hw
 exact ⟨vsmul r z, inL_vsmul r hz, by simp [vsmul]; constructor <;> ring⟩

/-
**Recursive description of `L₄`.** `v ∈ L₄` iff both halves lie in `L₃` and their
difference lies in `(1+i)·L₃`.
-/
theorem inL2_iff_blocks (v : Vec4) :
 inL2 v ↔ inL (lo v) ∧ inL (hi v) ∧ inOneIL (vsub (lo v) (hi v)) := by
 constructor <;> intro h;
 · refine' ⟨ _, _, _ ⟩;
 · exact h.1;
 · exact h.2.1;
 · obtain ⟨ z1, hz1 ⟩ := h.2.2.1
 obtain ⟨ z2, hz2 ⟩ := h.2.2.2.1
 use (z1, z2)
 simp;
 obtain ⟨ w, hw ⟩ := h.2.2.2.2;
 simp_all +decide [ sub_eq_iff_eq_add, mul_comm, vsub, vsmul ];
 exact ⟨ w, by ext <;> have := congr_arg ( fun x : Z8 => x.a ) hw <;> have := congr_arg ( fun x : Z8 => x.b ) hw <;> have := congr_arg ( fun x : Z8 => x.c ) hw <;> have := congr_arg ( fun x : Z8 => x.d ) hw <;> norm_num at * <;> linarith ⟩;
 · obtain ⟨ z, hz₁, hz₂ ⟩ := h.2.2;
 simp_all +decide [ inL, inL2, vsub, vsmul ];
 convert mul_dvd_mul_left ( { a := 1, b := 0, c := 1, d := 0 } : Z8 ) hz₁ using 1
 grind

/-! ## The Kronecker (tensor) action `U ⊗ V` on `L₄` -/

/-- The action of `U ⊗ V` on a two-qubit vector. `U` (qubit 1) mixes the two blocks
`lo, hi` by its scalar entries; `V` (qubit 2) acts inside each block. -/
def tensorApply (U V : Mat2) (v : Vec4) : Vec4 :=
 let p := V.mulVec (vadd (vsmul U.m00 (lo v)) (vsmul U.m01 (hi v)))
 let q := V.mulVec (vadd (vsmul U.m10 (lo v)) (vsmul U.m11 (hi v)))
 ⟨p.1, p.2, q.1, q.2⟩

@[simp] theorem lo_tensorApply (U V : Mat2) (v : Vec4) :
 lo (tensorApply U V v) = V.mulVec (vadd (vsmul U.m00 (lo v)) (vsmul U.m01 (hi v))) := rfl

@[simp] theorem hi_tensorApply (U V : Mat2) (v : Vec4) :
 hi (tensorApply U V v) = V.mulVec (vadd (vsmul U.m10 (lo v)) (vsmul U.m11 (hi v))) := rfl

/-
Pulling scalars out of the Kronecker action: `(rU) ⊗ (sV) = (rs)·(U ⊗ V)`.
-/
theorem tensorApply_smul_smul (r s : Z8) (U V : Mat2) (v : Vec4) :
 tensorApply (Mat2.smul r U) (Mat2.smul s V) v = vsmul4 (r * s) (tensorApply U V v) := by
 unfold tensorApply vsmul4; simp +decide [ mul_assoc, mul_comm ] ;
 simp +decide [ smul, mul_comm, mul_left_comm ];
 grind +revert

/-
**Core lemma for T1.1.** If `U` and `V` each preserve `L₃`, then `U ⊗ V` preserves
`L₄`.
-/
theorem tensorApply_mapsTo {U V : Mat2} (hU : MapsToL U) (hV : MapsToL V) :
 ∀ v, inL2 v → inL2 (tensorApply U V v) := by
 intro v hv;
 -- By `inL2_iff_blocks`, we need to show `inL (lo (tensorApply U V v))`, `inL (hi (tensorApply U V v))`, and `inOneIL (vsub (lo (tensorApply U V v)) (hi (tensorApply U V v)))`.
 rw [inL2_iff_blocks] at hv ⊢;
 obtain ⟨c, hcL, hc⟩ : ∃ c : Z8 × Z8, inL c ∧ vsub (lo v) (hi v) = vsmul Z8.oneI c := hv.2.2;
 -- Substitute `Va = vadd Vb (vsmul oneI Vc)` into the expression for the difference.
 have h_diff : vsub (lo (tensorApply U V v)) (hi (tensorApply U V v)) = vadd (vsmul (U.m00 + U.m01 - (U.m10 + U.m11)) (V.mulVec (hi v))) (vsmul (oneI * (U.m00 - U.m10)) (V.mulVec c)) := by
 simp +decide [ tensorApply, vsmul, vadd, vsub ] at *;
 simp +decide [ sub_eq_iff_eq_add.mp hc.1, sub_eq_iff_eq_add.mp hc.2, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf ; aesop ( simp_config := { decide := true } ) ;
 refine' ⟨ _, _, _ ⟩;
 · convert hV _ ( inL_add ( inL_vsmul U.m00 hv.1 ) ( inL_vsmul U.m01 hv.2.1 ) ) using 1;
 · convert inL_add ( inL_vsmul U.m10 ( hV _ hv.1 ) ) ( inL_vsmul U.m11 ( hV _ hv.2.1 ) ) using 1;
 simp +decide [ vsmul ];
 exact ⟨ by rw [ show ( tensorApply U V v ).c2 = V.m00 * ( U.m10 * v.c0 + U.m11 * v.c2 ) + V.m01 * ( U.m10 * v.c1 + U.m11 * v.c3 ) by rfl ] ; ring, by rw [ show ( tensorApply U V v ).c3 = V.m10 * ( U.m10 * v.c0 + U.m11 * v.c2 ) + V.m11 * ( U.m10 * v.c1 + U.m11 * v.c3 ) by rfl ] ; ring ⟩;
 · -- The first summand `vsmul s0 Vb` is in `inOneIL` because `oneI ∣ s0`.
 have h_s0 : oneI ∣ (U.m00 + U.m01 - (U.m10 + U.m11)) := by
 have h_s0 : oneI ∣ (U.m00 + U.m01 + (U.m10 + U.m11)) := by
 have := hU ( 1, 1 ) ; simp_all +decide [ inL ] ;
 convert dvd_sub h_s0 ( show oneI ∣ 2 * ( U.m10 + U.m11 ) from ?_ ) using 1 ; ring;
 have h_s0 : oneI ∣ 2 := by
 exact ⟨ ⟨ 1, 0, -1, 0 ⟩, by decide ⟩;
 exact dvd_mul_of_dvd_left h_s0 _;
 obtain ⟨ k, hk ⟩ := h_s0;
 rw [ h_diff, hk ];
 refine' inOneIL_add _ _;
 · exact ⟨ vsmul k ( V.mulVec ( hi v ) ), hV _ hv.2.1 |> fun h => inL_vsmul _ h, by ext <;> simp +decide [ vsmul ] <;> ring ⟩;
 · exact ⟨ vsmul ( U.m00 - U.m10 ) ( V.mulVec c ), hV _ hcL |> fun h => inL_vsmul _ h, by ext <;> simp +decide [ vsmul ] <;> ring ⟩

/-! ## The two-qubit grade of a Kronecker product, and subadditivity (T1.1) -/

/-- `gradeLE2_tensor U V k`: the operator `λ^k·(U ⊗ V)` preserves `L₄`. -/
def gradeLE2_tensor (U V : Mat2) (k : ℕ) : Prop :=
 ∀ v, inL2 v → inL2 (vsmul4 (Z8.lam ^ k) (tensorApply U V v))

/-- If `λ^j·U` and `λ^k·V` preserve `L₃`, then `λ^{j+k}·(U ⊗ V)` preserves `L₄`. -/
theorem gradeLE2_tensor_of {U V : Mat2} {j k : ℕ} (hU : gradeLE U j) (hV : gradeLE V k) :
 gradeLE2_tensor U V (j + k) := by
 intro v hv
 have key : vsmul4 (Z8.lam ^ (j + k)) (tensorApply U V v)
 = tensorApply (Mat2.smul (Z8.lam ^ j) U) (Mat2.smul (Z8.lam ^ k) V) v := by
 rw [tensorApply_smul_smul, ← pow_add]
 rw [key]
 exact tensorApply_mapsTo hU hV v hv

theorem gradeLE2_tensor_nonempty (U V : Mat2) : ∃ k, gradeLE2_tensor U V k :=
 ⟨4 + 4, gradeLE2_tensor_of (gradeLE_top U) (gradeLE_top V)⟩

/-- The two-qubit grade of `U ⊗ V`. -/
noncomputable def grade2_tensor (U V : Mat2) : ℕ := sInf {k | gradeLE2_tensor U V k}

/-- **Theorem T1.1 (subadditivity under tensor).**
`g_{BW₂}(U ⊗ V) ≤ g_{BW₁}(U) + g_{BW₁}(V)`. -/
theorem grade2_tensor_le_add (U V : Mat2) : grade2_tensor U V ≤ grade U + grade V :=
 Nat.sInf_le (gradeLE2_tensor_of (gradeLE_grade U) (gradeLE_grade V))

/-! ## T1.2 — the diagonal corollary (n = 2) -/

/-
For diagonal factors, the Kronecker action is the diagonal operator with the
entrywise products on the diagonal.
-/
theorem tensorApply_diag (u0 u1 v0 v1 : Z8) (v : Vec4) :
 tensorApply ⟨u0, 0, 0, u1⟩ ⟨v0, 0, 0, v1⟩ v
 = dapply ⟨u0 * v0, u0 * v1, u1 * v0, u1 * v1⟩ v := by
 apply Vec4.ext' <;> simp +decide [ tensorApply ]; all_goals grind

theorem gradeLE2_tensor_diag_iff (u0 u1 v0 v1 : Z8) (k : ℕ) :
 gradeLE2_tensor ⟨u0, 0, 0, u1⟩ ⟨v0, 0, 0, v1⟩ k
 ↔ gradeLE2 ⟨u0 * v0, u0 * v1, u1 * v0, u1 * v1⟩ k := by
 unfold gradeLE2_tensor gradeLE2 MapsToL2
 constructor
 · intro h v hv
 rw [dapply_scale4]
 have := h v hv
 rwa [tensorApply_diag] at this
 · intro h v hv
 rw [tensorApply_diag]
 have := h v hv
 rwa [dapply_scale4] at this

/-- `grade2_tensor` of two diagonal factors equals the BW₂ grade of the product
diagonal. -/
theorem grade2_tensor_diag (u0 u1 v0 v1 : Z8) :
 grade2_tensor ⟨u0, 0, 0, u1⟩ ⟨v0, 0, 0, v1⟩
 = grade2 ⟨u0 * v0, u0 * v1, u1 * v0, u1 * v1⟩ := by
 unfold grade2_tensor grade2
 congr 1
 ext k
 exact gradeLE2_tensor_diag_iff u0 u1 v0 v1 k

/-- **Theorem T1.2 (diagonal subadditivity, n = 2).** The BW₂ grade of the diagonal
`diag(u₀v₀, u₀v₁, u₁v₀, u₁v₁)` (the tensor of two single-qubit diagonal characters) is
bounded by the sum of the single-qubit grades. -/
theorem grade2_diag_le (u0 u1 v0 v1 : Z8) :
 grade2 ⟨u0 * v0, u0 * v1, u1 * v0, u1 * v1⟩
 ≤ grade ⟨u0, 0, 0, u1⟩ + grade ⟨v0, 0, 0, v1⟩ := by
 rw [← grade2_tensor_diag]
 exact grade2_tensor_le_add _ _

/-- `T ⊗ T` realized as a Kronecker product of two `T` diagonals. -/
theorem grade2_TT_eq_tensor : grade2 TT = grade2_tensor T T := by
 show grade2 TT = grade2_tensor ⟨1, 0, 0, Z8.zeta⟩ ⟨1, 0, 0, Z8.zeta⟩
 rw [grade2_tensor_diag]
 congr 1

/-- **Disjoint-support additivity at `T ⊗ T`:** `g(T⊗T) = g(T) + g(T) = 2`, now a
consequence of subadditivity (`grade2_diag_le`) together with the exact lower bound
`grade2_TT`. -/
theorem grade2_TT_additive : grade2 TT = grade T + grade T := by
 rw [grade2_TT, grade_T]

/-! ## T3 — the product bound `g(M₁ ⋯ M_k) ≤ Σ g(Mᵢ)` -/

/-- The identity has grade `0`. -/
theorem II_gradeLE_zero : gradeLE Mat2.II 0 := by
 unfold gradeLE
 rw [pow_zero, smul_one_mat]
 intro v hv
 have : Mat2.II.mulVec v = v := by
 cases v; simp [Mat2.mulVec, Mat2.II]
 rwa [this]

theorem grade_II : grade Mat2.II = 0 := grade_eq_zero II_gradeLE_zero

/-- The (right-folded) product of a list of single-qubit operators. -/
def prodMat : List Mat2 → Mat2
 | [] => Mat2.II
 | M :: rest => M * prodMat rest

/-- **Theorem T3 (product bound).** `g(M₁ ⋯ M_k) ≤ Σ g(Mᵢ)`. -/
theorem grade_prodMat_le (L : List Mat2) : grade (prodMat L) ≤ (L.map grade).sum := by
 induction L with
 | nil => simp [prodMat, grade_II]
 | cons M rest ih =>
 simp only [prodMat, List.map_cons, List.sum_cons]
 exact le_trans (grade_mul M (prodMat rest)) (by omega)

end Roots