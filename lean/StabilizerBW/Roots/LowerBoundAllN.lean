import StabilizerBW.Roots.UpperBoundAllN
import StabilizerBW.Roots.Lattice

/-!
# The all-`n` lower bound for the `ν = 0` maximal monomial (Target T2)

This file proves the matching lower bound for the maximal-degree `ν = 0` single
monomial `bwT n = D_{x_{1⋯n}}` at **every** `n`:

 `graden n (bwT n) = 2n − 1` (for `n ≥ 1`).

Combined with the upper bound `BWn.bwT_graden_le` / `UpperBoundAllN.graden_bwT_le`
(`≤ 2n − 1`) the only content is the lower bound `≥ 2n − 1`, i.e. that `λ^{2n−2}·bwT`
does *not* preserve `BW_n`.

The lower bound is detected by the **all-ones witness** `bwId n` (`bwMul (bwT n) (bwId n)
= bwT n`), so it reduces to `¬ inBW n (λ^{2n−2}·bwT n)`. The heart of the matter is the
**converse conductor at the corner**:

 `corner_inBW_iff : inBW n (λ^j · corner_n) ↔ 2n ≤ j`

(the corner delta vector requires `λ`-valuation exactly `2n`). The `←` direction is the
conductor lemma (`BWn.conductor` via `λ² = (1+i)·u`); the `→` direction is the new
content, proved by induction peeling the outer qubit and cancelling the `(1+i)`-factor
through the integral-domain cancellation `oneI_mul_cancel`.
-/

namespace Roots
open Z8

/-! ## Cancellation helpers in `R = ℤ[ζ₈]` -/

/-- `2·z = 0 → z = 0` in `R` (torsion-free). -/
theorem two_mul_eq_zero_Z8 {z : Z8} (h : (2 : Z8) * z = 0) : z = 0 := by
 have h2 : (2 : Z8) = ⟨2, 0, 0, 0⟩ := by decide
 rw [h2] at h
 have ha := congrArg Z8.a h
 have hb := congrArg Z8.b h
 have hc := congrArg Z8.c h
 have hd := congrArg Z8.d h
 simp only [Z8.mul_a, Z8.mul_b, Z8.mul_c, Z8.mul_d, Z8.zero_a, Z8.zero_b, Z8.zero_c,
 Z8.zero_d, zero_mul, add_zero, sub_zero] at ha hb hc hd
 apply Z8.ext' <;> simp only [Z8.zero_a, Z8.zero_b, Z8.zero_c, Z8.zero_d] <;> omega

/-- `oneI = 1 + i` is cancellable: `oneI·x = oneI·y → x = y`. -/
theorem oneI_mul_cancel {x y : Z8} (h : oneI * x = oneI * y) : x = y := by
 have hsub : oneI * (x - y) = 0 := by rw [mul_sub, h, sub_self]
 have h2 : (2 : Z8) * (x - y) = 0 := by
 have : Z8.conj oneI * oneI = 2 := by decide
 calc (2 : Z8) * (x - y) = (Z8.conj oneI * oneI) * (x - y) := by rw [this]
 _ = Z8.conj oneI * (oneI * (x - y)) := by rw [mul_assoc]
 _ = 0 := by rw [hsub, mul_zero]
 have := two_mul_eq_zero_Z8 h2
 exact sub_eq_zero.mp this

/-- Cancellation of `oneI` on `BW_n` vectors. -/
theorem bwSmul_oneI_inj (n : ℕ) {w w' : BWVec n}
 (h : bwSmul n oneI w = bwSmul n oneI w') : w = w' := by
 induction n with
 | zero => exact oneI_mul_cancel h
 | succ m ih =>
 obtain ⟨a, b⟩ := w; obtain ⟨a', b'⟩ := w'
 simp only [bwSmul_succ] at h
 exact Prod.ext (ih (congrArg Prod.fst h)) (ih (congrArg Prod.snd h))

/-! ## The corner delta vector and its `λ`-valuation -/

/-- The all-ones vector lies in `BW_n`. -/
theorem bwId_inBW (n : ℕ) : inBW n (bwId n) := by
 induction n with
 | zero => trivial
 | succ m ih => exact ⟨ih, ih, bwZero m, bwZero_inBW m, by rw [bwId_succ, bwSub_self, bwSmul_bwZero]⟩

/-- `bwMul D (all-ones) = D`. -/
theorem bwMul_bwId_right (n : ℕ) (D : BWVec n) : bwMul n D (bwId n) = D := by
 induction n with
 | zero => exact mul_one (show Z8 from D)
 | succ m ih => obtain ⟨A, B⟩ := D; simp only [bwId_succ, bwMul_succ, ih]

/-! ## The corner-coordinate functional -/

/-- The corner (all-ones) coordinate of a `BW_n` vector. -/
def cornerCoord : (n : ℕ) → BWVec n → Z8
 | 0 => fun z => (show Z8 from z)
 | _ + 1 => fun v => cornerCoord _ v.2

@[simp] theorem cornerCoord_succ (n : ℕ) (v : BWVec (n + 1)) :
 cornerCoord (n + 1) v = cornerCoord n v.2 := rfl

theorem cornerCoord_bwSmul (n : ℕ) (r : Z8) (v : BWVec n) :
 cornerCoord n (bwSmul n r v) = r * cornerCoord n v := by
 induction n with
 | zero => rfl
 | succ m ih => exact ih v.2

theorem cornerCoord_bwSub (n : ℕ) (a b : BWVec n) :
 cornerCoord n (bwSub n a b) = cornerCoord n a - cornerCoord n b := by
 induction n with
 | zero => rfl
 | succ m ih => exact ih a.2 b.2

theorem cornerCoord_bwZero (n : ℕ) : cornerCoord n (bwZero n) = 0 := by
 induction n with
 | zero => rfl
 | succ m ih => exact ih

theorem cornerCoord_bwCorner (n : ℕ) : cornerCoord n (bwCorner n) = 1 := by
 induction n with
 | zero => rfl
 | succ m ih => exact ih

/-- `oneI ∣ λ^j` forces `j ≥ 2` (since `λ`, `1` are not `(1+i)`-divisible). -/
theorem two_le_of_oneI_dvd_lam_pow {j : ℕ} (h : oneI ∣ Z8.lam ^ j) : 2 ≤ j := by
 by_contra hlt
 push_neg at hlt
 interval_cases j
 · rw [pow_zero, ← dvdOneI_iff] at h; exact absurd h (by decide)
 · rw [pow_one, ← dvdOneI_iff] at h; exact absurd h (by decide)

/-
**Converse conductor at the corner.** The corner delta vector scaled by `λ^j`
lies in `BW_n` iff `j ≥ 2n`. The `←` direction is the conductor; the `→` direction
is the new lower-bound content.
-/
theorem corner_inBW_iff (n j : ℕ) :
 inBW n (bwSmul n (Z8.lam ^ j) (bwCorner n)) ↔ 2 * n ≤ j := by
 induction' n with n ih generalizing j;
 · grind +suggestions;
 · constructor <;> intro h;
 · obtain ⟨w, hw⟩ : ∃ w : BWVec n, inBW n w ∧ bwSub n (bwZero n) (bwSmul n (lam ^ j) (bwCorner n)) = bwSmul n oneI w := by
 convert h.2.2 using 4 ; simp +decide [ bwSmul_succ, bwCorner_succ ];
 rw [ bwSmul_bwZero ];
 -- From `hw`, `oneI ∣ lam^j`, hence `j ≥ 2` by `two_le_of_oneI_dvd_lam_pow`.
 have h_j_ge_2 : 2 ≤ j := by
 apply two_le_of_oneI_dvd_lam_pow;
 have h_div : oneI * cornerCoord n w = -(lam ^ j) := by
 convert congr_arg ( cornerCoord n ) hw.2 using 1;
 · rw [ hw.2, cornerCoord_bwSmul ];
 · rw [ ← hw.2, cornerCoord_bwSub ] ; norm_num [ cornerCoord_bwSmul, cornerCoord_bwZero, cornerCoord_bwCorner ];
 exact ⟨ -cornerCoord n w, by linear_combination' h_div ⟩;
 -- Since `j ≥ 2`, we have `bwSmul n (-(lam^j)) (bwCorner n) = bwSmul n oneI (bwSmul n (-(uu) * lam^(j-2)) (bwCorner n))`.
 have h_eq : bwSmul n (-(lam ^ j)) (bwCorner n) = bwSmul n oneI (bwSmul n (-(uu) * lam ^ (j - 2)) (bwCorner n)) := by
 have h_eq : -(lam ^ j) = oneI * (-(uu) * lam ^ (j - 2)) := by
 rw [ show lam ^ j = lam ^ 2 * lam ^ ( j - 2 ) by rw [ ← pow_add, Nat.add_sub_of_le h_j_ge_2 ] ] ; simp +decide [ Z8.lam_sq, mul_assoc, mul_left_comm ];
 simp +decide [ ← mul_assoc, ← sq ];
 congr;
 rw [ h_eq, ← bwSmul_bwSmul ];
 -- By `bwSmul_oneI_inj`, `w = bwSmul n (-(uu) * lam^(j-2)) (bwCorner n)`.
 have h_w_eq : w = bwSmul n (-(uu) * lam ^ (j - 2)) (bwCorner n) := by
 apply bwSmul_oneI_inj;
 rw [ ← hw.2, ← h_eq, bwSub_bwZero_left ];
 convert bwSmul_bwSmul n ( -1 ) ( lam ^ j ) ( bwCorner n ) using 1 ; ring;
 -- Then `bwSmul n (lam^(j-2)) (bwCorner n) = bwSmul n (-(uuInv)) w` because scaling `w` by `-(uuInv)` gives scalar `(-(uuInv)) * (-(uu) * lam^(j-2)) = (uuInv*uu) * lam^(j-2) = lam^(j-2)` (using `uu_mul_uuInv`).
 have h_eq' : bwSmul n (lam ^ (j - 2)) (bwCorner n) = bwSmul n (-(uuInv)) w := by
 rw [h_w_eq];
 rw [ bwSmul_bwSmul ];
 rw [ ← mul_assoc, show -uuInv * -uu = 1 from by
 decide ] ; norm_num;
 grind +suggestions;
 · rw [ inBW_succ_iff ];
 simp_all +decide [ bwSmul_succ, bwCorner_succ ];
 refine' ⟨ _, _, _ ⟩;
 · rw [ bwSmul_bwZero ] ; exact bwZero_inBW _;
 · linarith;
 · refine' ⟨ bwSmul n ( -1 * Z8.uu * Z8.lam ^ ( j - 2 ) ) ( bwCorner n ), _, _ ⟩;
 · convert bwSmul_inBW n ( -1 * uu ) ( ih ( j - 2 ) |>.2 ( by omega ) ) using 1;
 convert bwSmul_bwSmul n ( -1 * uu ) ( Z8.lam ^ ( j - 2 ) ) ( bwCorner n ) using 1;
 · grind +suggestions;
 · convert bwSmul_bwSmul n ( -1 * uu ) ( Z8.lam ^ ( j - 2 ) ) ( bwCorner n ) using 1;
 · rw [ show ( { a := 1, b := -1, c := 0, d := 0 } : Z8 ) ^ j = ( { a := 1, b := -1, c := 0, d := 0 } : Z8 ) ^ 2 * ( { a := 1, b := -1, c := 0, d := 0 } : Z8 ) ^ ( j - 2 ) by rw [ ← pow_add, Nat.add_sub_of_le ( by linarith ) ] ] ; simp +decide [ *, mul_assoc, mul_left_comm ] ;
 rw [ show ( { a := 1, b := -1, c := 0, d := 0 } : Z8 ) ^ 2 = { a := 1, b := 0, c := 1, d := 0 } * { a := 1, b := -1, c := 0, d := 1 } by rfl ] ; simp +decide [ *, mul_assoc, mul_left_comm ] ;
 simp +decide [ bwSmul_bwZero, bwSub_bwZero_left, bwSmul_bwSmul ]

/-
The corner delta vector scaled by `λ^j` lies in `(1+i)·BW_n` iff `j ≥ 2n + 2`.
-/
theorem corner_inOneIL_iff (n j : ℕ) :
 (∃ w, inBW n w ∧ bwSub n (bwZero n) (bwSmul n (Z8.lam ^ j) (bwCorner n))
 = bwSmul n oneI w) ↔ 2 * n + 2 ≤ j := by
 by_cases hj : j ≥ 2 <;> simp_all +decide [ pow_succ', mul_assoc, mul_left_comm ];
 · constructor <;> intro h;
 · obtain ⟨ w, hw₁, hw₂ ⟩ := h
 have h_div : oneI ∣ Z8.lam ^ j := by
 apply_fun cornerCoord n at hw₂ ; simp_all +decide [ pow_succ', mul_assoc, mul_left_comm ];
 simp_all +decide [ cornerCoord_bwSub, cornerCoord_bwSmul, cornerCoord_bwZero, cornerCoord_bwCorner ];
 exact ⟨ -cornerCoord n w, by linear_combination' -hw₂ ⟩;
 have h_j_ge_2n2 : inBW n (bwSmul n (Z8.lam ^ (j - 2)) (bwCorner n)) := by
 have h_j_ge_2n2 : w = bwSmul n (-(Z8.uu) * Z8.lam ^ (j - 2)) (bwCorner n) := by
 apply bwSmul_oneI_inj n;
 convert hw₂.symm using 1;
 rw [ ← Nat.sub_add_cancel hj, pow_add ] ; norm_num [ pow_succ', mul_assoc, mul_left_comm ] ;
 rw [ bwSub_bwZero_left ] ; norm_num [ bwSmul_bwSmul ] ; ring;
 congr! 2;
 convert bwSmul_inBW n ( -Z8.uuInv ) hw₁ using 1;
 rw [ h_j_ge_2n2 ];
 have h_scalar : -Z8.uuInv * (-Z8.uu * Z8.lam ^ (j - 2)) = Z8.lam ^ (j - 2) := by
 have h_scalar : -Z8.uuInv * (-Z8.uu) = 1 := by
 decide;
 rw [ ← mul_assoc, h_scalar, one_mul ];
 rw [ ← h_scalar, bwSmul_bwSmul ];
 grind;
 have := corner_inBW_iff n ( j - 2 ) |>.1 h_j_ge_2n2; omega;
 · refine' ⟨ bwSmul n ( -Z8.uu * Z8.lam ^ ( j - 2 ) ) ( bwCorner n ), _, _ ⟩;
 · convert bwSmul_inBW n _ ( corner_inBW_iff n ( j - 2 ) |>.2 ( by omega ) ) using 1;
 rw [ ← bwSmul_bwSmul ];
 · convert bwSub_bwZero_left n ( bwSmul n ( Z8.lam ^ j ) ( bwCorner n ) ) using 1;
 rw [ ← Nat.sub_add_cancel hj ] ; simp +decide [ pow_add, mul_assoc, mul_left_comm, bwSmul_bwSmul ] ;
 congr 2 ; ext <;> simp +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm ];
 · grind;
 · ring;
 · grind;
 · grind;
 · interval_cases j <;> simp_all +decide [ bwSub_bwZero_left ];
 · intro x hx h; have := congr_arg ( fun z => cornerCoord n z ) h; norm_num [ cornerCoord_bwSmul, cornerCoord_bwCorner ] at this;
 have := congr_arg ( fun z => z.a ) this; norm_num [ Z8.mul_a ] at this;
 have := congr_arg ( fun z => z.c ) ‹-1 = { a := 1, b := 0, c := 1, d := 0 } * cornerCoord n x›; norm_num [ Z8.mul_c ] at this; omega;
 · intro x hx h; have := congr_arg ( fun z => cornerCoord n z ) h; norm_num [ cornerCoord_bwSmul, cornerCoord_bwCorner ] at this;
 injection this;
 grind

/-! ## The lower bound at all `n` for the `ν = 0` maximal monomial -/

/-
`λ^{2n}·bwT_{n+1}` does not preserve `BW_{n+1}`: the all-ones witness's image has a
corner syndrome of `λ`-valuation `2n+1`, one short of the required `2n+2`.
-/
theorem bwT_not_inBW (n : ℕ) :
 ¬ inBW (n + 1) (bwSmul (n + 1) (Z8.lam ^ (2 * n)) (bwT (n + 1))) := by
 intro h;
 -- By `inBW_succ_iff` (and `bwT_succ`, `bwSmul_succ`), extract the syndrome part: there is `w` with `inBW n w` and
 obtain ⟨w, hw⟩ : ∃ w : BWVec n, inBW n w ∧ bwSub n (bwSmul n (lam^(2*n)) (bwId n)) (bwSmul n (lam^(2*n)) (bwT n)) = bwSmul n oneI w := by
 simp_all +decide [ inBW_succ_iff ];
 -- Simplify the left side: by `bwSmul_bwSub` it is `bwSmul n (lam^(2*n)) (bwSub n (bwId n) (bwT n))`; by `bwSub_bwId_bwT` this is `bwSmul n (lam^(2*n)) (bwSmul n lam (bwCorner n))`; by `bwSmul_bwSmul` it is `bwSmul n (lam^(2*n) * lam) (bwCorner n) = bwSmul n (lam^(2*n+1)) (bwCorner n)`.
 have h_simp : bwSmul n (lam^(2*n+1)) (bwCorner n) = bwSmul n oneI w := by
 rw [ ← hw.2, pow_succ, mul_comm ];
 rw [ bwSmul_bwSub, bwSub_bwId_bwT ];
 rw [ mul_comm, bwSmul_bwSmul ];
 -- Now build a witness for `corner_inOneIL_iff n (2*n+1)`: take `w' = bwSmul n (-1) w`, which is in `BW` by `bwSmul_inBW`, and
 have h_witness : ∃ w' : BWVec n, inBW n w' ∧ bwSub n (bwZero n) (bwSmul n (lam^(2*n+1)) (bwCorner n)) = bwSmul n oneI w' := by
 use bwSmul n (-1) w;
 grind +suggestions;
 exact absurd ( corner_inOneIL_iff n ( 2 * n + 1 ) |>.1 h_witness ) ( by norm_num )

/-- **Target T2 (lower bound).** `λ^{2(n+1)−2} · bwT_{n+1}` does not preserve `BW_{n+1}`. -/
theorem bwT_not_gradeLE (n : ℕ) : ¬ gradeLEn (n + 1) (bwT (n + 1)) (2 * (n + 1) - 2) := by
 intro h
 have hkey := h (bwId (n + 1)) (bwId_inBW (n + 1))
 rw [bwSmul_bwMul_left, bwMul_bwId_right] at hkey
 have he : 2 * (n + 1) - 2 = 2 * n := by omega
 rw [he] at hkey
 exact bwT_not_inBW n hkey

/-- **Target T2 (exact grade).** `graden (bwT_{n+1}) = 2(n+1) − 1`. -/
theorem graden_bwT_eq (n : ℕ) : graden (n + 1) (bwT (n + 1)) = 2 * (n + 1) - 1 := by
 have hle : graden (n + 1) (bwT (n + 1)) ≤ 2 * (n + 1) - 1 := graden_bwT_le (n + 1)
 have hge : 2 * (n + 1) - 1 ≤ graden (n + 1) (bwT (n + 1)) := by
 by_contra hlt
 push_neg at hlt
 have hmem : gradeLEn (n + 1) (bwT (n + 1)) (graden (n + 1) (bwT (n + 1))) :=
 Nat.sInf_mem (gradeLEn_nonempty (n + 1) (bwT (n + 1)))
 have : gradeLEn (n + 1) (bwT (n + 1)) (2 * (n + 1) - 2) :=
 gradeLEn_of_le hmem (by omega)
 exact bwT_not_gradeLE n this
 omega

/-! ## The all-`n` lower bound for every `ν` (Target T3), maximal monomial `d = n`

The same corner machinery gives the matching lower bound for *every* valuation class,
not just `ν = 0`: the all-ones witness reduces `λ^{2n−p−1}·(topMon n n s)` to a corner
term of `λ`-valuation `2n−1`, one short of the conductor depth `2n`. -/

/-- `bwSub x y = bwAdd x ((-1)·y)`. -/
theorem bwSub_eq_add_neg (n : ℕ) (x y : BWVec n) :
 bwSub n x y = bwAdd n x (bwSmul n (-1) y) := by
 induction n with
 | zero => show (show Z8 from x) - (show Z8 from y) = (show Z8 from x) + (-1) * (show Z8 from y); ring
 | succ m ih => obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y; simp only [bwSub_succ, bwAdd_succ, bwSmul_succ, ih]

/-- `BW_n` is closed under subtraction. -/
theorem bwSub_inBW (n : ℕ) {x y : BWVec n} (hx : inBW n x) (hy : inBW n y) :
 inBW n (bwSub n x y) := by
 rw [bwSub_eq_add_neg]
 exact bwAdd_inBW n hx (bwSmul_inBW n (-1) hy)

/-- `(A + B) - A = B`. -/
theorem bwSub_bwAdd_left_cancel (n : ℕ) (A B : BWVec n) :
 bwSub n (bwAdd n A B) A = B := by
 induction n with
 | zero => show ((show Z8 from A) + (show Z8 from B)) - (show Z8 from A) = (show Z8 from B); ring
 | succ m ih => obtain ⟨A1, A2⟩ := A; obtain ⟨B1, B2⟩ := B; simp only [bwAdd_succ, bwSub_succ, ih]

/-
**General lower bound (all `ν`).** If `s − 1 = λ^p·u` for a unit `u` and `p < 2n`, then
`λ^{2n−p−1}·(topMon n n s)` does not preserve `BW_n`: the all-ones witness's image lands on
a corner term of valuation `2n−1 < 2n`.
-/
theorem topMon_not_inBW (n p : ℕ) (s u : Z8) (hu : IsUnit u)
 (hs : s - 1 = Z8.lam ^ p * u) (hp : p < 2 * n) :
 ¬ inBW n (bwSmul n (Z8.lam ^ (2 * n - p - 1)) (topMon n n s)) := by
 intro h
 have hB : inBW n (bwSmul n (lam ^ (2 * n - p - 1) * (lam ^ p * u)) (bwCorner n)) := by
 have hB : inBW n (bwSub n (bwSmul n (lam ^ (2 * n - p - 1)) (topMon n n s)) (bwSmul n (lam ^ (2 * n - p - 1)) (bwId n))) := by
 apply bwSub_inBW n h (bwSmul_inBW n (lam ^ (2 * n - p - 1)) (bwId_inBW n));
 unfold topMon at *;
 convert hB using 1;
 rw [ ← hs ];
 exact Eq.symm ( by rw [ topProj_eq_bwCorner, ← bwSmul_bwAdd, ← bwSmul_bwSmul ] ; exact bwSub_bwAdd_left_cancel _ _ _ );
 convert corner_inBW_iff n ( 2 * n - 1 ) |>.1 _ using 1;
 · grind;
 · convert bwSmul_inBW n ( hu.unit⁻¹.val ) hB using 1;
 convert bwSmul_bwSmul n ( hu.unit⁻¹.val ) ( lam ^ ( 2 * n - p - 1 ) * ( lam ^ p * u ) ) ( bwCorner n ) |> Eq.symm using 1;
 rw [ show 2 * n - 1 = ( 2 * n - p - 1 ) + p by omega ] ; simp +decide [ pow_add, mul_assoc, mul_left_comm, mul_comm ] ;
 simp +decide [ ← mul_assoc, ← Units.val_mul ]

/-- **General lower bound on the grade (all `ν`).** `graden (topMon n n s) ≥ 2n − p`. -/
theorem topMon_graden_ge (n p : ℕ) (s u : Z8) (hu : IsUnit u)
 (hs : s - 1 = Z8.lam ^ p * u) (hp : p < 2 * n) :
 2 * n - p ≤ graden n (topMon n n s) := by
 by_contra hlt
 push_neg at hlt
 have hmem : gradeLEn n (topMon n n s) (graden n (topMon n n s)) :=
 Nat.sInf_mem (gradeLEn_nonempty n (topMon n n s))
 have hg : gradeLEn n (topMon n n s) (2 * n - p - 1) := gradeLEn_of_le hmem (by omega)
 have := hg (bwId n) (bwId_inBW n)
 rw [bwSmul_bwMul_left, bwMul_bwId_right] at this
 exact topMon_not_inBW n p s u hu hs hp this

/-- **Exact grade (all `ν`), maximal monomial.** Combining the upper bound
`topMon_graden_le` and the lower bound `topMon_graden_ge`: `graden (topMon n n s) = 2n − p`
whenever `s − 1 = λ^p·u` with `u` a unit and `p < 2n`. -/
theorem topMon_graden_eq (n p : ℕ) (s u : Z8) (hu : IsUnit u)
 (hs : s - 1 = Z8.lam ^ p * u) (hp : p < 2 * n) :
 graden n (topMon n n s) = 2 * n - p :=
 le_antisymm (topMon_graden_le n n p s u hs) (topMon_graden_ge n p s u hu hs hp)

/-- **`ν = 0` exact grade:** `g(D_{x_{1⋯n}}) = 2n − 1` (`n ≥ 1`). -/
theorem graden_topMon_zeta_eq (n : ℕ) (hn : 1 ≤ n) :
 graden n (topMon n n Z8.zeta) = 2 * n - 1 := by
 apply topMon_graden_eq n 1 Z8.zeta (-1) isUnit_neg_one scalar_zeta; omega

/-- **`ν = 1` exact grade:** `g(D_{2·x_{1⋯n}}) = 2n − 2` (`n ≥ 2`; at `n = 1` the gate is
the Clifford `S` with grade `0`). -/
theorem graden_topMon_iu_eq (n : ℕ) (hn : 2 ≤ n) :
 graden n (topMon n n Z8.iu) = 2 * n - 2 := by
 apply topMon_graden_eq n 2 Z8.iu (Z8.iu * Z8.uuInv) isUnit_iu_uuInv scalar_iu; omega

/-- **`ν = 2` exact grade:** `g(D_{4·x_{1⋯n}}) = 2n − 4` (`n ≥ 3`; at `n ≤ 2` the gate is
Clifford with grade `0`). -/
theorem graden_topMon_negOne_eq (n : ℕ) (hn : 3 ≤ n) :
 graden n (topMon n n (-1)) = 2 * n - 4 := by
 apply topMon_graden_eq n 4 (-1) (Z8.iu * Z8.uuInv * Z8.uuInv) isUnit_iu_uuInv_sq scalar_negOne; omega

end Roots