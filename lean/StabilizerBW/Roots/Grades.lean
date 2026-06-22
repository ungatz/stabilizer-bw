import StabilizerBW.Roots.Lattice

/-!
# Grades at level 3 (Priority 1.4) and the four √X automorphisms (Priority 1.2)

The grade is `g(U) = min k ≥ 0 with λ^k·U·L₃ ⊆ L₃`.  For an *integral* operator
`M` we package this as `gradeLE M k := MapsToL (λ^k · M)` and `grade M := sInf {k | …}`.

* `g(T) = 1` for `T = diag(1, ζ₈)`  (integral, Priority 1.4);
* `g(ζ₈·I) = 0`                      (integral, Priority 1.4);
* the four unitary square roots of `X` preserve `L₃` (Priority 1.2);
* `g(V) = g(H) = 0`                  (half-integral, Priority 1.4).

The half-integral operators `V, H, √X` carry a `1/2` factor; they are represented
by `halfAction M v = ((M·v).1 / 2, (M·v).2 / 2)` with `M = 2U` integral, so the
division is exact on `L₃`.
-/

namespace Roots
open Z8 Mat2

/-! ## Interaction of scalar multiples with the action -/

@[simp] theorem smul_mulVec (r : Z8) (M : Mat2) (v : Z8 × Z8) :
    (Mat2.smul r M).mulVec v = vsmul r (M.mulVec v) := by
  simp [Mat2.smul, Mat2.mulVec, vsmul]; constructor <;> ring

@[simp] theorem smul_one_mat (M : Mat2) : Mat2.smul 1 M = M := by
  cases M; simp [Mat2.smul]

/-- Scaling preserves `MapsToL` (since `λ, r ∈ R` act on the lattice). -/
theorem mapsToL_smul (r : Z8) {M : Mat2} (h : MapsToL M) : MapsToL (Mat2.smul r M) := by
  intro v hv
  rw [smul_mulVec]
  exact inL_vsmul r (h v hv)

/-! ## The grade of an integral operator -/

/-- `gradeLE M k`: the operator `λ^k · M` maps `L₃` into `L₃`. -/
def gradeLE (M : Mat2) (k : ℕ) : Prop := MapsToL (Mat2.smul (Z8.lam ^ k) M)

/-- `gradeLE` is upward closed. -/
theorem gradeLE_succ {M : Mat2} {k : ℕ} (h : gradeLE M k) : gradeLE M (k+1) := by
  unfold gradeLE at *
  have : (Z8.lam ^ (k+1)) = Z8.lam * Z8.lam ^ k := by ring
  rw [this]
  intro v hv
  rw [show Mat2.smul (Z8.lam * Z8.lam ^ k) M = Mat2.smul Z8.lam (Mat2.smul (Z8.lam^k) M) by
    cases M; simp [Mat2.smul]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring]
  exact mapsToL_smul Z8.lam h v hv

/-- The grade `g(M) = min k with λ^k·M·L ⊆ L`. -/
noncomputable def grade (M : Mat2) : ℕ := sInf {k | gradeLE M k}

theorem grade_le {M : Mat2} {k : ℕ} (h : gradeLE M k) : grade M ≤ k :=
  Nat.sInf_le h

/-- If `λ^k·M` preserves `L` but `M` itself does not (and the set is nonempty),
the grade is exactly `k`… here specialised to the case used below. -/
theorem grade_eq_one {M : Mat2} (h1 : gradeLE M 1) (h0 : ¬ gradeLE M 0) : grade M = 1 := by
  have hmem : grade M ∈ {k | gradeLE M k} := Nat.sInf_mem ⟨1, h1⟩
  have hle : grade M ≤ 1 := Nat.sInf_le h1
  rcases Nat.lt_or_ge (grade M) 1 with h | h
  · interval_cases (grade M)
    · exact absurd hmem h0
  · omega

theorem grade_eq_zero {M : Mat2} (h0 : gradeLE M 0) : grade M = 0 :=
  Nat.le_zero.mp (Nat.sInf_le h0)

/-! ## Priority 1.4 — `g(T) = 1` -/

/-- `T` does not preserve `L₃`: it sends `(1,1) ∈ L₃` out of `L₃`. -/
theorem T_not_gradeLE_zero : ¬ gradeLE T 0 := by
  intro h
  have h1 : inL ((1 : Z8), (1 : Z8)) := by decide
  have := h ((1:Z8),(1:Z8)) (by simpa using h1)
  revert this
  decide

/-- `λ·T` preserves both generators, hence all of `L₃`. -/
theorem T_gradeLE_one : gradeLE T 1 := by
  unfold gradeLE
  apply mapsToL_of_gens
  · decide
  · decide

/-- **Priority 1.4: `g(T) = 1`.** -/
theorem grade_T : grade T = 1 := grade_eq_one T_gradeLE_one T_not_gradeLE_zero

/-- The explicit generating-set check from the prompt: `λ·T` maps
`{(1,-1), (0,1+i), (1,1), (ζ₈,-ζ₈)}` into `L₃`, while `T·(1,1) ∉ L₃`. -/
theorem lamT_maps_generating_set :
    inL ((Mat2.smul Z8.lam T).mulVec (1, -1)) ∧
    inL ((Mat2.smul Z8.lam T).mulVec (0, Z8.oneI)) ∧
    inL ((Mat2.smul Z8.lam T).mulVec (1, 1)) ∧
    inL ((Mat2.smul Z8.lam T).mulVec (Z8.zeta, -Z8.zeta)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem T_one_one_not_inL : ¬ inL (T.mulVec (1, 1)) := by decide

/-! ## Priority 1.4 — `g(ζ₈·I) = 0` -/

/-- `ζ₈·I` is a lattice automorphism: grade `0`. -/
theorem zetaI_gradeLE_zero : gradeLE (Mat2.smul Z8.zeta II) 0 := by
  unfold gradeLE
  rw [Z8.lam_eq] -- not needed but harmless; simplify λ^0
  simp only [pow_zero, smul_one_mat]
  apply mapsToL_of_gens <;> decide

/-- **Priority 1.4: `g(ζ₈·I) = 0`.** -/
theorem grade_zetaI : grade (Mat2.smul Z8.zeta II) = 0 := grade_eq_zero zetaI_gradeLE_zero

/-! ## Half-integral operators: `V`, `H`, and the four roots of `X` -/

/-- Componentwise evenness. -/
def Even2 (z : Z8) : Prop := 2 ∣ z.a ∧ 2 ∣ z.b ∧ 2 ∣ z.c ∧ 2 ∣ z.d

/-- Exact halving of an even element is additive. -/
theorem half_add_of_even {x y : Z8} (hx : Even2 x) (hy : Even2 y) :
    half x + half y = half (x + y) := by
  obtain ⟨⟨pa,ha⟩,⟨pb,hb⟩,⟨pc,hc⟩,⟨pd,hd⟩⟩ := hx
  obtain ⟨⟨qa,ka⟩,⟨qb,kb⟩,⟨qc,kc⟩,⟨qd,kd⟩⟩ := hy
  ext <;> simp [half] <;> omega

/-- The "doubled" action `halfAction M v = (M·v)/2`, exact when `M·v` is even. -/
def halfAction (M : Mat2) (v : Z8 × Z8) : Z8 × Z8 :=
  (half (M.mulVec v).1, half (M.mulVec v).2)

/-- An operator `M = 2U` with `U` lattice-preserving: the half-action preserves `L₃`
provided the doubled image is even (so halving is exact) and the halved coordinate-sum
lands in `L₃`.  This is the grade-`0` statement for a half-integral `U`. -/
def HalfMapsToL (M : Mat2) : Prop := ∀ v, inL v → inL (halfAction M v)

/-- Reduction: to show a half-integral operator preserves `L₃`, show its doubled
image is even (halving is exact) and the halved coordinate-sum is `(1+i)`-divisible. -/
theorem HalfMapsToL_of (M : Mat2)
    (heven1 : ∀ v, inL v → Even2 (M.mulVec v).1)
    (heven2 : ∀ v, inL v → Even2 (M.mulVec v).2)
    (hsum : ∀ v, inL v → dvdOneI (half ((M.mulVec v).1 + (M.mulVec v).2))) :
    HalfMapsToL M := by
  intro v hv
  rw [inL_iff]
  have hadd : (halfAction M v).1 + (halfAction M v).2
      = half ((M.mulVec v).1 + (M.mulVec v).2) := by
    simp only [halfAction]
    exact half_add_of_even (heven1 v hv) (heven2 v hv)
  rw [hadd]
  exact hsum v hv

/-! ### Priority 1.4: `g(V) = 0` -/

/-- `oneI² = 2i`, used to show doubled images are even on `L₃`. -/
theorem oneI_sq : Z8.oneI * Z8.oneI = 2 * Z8.iu := by decide

/-
**Priority 1.4: `V` preserves `L₃` (grade 0).**
-/
theorem V_HalfMapsToL : HalfMapsToL twoV := by
  intro v hv;
  rw [inL_iff] at *;
  unfold halfAction Mat2.mulVec twoV;
  simp +decide [ Z8.dvdOneI, Z8.half ] at *;
  omega

/-! ### Priority 1.4: `g(H) = 0` -/

/-- The integral double of `H`: `2H = √2 · (√2H)`. -/
def twoH : Mat2 := Mat2.smul Z8.sqrt2 sqrt2H

/-
**Priority 1.4: `H` preserves `L₃` (grade 0).**
-/
theorem H_HalfMapsToL : HalfMapsToL twoH := by
  intro v hv
  rw [inL_iff] at *;
  unfold halfAction Mat2.mulVec twoH Mat2.smul Roots.Mat2.sqrt2H;
  simp +decide [ Z8.dvdOneI, Z8.half, Z8.sqrt2 ] at *;
  omega

/-! ## Priority 1.2 — the four unitary square roots of `X` -/

/-- `2·R` for the four roots `R = ½[(α+β)I + (α-β)X]`, `α ∈ {±1}`, `β ∈ {±i}`. -/
def twoR1 : Mat2 := twoV                              -- (α,β) = (1, i)
def twoR2 : Mat2 := ⟨1 - Z8.iu, Z8.oneI, Z8.oneI, 1 - Z8.iu⟩  -- (1, -i)
def twoR3 : Mat2 := ⟨-1 + Z8.iu, -1 - Z8.iu, -1 - Z8.iu, -1 + Z8.iu⟩  -- (-1, i)
def twoR4 : Mat2 := ⟨-1 - Z8.iu, -1 + Z8.iu, -1 + Z8.iu, -1 - Z8.iu⟩  -- (-1, -i)

/-- Each doubled root squares to `4X` (i.e. `R² = X`). -/
theorem twoR1_sq : twoR1 * twoR1 = Mat2.smul 4 X := by decide
theorem twoR2_sq : twoR2 * twoR2 = Mat2.smul 4 X := by decide
theorem twoR3_sq : twoR3 * twoR3 = Mat2.smul 4 X := by decide
theorem twoR4_sq : twoR4 * twoR4 = Mat2.smul 4 X := by decide

/-- The four roots map `L₃` into `L₃` (Clifford / lattice automorphisms). -/
theorem twoR1_HalfMapsToL : HalfMapsToL twoR1 := V_HalfMapsToL

theorem twoR2_HalfMapsToL : HalfMapsToL twoR2 := by
  intro v hv; rw [ inL_iff ] at *; unfold halfAction Mat2.mulVec twoR2; simp +decide [ Z8.dvdOneI, Z8.half ] at *;
  grind

theorem twoR3_HalfMapsToL : HalfMapsToL twoR3 := by
  intro v hv;
  rw [inL_iff] at *;
  unfold halfAction; simp +decide [ Z8.dvdOneI, Z8.half ] at *;
  unfold twoR3; simp +decide [ Z8.iu ] at *; omega;

theorem twoR4_HalfMapsToL : HalfMapsToL twoR4 := by
  intro v hv;
  convert inL_iff _ |>.2 _ using 1;
  unfold halfAction;
  unfold twoR4; simp +decide [ Z8.dvdOneI, Z8.half, Z8.iu ] ;
  constructor <;> rw [ inL_iff ] at hv <;> norm_num [ Z8.dvdOneI ] at hv ⊢ <;> omega;

/-- Unitarity of the roots in doubled form: `(2R₁)(2R₂) = 4I` (i.e. `V·V† = I`),
so `R₂ = R₁⁻¹` and, since both preserve `L₃`, each root is a lattice *automorphism*. -/
theorem twoR1_twoR2_unitary : twoR1 * twoR2 = Mat2.smul 4 II := by decide
theorem twoR3_twoR4_unitary : twoR3 * twoR4 = Mat2.smul 4 II := by decide

end Roots