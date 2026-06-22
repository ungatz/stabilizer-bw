import StabilizerBW.Qutrit.EisensteinToy.EisensteinIntegers

/-!
# T3 — The *genuine* qutrit Barnes–Wall grade over `ℤ[ω]`

This is the corrected qutrit analogue of the qubit level-3 Barnes–Wall lattice
`L₃ = {(x,y) ∈ ℤ[ζ₈]² : (1+i) ∣ (x+y)}` (`StabilizerBW.Roots/Lattice.lean`).

The decisive arithmetic point that Layer 90's *toy* lattice
(`StabilizerBW.QutritEisensteinAnalogue/BW3.lean`) got wrong is the choice of
**lattice modulus**.  In the qubit case the modulus is `1+i`, which is *not* the
ramified prime `λ₂ = 1-ζ₈` above the dimension `d = 2`, but its **square**:
`1+i = λ₂²·unit`, equivalently `(1+i)` and `(2)` have the same `λ₂`-valuation up
to the unit, with `ν_{λ₂}(2) = 2`.  The grade scaling, by contrast, is by the
single prime `λ₂`.  The "`2`" in the qubit closed form `g = 2·d − p` is exactly
`ν_{λ₂}(2) = 2`.

Layer 90's toy lattice used the *prime* `λ₃ = 1-ω` itself as the modulus
(`inL v ↔ λ₃ ∣ (x+y)`), the analogue of taking the qubit modulus to be `λ₂`
rather than `λ₂² = 1+i`.  That collapses the coefficient to `ν_{λ₃}(λ₃) = 1`.

Here we build the **genuine** lattice, whose modulus is the square of the
ramified prime, `λ₃² = -3·ω` (an associate of the dimension `d = 3`):

  `L = {(x,y,z) ∈ ℤ[ω]³ : λ₃² ∣ (x+y+z)}`   (equivalently `3 ∣ (x+y+z)`).

Working over a single qutrit (`ℤ[ω]³`, three computational levels) and with
`3×3` matrices, the grade `gradeQ M = min{k : λ₃^k·M·L ⊆ L}` then has the
**genuine coefficient `2 = ν_{λ₃}(3)`**, matching the qubit case exactly:

* `gradeQ_clockZ`      : `gradeQ (diag 1 ω ω²) = 1`   (the qutrit clock `Z₃`);
* `gradeQ_diagNegOne`  : `gradeQ (diag 1 (-1) 1) = 2`  (a Clifford phase `-1`):
  grade `2 = ν_{λ₃}(3)`, **not** the toy lattice's `1`.

It is also Clifford-invariant: conjugation by the qutrit shift `X₃` (a lattice
automorphism) and rescaling by the unit `ω` leave the grade unchanged
(`gradeQ_invariant_under_qutrit_clifford`).

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace QutritCSSBarnesWall

open QutritEis QutritEis.Eis

/-- The genuine lattice modulus: the **square** of the ramified prime,
`λ₃² = -3·ω`, an associate of the dimension `d = 3` (analogue of the qubit
modulus `1+i = λ₂²`). -/
def lamSq : Eis := lam ^ 2

/-! ## The single-qutrit column space `ℤ[ω]³` -/

/-- Column vectors over `ℤ[ω]` for one qutrit (three levels). -/
abbrev V3 := Eis × Eis × Eis

/-- The coordinate sum `x + y + z`. -/
def vsum (v : V3) : Eis := v.1 + v.2.1 + v.2.2

/-- Scalar action of `ℤ[ω]` on `ℤ[ω]³`. -/
def vsmul (r : Eis) (v : V3) : V3 := (r * v.1, r * v.2.1, r * v.2.2)

/-- Pairwise addition of column vectors. -/
def vadd (v w : V3) : V3 := (v.1 + w.1, v.2.1 + w.2.1, v.2.2 + w.2.2)

@[simp] theorem vsmul_fst (r : Eis) (v : V3) : (vsmul r v).1 = r * v.1 := rfl
@[simp] theorem vsmul_snd (r : Eis) (v : V3) : (vsmul r v).2.1 = r * v.2.1 := rfl
@[simp] theorem vsmul_thd (r : Eis) (v : V3) : (vsmul r v).2.2 = r * v.2.2 := rfl
@[simp] theorem vadd_fst (v w : V3) : (vadd v w).1 = v.1 + w.1 := rfl
@[simp] theorem vadd_snd (v w : V3) : (vadd v w).2.1 = v.2.1 + w.2.1 := rfl
@[simp] theorem vadd_thd (v w : V3) : (vadd v w).2.2 = v.2.2 + w.2.2 := rfl

/-! ## Decidable divisibility by `λ₃² = -3ω` -/

/-- Decidable criterion for divisibility by `λ₃² = -3ω`: since `(λ₃²) = (3)`
as ideals (`λ₃² = -3·ω` with `ω` a unit), this is `3 ∣ re ∧ 3 ∣ im`. -/
def dvdLamSq (z : Eis) : Prop := (3 : ℤ) ∣ z.re ∧ (3 : ℤ) ∣ z.im

instance (z : Eis) : Decidable (dvdLamSq z) := by unfold dvdLamSq; infer_instance

/-- `λ₃² = -3ω = ⟨0, -3⟩`. -/
theorem lamSq_val : lamSq = ⟨0, -3⟩ := by decide

/-- The parity criterion `dvdLamSq` is honest divisibility by `λ₃²`. -/
theorem dvdLamSq_iff (z : Eis) : dvdLamSq z ↔ lamSq ∣ z := by
  constructor
  · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    -- z = ⟨3p, 3q⟩ and (λ₃² · ⟨p-q, p⟩) = ⟨3p, 3q⟩.
    refine ⟨⟨p - q, p⟩, ?_⟩
    apply Eis.ext'
    · rw [lamSq_val]; simp only [Eis.mul_re]; omega
    · rw [lamSq_val]; simp only [Eis.mul_im]; omega
  · rintro ⟨w, rfl⟩
    obtain ⟨wr, wi⟩ := w
    refine ⟨⟨wi, ?_⟩, ⟨wi - wr, ?_⟩⟩
    · rw [lamSq_val]; simp only [Eis.mul_re]; ring
    · rw [lamSq_val]; simp only [Eis.mul_im]; ring

/-! ## The genuine lattice `L` -/

/-- Membership in the genuine qutrit Barnes–Wall lattice
`L = {(x,y,z) : λ₃² ∣ (x+y+z)}`. -/
def inL (v : V3) : Prop := lamSq ∣ vsum v

instance : DecidablePred inL := fun v =>
  decidable_of_iff (dvdLamSq (vsum v)) (dvdLamSq_iff _)

theorem inL_iff (v : V3) : inL v ↔ dvdLamSq (vsum v) := (dvdLamSq_iff _).symm

theorem inL_zero : inL (0, 0, 0) := by simp [inL, vsum]

theorem inL_vadd {v w : V3} (hv : inL v) (hw : inL w) : inL (vadd v w) := by
  unfold inL vsum vadd at *
  simp only
  have : (v.1 + w.1) + (v.2.1 + w.2.1) + (v.2.2 + w.2.2)
      = (v.1 + v.2.1 + v.2.2) + (w.1 + w.2.1 + w.2.2) := by ring
  rw [this]; exact Dvd.dvd.add hv hw

theorem inL_vsmul (r : Eis) {v : V3} (hv : inL v) : inL (vsmul r v) := by
  unfold inL vsum vsmul at *
  simp only
  have : r * v.1 + r * v.2.1 + r * v.2.2 = r * (v.1 + v.2.1 + v.2.2) := by ring
  rw [this]; exact Dvd.dvd.mul_left hv r

/-! ## Generators of `L` -/

/-- First generator `(1, -1, 0)`. -/
def g1 : V3 := (1, -1, 0)
/-- Second generator `(0, 1, -1)`. -/
def g2 : V3 := (0, 1, -1)
/-- Third generator `(0, 0, λ₃²)`. -/
def g3 : V3 := (0, 0, lamSq)

theorem inL_g1 : inL g1 := by decide
theorem inL_g2 : inL g2 := by decide
theorem inL_g3 : inL g3 := by decide

/-- Every lattice vector decomposes over the three generators:
`v = v.1 • g₁ + (v.1 + v.2.1) • g₂ + k • g₃`, where `k` solves `λ₃² · k = x+y+z`. -/
theorem inL_decompose {v : V3} (hv : inL v) :
    ∃ k : Eis,
      v = vadd (vsmul v.1 g1) (vadd (vsmul (v.1 + v.2.1) g2) (vsmul k g3)) := by
  obtain ⟨k, hk⟩ := hv
  obtain ⟨x, y, z⟩ := v
  refine ⟨k, ?_⟩
  simp only [vadd, vsmul, g1, g2, g3, vsum] at *
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [mul_one, mul_zero, add_zero]
  · simp only [mul_neg, mul_one, mul_zero, add_zero]; ring
  · simp only [mul_zero, mul_neg, mul_one, zero_add]
    -- z = -(x+y) + λ₃²·k since (x+y+z) = λ₃²·k
    have hk' : x + y + z = lamSq * k := hk
    linear_combination hk'

/-! ## `3×3` matrices over `ℤ[ω]` and their action -/

/-- A `3×3` matrix over `ℤ[ω]` (row-major). -/
structure EMat3 where
  a11 : Eis
  a12 : Eis
  a13 : Eis
  a21 : Eis
  a22 : Eis
  a23 : Eis
  a31 : Eis
  a32 : Eis
  a33 : Eis
deriving DecidableEq, Repr

namespace EMat3

@[ext] theorem ext' {M N : EMat3}
    (h11 : M.a11 = N.a11) (h12 : M.a12 = N.a12) (h13 : M.a13 = N.a13)
    (h21 : M.a21 = N.a21) (h22 : M.a22 = N.a22) (h23 : M.a23 = N.a23)
    (h31 : M.a31 = N.a31) (h32 : M.a32 = N.a32) (h33 : M.a33 = N.a33) : M = N := by
  cases M; cases N; simp_all

/-- Matrix–vector product. -/
def mulVec (M : EMat3) (v : V3) : V3 :=
  (M.a11 * v.1 + M.a12 * v.2.1 + M.a13 * v.2.2,
   M.a21 * v.1 + M.a22 * v.2.1 + M.a23 * v.2.2,
   M.a31 * v.1 + M.a32 * v.2.1 + M.a33 * v.2.2)

/-- Scalar multiple of a matrix. -/
def smul (r : Eis) (M : EMat3) : EMat3 :=
  ⟨r * M.a11, r * M.a12, r * M.a13,
   r * M.a21, r * M.a22, r * M.a23,
   r * M.a31, r * M.a32, r * M.a33⟩

/-- Matrix product. -/
def mul (M N : EMat3) : EMat3 :=
  ⟨M.a11*N.a11 + M.a12*N.a21 + M.a13*N.a31,
   M.a11*N.a12 + M.a12*N.a22 + M.a13*N.a32,
   M.a11*N.a13 + M.a12*N.a23 + M.a13*N.a33,
   M.a21*N.a11 + M.a22*N.a21 + M.a23*N.a31,
   M.a21*N.a12 + M.a22*N.a22 + M.a23*N.a32,
   M.a21*N.a13 + M.a22*N.a23 + M.a23*N.a33,
   M.a31*N.a11 + M.a32*N.a21 + M.a33*N.a31,
   M.a31*N.a12 + M.a32*N.a22 + M.a33*N.a32,
   M.a31*N.a13 + M.a32*N.a23 + M.a33*N.a33⟩

/-- The identity matrix. -/
def one : EMat3 := ⟨1,0,0, 0,1,0, 0,0,1⟩

theorem mulVec_vadd (M : EMat3) (v w : V3) :
    M.mulVec (vadd v w) = vadd (M.mulVec v) (M.mulVec w) := by
  simp only [mulVec, vadd]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> ring

theorem mulVec_vsmul (M : EMat3) (r : Eis) (v : V3) :
    M.mulVec (vsmul r v) = vsmul r (M.mulVec v) := by
  simp only [mulVec, vsmul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> ring

@[simp] theorem smul_mulVec (r : Eis) (M : EMat3) (v : V3) :
    (smul r M).mulVec v = vsmul r (M.mulVec v) := by
  simp only [smul, mulVec, vsmul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> ring

@[simp] theorem smul_one_mat (M : EMat3) : smul 1 M = M := by cases M; simp [smul]

theorem smul_smul (r s : Eis) (M : EMat3) : smul r (smul s M) = smul (r * s) M := by
  cases M; simp only [smul]; refine EMat3.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem mulVec_mul (M N : EMat3) (v : V3) :
    (mul M N).mulVec v = M.mulVec (N.mulVec v) := by
  simp only [mul, mulVec]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> ring

@[simp] theorem one_mulVec (v : V3) : one.mulVec v = v := by
  simp only [one, mulVec]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

theorem smul_mul_left (r : Eis) (M N : EMat3) :
    mul (smul r M) N = smul r (mul M N) := by
  simp only [mul, smul]; refine EMat3.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

end EMat3

/-! ## The grade -/

/-- An operator maps `L` into `L`. -/
def MapsToL (M : EMat3) : Prop := ∀ v, inL v → inL (M.mulVec v)

/-- **Reduction lemma.** A matrix preserves `L` iff it preserves all three
generators. -/
theorem mapsToL_of_gens (M : EMat3)
    (h1 : inL (M.mulVec g1)) (h2 : inL (M.mulVec g2)) (h3 : inL (M.mulVec g3)) :
    MapsToL M := by
  intro v hv
  obtain ⟨k, hk⟩ := inL_decompose hv
  rw [hk, EMat3.mulVec_vadd, EMat3.mulVec_vadd,
      EMat3.mulVec_vsmul, EMat3.mulVec_vsmul, EMat3.mulVec_vsmul]
  exact inL_vadd (inL_vsmul _ h1) (inL_vadd (inL_vsmul _ h2) (inL_vsmul _ h3))

theorem mapsToL_smul (r : Eis) {M : EMat3} (h : MapsToL M) :
    MapsToL (EMat3.smul r M) := by
  intro v hv
  rw [EMat3.smul_mulVec]
  exact inL_vsmul r (h v hv)

/-- `gradeLE M k`: the operator `λ₃^k · M` maps `L` into `L`. -/
def gradeLE (M : EMat3) (k : ℕ) : Prop := MapsToL (EMat3.smul (lam ^ k) M)

theorem gradeLE_succ {M : EMat3} {k : ℕ} (h : gradeLE M k) : gradeLE M (k + 1) := by
  unfold gradeLE at *
  have hpow : (lam ^ (k + 1)) = lam * lam ^ k := by ring
  rw [hpow]
  intro v hv
  rw [show EMat3.smul (lam * lam ^ k) M = EMat3.smul lam (EMat3.smul (lam ^ k) M) by
    cases M; simp [EMat3.smul]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring]
  exact mapsToL_smul lam h v hv

theorem gradeLE_of_le {M : EMat3} {k k' : ℕ} (h : gradeLE M k) (hk : k ≤ k') :
    gradeLE M k' := by
  induction hk with
  | refl => exact h
  | step _ ih => exact gradeLE_succ ih

/-- The genuine qutrit grade `gradeQ M = min{k : λ₃^k·M·L ⊆ L}`. -/
noncomputable def gradeQ (M : EMat3) : ℕ := sInf {k | gradeLE M k}

theorem gradeQ_le {M : EMat3} {k : ℕ} (h : gradeLE M k) : gradeQ M ≤ k :=
  Nat.sInf_le h

theorem gradeQ_eq_zero {M : EMat3} (h0 : gradeLE M 0) : gradeQ M = 0 :=
  Nat.le_zero.mp (Nat.sInf_le h0)

theorem gradeQ_eq_one {M : EMat3} (h1 : gradeLE M 1) (h0 : ¬ gradeLE M 0) :
    gradeQ M = 1 := by
  have hmem : gradeQ M ∈ {k | gradeLE M k} := Nat.sInf_mem ⟨1, h1⟩
  rcases Nat.lt_or_ge (gradeQ M) 1 with h | h
  · interval_cases (gradeQ M)
    · exact absurd hmem h0
  · exact le_antisymm (Nat.sInf_le h1) h

theorem gradeQ_eq_two {M : EMat3} (h2 : gradeLE M 2)
    (h1 : ¬ gradeLE M 1) (h0 : ¬ gradeLE M 0) : gradeQ M = 2 := by
  have hmem : gradeQ M ∈ {k | gradeLE M k} := Nat.sInf_mem ⟨2, h2⟩
  rcases Nat.lt_or_ge (gradeQ M) 2 with h | h
  · interval_cases (gradeQ M)
    · exact absurd hmem h0
    · exact absurd hmem h1
  · exact le_antisymm (Nat.sInf_le h2) h

/-! ## Named diagonal / permutation operators -/

/-- A diagonal matrix `diag(a, b, c)`. -/
def diag (a b c : Eis) : EMat3 := ⟨a,0,0, 0,b,0, 0,0,c⟩

/-- The identity. -/
def diagId : EMat3 := diag 1 1 1
/-- The qutrit clock gate `Z₃ = diag(1, ω, ω²)`. -/
def clockZ : EMat3 := diag 1 omega (omega ^ 2)
/-- A Clifford phase `diag(1, -1, 1)` (the order-2 phase on one level). -/
def diagNegOne : EMat3 := diag 1 (-1) 1
/-- `diag(1, 1, ω)`, a single non-trivial order-3 phase. -/
def diagOmega1 : EMat3 := diag 1 1 omega
/-- The qutrit shift `X₃`: the cyclic permutation of the three levels. -/
def shiftX : EMat3 := ⟨0,0,1, 1,0,0, 0,1,0⟩

/-! ### Grades of the canonical witnesses -/

theorem clockZ_gradeLE_one : gradeLE clockZ 1 := by
  unfold gradeLE clockZ diag
  apply mapsToL_of_gens <;> decide

theorem clockZ_not_gradeLE_zero : ¬ gradeLE clockZ 0 := by
  intro h
  have h1 : inL g1 := inL_g1
  have := h g1 (by simpa using h1)
  revert this; decide

/-- **The qutrit clock `Z₃ = diag(1, ω, ω²)` has grade `1`.** -/
theorem gradeQ_clockZ : gradeQ clockZ = 1 :=
  gradeQ_eq_one clockZ_gradeLE_one clockZ_not_gradeLE_zero

theorem diagOmega1_gradeLE_one : gradeLE diagOmega1 1 := by
  unfold gradeLE diagOmega1 diag
  apply mapsToL_of_gens <;> decide

theorem diagOmega1_not_gradeLE_zero : ¬ gradeLE diagOmega1 0 := by
  intro h
  have := h g2 (by simpa using inL_g2)
  revert this; decide

/-- `diag(1, 1, ω)` has grade `1`. -/
theorem gradeQ_diagOmega1 : gradeQ diagOmega1 = 1 :=
  gradeQ_eq_one diagOmega1_gradeLE_one diagOmega1_not_gradeLE_zero

theorem diagNegOne_gradeLE_two : gradeLE diagNegOne 2 := by
  unfold gradeLE diagNegOne diag
  apply mapsToL_of_gens <;> decide

theorem diagNegOne_not_gradeLE_one : ¬ gradeLE diagNegOne 1 := by
  intro h
  have := h g1 (by simpa using inL_g1)
  revert this; decide

theorem diagNegOne_not_gradeLE_zero : ¬ gradeLE diagNegOne 0 := by
  intro h
  have := h g1 (by simpa using inL_g1)
  revert this; decide

/-- **The Clifford phase `diag(1, -1, 1)` has grade `2 = ν_{λ₃}(3)`** over the
genuine lattice — matching the qubit coefficient, and correcting the toy
lattice's spurious `1`. -/
theorem gradeQ_diagNegOne : gradeQ diagNegOne = 2 :=
  gradeQ_eq_two diagNegOne_gradeLE_two diagNegOne_not_gradeLE_one diagNegOne_not_gradeLE_zero

theorem diagId_gradeLE_zero : gradeLE diagId 0 := by
  unfold gradeLE diagId diag
  simp only [pow_zero, EMat3.smul_one_mat]
  apply mapsToL_of_gens <;> decide

theorem gradeQ_diagId : gradeQ diagId = 0 := gradeQ_eq_zero diagId_gradeLE_zero

/-! ## Clifford invariance of the grade -/

/-- The shift `X₃` is a lattice automorphism (grade `0`), and so is its inverse
`X₃²`. -/
theorem shiftX_mapsToL : MapsToL shiftX := by
  apply mapsToL_of_gens <;> decide

/-- `X₃` composed with `X₃²` is the identity (so `X₃` is invertible with inverse
`X₃²`). -/
theorem shiftX_cube : EMat3.mul shiftX (EMat3.mul shiftX shiftX) = EMat3.one := by
  decide

theorem shiftXsq_mapsToL : MapsToL (EMat3.mul shiftX shiftX) := by
  apply mapsToL_of_gens <;> decide

/-- **Conjugation invariance.** If `P` and `Q` preserve `L` and `P·Q = I`, then
conjugation by `P` (with inverse `Q`) leaves the grade unchanged. -/
theorem gradeLE_conj {P Q M : EMat3} (hP : MapsToL P) (hQ : MapsToL Q)
    (hQP : EMat3.mul Q P = EMat3.one) (k : ℕ) :
    gradeLE (EMat3.mul P (EMat3.mul M Q)) k ↔ gradeLE M k := by
  constructor
  · intro h v hv
    -- feed `P v ∈ L` into the hypothesis, then post-compose with `Q`
    have key := h (P.mulVec v) (hP v hv)
    have e : (EMat3.smul (lam ^ k) (EMat3.mul P (EMat3.mul M Q))).mulVec (P.mulVec v)
        = vsmul (lam ^ k) (P.mulVec (M.mulVec v)) := by
      rw [EMat3.smul_mulVec, EMat3.mulVec_mul, EMat3.mulVec_mul,
        ← EMat3.mulVec_mul Q P v, hQP, EMat3.one_mulVec]
    rw [e] at key
    have key2 := hQ _ key
    have e2 : Q.mulVec (vsmul (lam ^ k) (P.mulVec (M.mulVec v)))
        = (EMat3.smul (lam ^ k) M).mulVec v := by
      rw [EMat3.mulVec_vsmul, ← EMat3.mulVec_mul Q P (M.mulVec v), hQP, EMat3.one_mulVec,
        EMat3.smul_mulVec]
    rw [e2] at key2
    exact key2
  · intro h v hv
    have key := h (Q.mulVec v) (hQ v hv)
    have key2 := hP _ key
    have e2 : P.mulVec ((EMat3.smul (lam ^ k) M).mulVec (Q.mulVec v))
        = (EMat3.smul (lam ^ k) (EMat3.mul P (EMat3.mul M Q))).mulVec v := by
      rw [EMat3.smul_mulVec, EMat3.smul_mulVec, EMat3.mulVec_vsmul, EMat3.mulVec_mul,
        EMat3.mulVec_mul]
    rw [e2] at key2
    exact key2

theorem gradeQ_conj {P Q M : EMat3} (hP : MapsToL P) (hQ : MapsToL Q)
    (hQP : EMat3.mul Q P = EMat3.one) :
    gradeQ (EMat3.mul P (EMat3.mul M Q)) = gradeQ M := by
  unfold gradeQ
  congr 1
  ext k
  exact gradeLE_conj hP hQ hQP k

/-- **Grade is invariant under rescaling by the unit `ω`** (a global Clifford
phase): `ω·L = L`, so it does not change the grade. -/
theorem gradeLE_unit_smul {M : EMat3} {k : ℕ} (u : Eis) (hu : IsUnit u) :
    gradeLE (EMat3.smul u M) k ↔ gradeLE M k := by
  obtain ⟨v, hv⟩ := hu
  constructor
  · intro h w hw
    have hMmaps : MapsToL
        (EMat3.smul ((v⁻¹ : Eisˣ).val) (EMat3.smul (lam ^ k) (EMat3.smul u M))) :=
      mapsToL_smul _ h
    have e : EMat3.smul ((v⁻¹ : Eisˣ).val) (EMat3.smul (lam ^ k) (EMat3.smul u M))
        = EMat3.smul (lam ^ k) M := by
      rw [EMat3.smul_smul, EMat3.smul_smul,
        show (v⁻¹ : Eisˣ).val * lam ^ k * u = lam ^ k * ((v⁻¹ : Eisˣ).val * u) by ring,
        ← hv, Units.inv_mul, mul_one]
    rw [e] at hMmaps
    exact hMmaps w hw
  · intro h w hw
    have hMmaps : MapsToL (EMat3.smul u (EMat3.smul (lam ^ k) M)) := mapsToL_smul u h
    have e : EMat3.smul u (EMat3.smul (lam ^ k) M)
        = EMat3.smul (lam ^ k) (EMat3.smul u M) := by
      rw [EMat3.smul_smul, EMat3.smul_smul, mul_comm]
    rw [e] at hMmaps
    exact hMmaps w hw

theorem gradeQ_unit_smul {M : EMat3} (u : Eis) (hu : IsUnit u) :
    gradeQ (EMat3.smul u M) = gradeQ M := by
  unfold gradeQ
  congr 1
  ext k
  exact gradeLE_unit_smul u hu

/-- **Clifford invariance of the genuine qutrit grade (headline).** The grade is
invariant under (i) conjugation by the qutrit shift `X₃` (a lattice
automorphism, with inverse `X₃²`), and (ii) rescaling by the unit phase `ω`.
These are the generating qutrit Clifford symmetries that act on the witnesses,
so the grade is a genuine Clifford invariant on them. -/
theorem gradeQ_invariant_under_qutrit_clifford (M : EMat3) :
    gradeQ (EMat3.mul shiftX (EMat3.mul M (EMat3.mul shiftX shiftX))) = gradeQ M
    ∧ gradeQ (EMat3.smul omega M) = gradeQ M := by
  refine ⟨?_, gradeQ_unit_smul omega isUnit_omega⟩
  apply gradeQ_conj shiftX_mapsToL shiftXsq_mapsToL
  -- X₃² · X₃ = I
  decide

end QutritCSSBarnesWall
