import StabilizerBW.Roots.Zeta16

/-!
# Target B — the level-4 two-lattice grade table over `ℤ[ζ₁₆]`

`R = ℤ[ζ₁₆]`, `λ = λ₁₆ = 1 - ζ₁₆` (`Z16.lam16`). We study two rank-2 lattices in `R²`,
distinguished only by the divisor of the coordinate sum:

* `L4a := {(a,b) : (1-ζ₈) ∣ (a+b)}` — the genuine level-4 design; `(1-ζ₈) = lam8 ∼ λ²`;
* `L4b := {(a,b) : (1+i) ∣ (a+b)}` — the base change of the level-3 lattice; `(1+i) ∼ λ⁴`.

The grade is `g_d(D) = min k with λ^k·D·L_d ⊆ L_d` (`graded`), where `λ = lam16` in both
cases. We compute the grades of the three diagonal operators

 `T = diag(1, ζ₈)`, `√T = diag(1, ζ₁₆)`, `ζ₁₆·I = diag(ζ₁₆, ζ₁₆)`.

## The kernel-confirmed table

| `U` | `g_a(U)` (L4a) | `g_b(U)` (L4b) |
|---------|----------------|----------------|
| `T` | 0 | 2 |
| `√T` | 1 | 3 |
| `ζ₁₆·I` | 0 | 0 |

This **confirms the revised hand predictions** and refutes the original queued slogan
(`g_b(√T) = 3`, not `≤ 1`). Packaged as `Theorem B.4` (`level4_table` / `level4_slogan`):
* **level self-similarity:** each level prices its own new generator at exactly 1
 (`g₃(T) = 1` at level 3, `g_a(√T) = 1` at level 4);
* **base-change doubling:** `g_b(T) = 2·g₃(T)` and `g_b(√T) = 2·g₃(T) + 1`.

All divisibility lower bounds are discharged by `decide` through the explicit λ-adic parity
criteria `critLam8`/`critOneI16` (necessary conditions for divisibility, proved by `omega`).
-/

namespace Roots
open Z16

/-- `i = ζ₁₆⁴ = ζ₄`. -/
def i16 : Z16 := z16 ^ 4
/-- `1 + i` inside `ℤ[ζ₁₆]`. -/
def oneI16 : Z16 := 1 + z16 ^ 4

theorem i16_sq : i16 ^ 2 = -1 := by decide
theorem oneI16_eq : oneI16 = 1 + i16 := by decide

/-! ## Generic divisor-parametrised lattice on `R² = Z16 × Z16` (diagonal operators) -/

/-- Scalar action of `R` on `R²`. -/
def vsmulZ (r : Z16) (v : Z16 × Z16) : Z16 × Z16 := (r * v.1, r * v.2)
/-- Vector addition on `R²`. -/
def vaddZ (v w : Z16 × Z16) : Z16 × Z16 := (v.1 + w.1, v.2 + w.2)
/-- Diagonal operator action (componentwise multiplication by `D = (D.1, D.2)`). -/
def dapp (D v : Z16 × Z16) : Z16 × Z16 := (D.1 * v.1, D.2 * v.2)
/-- Scale a diagonal operator by a ring element. -/
def scaleD (r : Z16) (D : Z16 × Z16) : Z16 × Z16 := (r * D.1, r * D.2)

@[simp] theorem vsmulZ_fst (r v) : (vsmulZ r v).1 = r * v.1 := rfl
@[simp] theorem vsmulZ_snd (r v) : (vsmulZ r v).2 = r * v.2 := rfl
@[simp] theorem vaddZ_fst (v w) : (vaddZ v w).1 = v.1 + w.1 := rfl
@[simp] theorem vaddZ_snd (v w) : (vaddZ v w).2 = v.2 + w.2 := rfl
@[simp] theorem dapp_fst (D v) : (dapp D v).1 = D.1 * v.1 := rfl
@[simp] theorem dapp_snd (D v) : (dapp D v).2 = D.2 * v.2 := rfl

/-- Membership in the lattice `L_d = {(a,b) : d ∣ (a+b)}`. -/
def inLd (d : Z16) (v : Z16 × Z16) : Prop := d ∣ (v.1 + v.2)

theorem inLd_g1 (d : Z16) : inLd d (1, -1) := by simp [inLd]
theorem inLd_g2 (d : Z16) : inLd d (0, d) := by simp [inLd]

theorem inLd_add {d : Z16} {v w : Z16 × Z16} (hv : inLd d v) (hw : inLd d w) :
 inLd d (vaddZ v w) := by
 unfold inLd at *
 rw [show (vaddZ v w).1 + (vaddZ v w).2 = (v.1 + v.2) + (w.1 + w.2) by simp; ring]
 exact dvd_add hv hw

theorem inLd_smul {d : Z16} (r : Z16) {v : Z16 × Z16} (hv : inLd d v) :
 inLd d (vsmulZ r v) := by
 unfold inLd at *
 rw [show (vsmulZ r v).1 + (vsmulZ r v).2 = r * (v.1 + v.2) by simp; ring]
 exact Dvd.dvd.mul_left hv r

theorem dapp_vadd (D v w : Z16 × Z16) : dapp D (vaddZ v w) = vaddZ (dapp D v) (dapp D w) := by
 simp [dapp, vaddZ]; constructor <;> ring

theorem dapp_vsmul (D : Z16 × Z16) (r : Z16) (v : Z16 × Z16) :
 dapp D (vsmulZ r v) = vsmulZ r (dapp D v) := by
 simp [dapp, vsmulZ]; constructor <;> ring

theorem inLd_decompose (d : Z16) {v : Z16 × Z16} (hv : inLd d v) :
 ∃ k, v = vaddZ (vsmulZ v.1 (1, -1)) (vsmulZ k (0, d)) := by
 obtain ⟨k, hk⟩ := hv
 obtain ⟨x, y⟩ := v
 refine ⟨k, ?_⟩
 simp only [vaddZ, vsmulZ, Prod.mk.injEq]
 refine ⟨by ring, ?_⟩
 have hk' : x + y = d * k := hk
 linear_combination hk'

/-- A diagonal operator maps `L_d` into `L_d`. -/
def MapsToLd (d : Z16) (D : Z16 × Z16) : Prop := ∀ v, inLd d v → inLd d (dapp D v)

/-- **Reduction lemma.** A diagonal operator preserves `L_d` iff it preserves both
generators `(1,-1)` and `(0,d)`. -/
theorem mapsToLd_of_gens (d : Z16) (D : Z16 × Z16)
 (h1 : inLd d (dapp D (1, -1))) (h2 : inLd d (dapp D (0, d))) : MapsToLd d D := by
 intro v hv
 obtain ⟨k, hk⟩ := inLd_decompose d hv
 rw [hk, dapp_vadd, dapp_vsmul, dapp_vsmul]
 exact inLd_add (inLd_smul _ h1) (inLd_smul _ h2)

theorem mapsToLd_scale (d : Z16) (r : Z16) {D : Z16 × Z16} (h : MapsToLd d D) :
 MapsToLd d (scaleD r D) := by
 intro v hv
 have : dapp (scaleD r D) v = vsmulZ r (dapp D v) := by
 simp [dapp, scaleD, vsmulZ]; constructor <;> ring
 rw [this]
 exact inLd_smul r (h v hv)

/-! ## The grade -/

/-- `gradeLEd d D k`: the operator `λ^k · D` maps `L_d` into `L_d`. -/
def gradeLEd (d : Z16) (D : Z16 × Z16) (k : ℕ) : Prop := MapsToLd d (scaleD (lam16 ^ k) D)

theorem gradeLEd_succ {d : Z16} {D : Z16 × Z16} {k : ℕ} (h : gradeLEd d D k) :
 gradeLEd d D (k + 1) := by
 unfold gradeLEd at *
 have hsc : scaleD (lam16 ^ (k + 1)) D = scaleD lam16 (scaleD (lam16 ^ k) D) := by
 simp [scaleD]; constructor <;> ring
 rw [hsc]
 exact mapsToLd_scale d lam16 h

theorem gradeLEd_of_le {d : Z16} {D : Z16 × Z16} {a b : ℕ} (h : gradeLEd d D a)
 (hab : a ≤ b) : gradeLEd d D b := by
 induction hab with
 | refl => exact h
 | step _ ih => exact gradeLEd_succ ih

/-- If `d ∣ λ⁸` then `λ⁸·D` preserves `L_d` (everything lands in `(d)`), so the grade is
finite (`≤ 8`). -/
theorem gradeLEd_top {d : Z16} (D : Z16 × Z16) (hd : d ∣ lam16 ^ 8) : gradeLEd d D 8 := by
 intro v _
 unfold inLd
 have : (dapp (scaleD (lam16 ^ 8) D) v).1 + (dapp (scaleD (lam16 ^ 8) D) v).2
 = lam16 ^ 8 * (D.1 * v.1 + D.2 * v.2) := by simp [dapp, scaleD]; ring
 rw [this]
 exact Dvd.dvd.mul_right hd _

theorem gradeLEd_nonempty {d : Z16} (D : Z16 × Z16) (hd : d ∣ lam16 ^ 8) :
 ∃ k, gradeLEd d D k := ⟨8, gradeLEd_top D hd⟩

/-- The grade `g_d(D) = min k with λ^k·D·L_d ⊆ L_d`. -/
noncomputable def graded (d : Z16) (D : Z16 × Z16) : ℕ := sInf {k | gradeLEd d D k}

theorem graded_eq_zero {d : Z16} {D : Z16 × Z16} (h0 : gradeLEd d D 0) : graded d D = 0 :=
 Nat.le_zero.mp (Nat.sInf_le h0)

/-- If `λ^m·D` preserves `L_d` but `λ^{m-1}·D` does not (and the grade is finite), then
`g_d(D) = m`. -/
theorem graded_eq_of {d : Z16} {D : Z16 × Z16} {m : ℕ} (hfin : d ∣ lam16 ^ 8)
 (hm : gradeLEd d D m) (hpred : ¬ gradeLEd d D (m - 1)) : graded d D = m := by
 have hmem : graded d D ∈ {k | gradeLEd d D k} := Nat.sInf_mem (gradeLEd_nonempty D hfin)
 have hle : graded d D ≤ m := Nat.sInf_le hm
 rcases Nat.lt_or_ge (graded d D) m with h | h
 · exact absurd (gradeLEd_of_le hmem (by omega : graded d D ≤ m - 1)) hpred
 · omega

/-! ## λ-adic parity criteria (necessary conditions for divisibility) -/

/-- Necessary condition for divisibility by `lam8 ∼ λ²`: the two lowest λ-adic coordinates
of the element (read off mod 2 from the ζ-coordinates) vanish. -/
def critLam8 (x : Z16) : Prop :=
 (2 : ℤ) ∣ (x.a0 + x.a1 + x.a2 + x.a3 + x.a4 + x.a5 + x.a6 + x.a7) ∧
 (2 : ℤ) ∣ (x.a1 + x.a3 + x.a5 + x.a7)

/-- Necessary condition for divisibility by `oneI16 ∼ λ⁴`: the four lowest λ-adic
coordinates vanish mod 2. -/
def critOneI16 (x : Z16) : Prop :=
 critLam8 x ∧ (2 : ℤ) ∣ (x.a2 + x.a3 + x.a6 + x.a7) ∧ (2 : ℤ) ∣ (x.a3 + x.a7)

instance : DecidablePred critLam8 := fun x => by unfold critLam8; infer_instance
instance : DecidablePred critOneI16 := fun x => by unfold critOneI16 critLam8; infer_instance

/-- Coordinate literal of `lam8 = 1 - ζ₈`. -/
theorem lam8_lit : lam8 = ⟨1, 0, -1, 0, 0, 0, 0, 0⟩ := by decide
/-- Coordinate literal of `oneI16 = 1 + i = 1 + ζ₁₆⁴`. -/
theorem oneI16_lit : oneI16 = ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ := by decide

/-- `lam8 ∣ x → critLam8 x` (necessary condition; the criterion forms are λ-adic
coordinates and any `lam8`-multiple has λ-valuation `≥ 2`). -/
theorem lam8_dvd_imp_crit {x : Z16} (h : lam8 ∣ x) : critLam8 x := by
 obtain ⟨q, rfl⟩ := h
 refine ⟨?_, ?_⟩ <;> simp [lam8_lit] <;> omega

/-- `oneI16 ∣ x → critOneI16 x` (necessary condition; any `oneI16`-multiple has
λ-valuation `≥ 4`). -/
theorem oneI16_dvd_imp_crit {x : Z16} (h : oneI16 ∣ x) : critOneI16 x := by
 obtain ⟨q, rfl⟩ := h
 refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [oneI16_lit] <;> omega

/-! ## The three operators -/

/-- `T = diag(1, ζ₈)`. -/
def T16 : Z16 × Z16 := (1, z8)
/-- `√T = diag(1, ζ₁₆)`. -/
def sqrtT16 : Z16 × Z16 := (1, z16)
/-- `ζ₁₆·I = diag(ζ₁₆, ζ₁₆)`. -/
def zI16 : Z16 × Z16 := (z16, z16)

/-! ## Generator-image helpers -/

/-- The coordinate sum of `(λ^k·D)·(1,-1)` is `λ^k·(D.1 - D.2)`. -/
theorem g1_image_sum (r : Z16) (D : Z16 × Z16) :
 (dapp (scaleD r D) (1, -1)).1 + (dapp (scaleD r D) (1, -1)).2 = r * (D.1 - D.2) := by
 simp [dapp, scaleD]; ring

/-- First generator obligation, reduced to a single divisibility `d ∣ r·(D.1 - D.2)`. -/
theorem inLd_g1_image {d : Z16} (r : Z16) (D : Z16 × Z16) (hdvd : d ∣ r * (D.1 - D.2)) :
 inLd d (dapp (scaleD r D) (1, -1)) := by
 unfold inLd; rw [g1_image_sum]; exact hdvd

/-- Second generator obligation always holds: `d ∣ (λ^k·D.2)·d`. -/
theorem inLd_g2_image (d r : Z16) (D : Z16 × Z16) :
 inLd d (dapp (scaleD r D) (0, d)) := by
 unfold inLd
 rw [show (dapp (scaleD r D) (0, d)).1 + (dapp (scaleD r D) (0, d)).2 = (r * D.2) * d by
 simp [dapp, scaleD]]
 exact dvd_mul_left d (r * D.2)

/-- `(1,1) ∈ L4a` (`lam8 ∣ 2`). -/
theorem one_one_inL4a : inLd lam8 (1, 1) :=
 ⟨(z16 ^ 4 + z16 ^ 6) * ((-i16) * oneI16), by decide⟩

/-- `(1,1) ∈ L4b` (`oneI16 ∣ 2`). -/
theorem one_one_inL4b : inLd oneI16 (1, 1) :=
 ⟨(-i16) * oneI16, by decide⟩

/-! ## Key divisibility facts -/

/-- `lam8 ∣ λ²` (from `λ² = lam8·unit'`, `Z16.lam16_sq`). -/
theorem lam8_dvd_lam16_sq : lam8 ∣ lam16 ^ 2 := ⟨unit', by rw [pow_two]; exact lam16_sq⟩

/-- `oneI16 ∣ lam8²` with explicit quotient `1 - ζ₈ + ζ₈³` (the lifted Z8 ramification). -/
theorem oneI16_dvd_lam8_sq : oneI16 ∣ lam8 ^ 2 := ⟨1 - z16 ^ 2 + z16 ^ 6, by decide⟩

theorem lam8_dvd_lam16_pow8 : lam8 ∣ lam16 ^ 8 := by
 have : lam16 ^ 8 = lam16 ^ 2 * (lam16 ^ 2 * lam16 ^ 2 * lam16 ^ 2) := by ring
 rw [this]; exact Dvd.dvd.mul_right lam8_dvd_lam16_sq _

theorem oneI16_dvd_lam16_pow8 : oneI16 ∣ lam16 ^ 8 := by
 have h : lam16 ^ 8 = lam8 ^ 2 * (unit' ^ 2 * (lam16 ^ 2 * lam16 ^ 2)) := by
 have e : lam16 ^ 2 = lam8 * unit' := by rw [pow_two]; exact lam16_sq
 rw [show lam16 ^ 8 = lam16 ^ 2 * lam16 ^ 2 * (lam16 ^ 2 * lam16 ^ 2) by ring, e]; ring
 rw [h]; exact Dvd.dvd.mul_right oneI16_dvd_lam8_sq _

theorem oneI16_dvd_lam16_sq_mul_lam8 : oneI16 ∣ lam16 ^ 2 * lam8 := by
 have e : lam16 ^ 2 * lam8 = lam8 ^ 2 * unit' := by
 have : lam16 ^ 2 = lam8 * unit' := by rw [pow_two]; exact lam16_sq
 rw [this]; ring
 rw [e]; exact Dvd.dvd.mul_right oneI16_dvd_lam8_sq _

theorem oneI16_dvd_lam16_pow4 : oneI16 ∣ lam16 ^ 4 := by
 have e : lam16 ^ 4 = lam8 ^ 2 * unit' ^ 2 := by
 have : lam16 ^ 2 = lam8 * unit' := by rw [pow_two]; exact lam16_sq
 rw [show lam16 ^ 4 = lam16 ^ 2 * lam16 ^ 2 by ring, this]; ring
 rw [e]; exact Dvd.dvd.mul_right oneI16_dvd_lam8_sq _

/-! ## Target B grades — lattice `L4a` (divisor `lam8`) -/

/-- `g_a(T) = 0`: `T` is an automorphism of `L4a` (level-4 Clifford-cyclotomic). -/
theorem grade_a_T : graded lam8 T16 = 0 := by
 apply graded_eq_zero
 unfold gradeLEd
 apply mapsToLd_of_gens
 · exact inLd_g1_image (lam16 ^ 0) T16
 (by rw [show (lam16 ^ 0) * (T16.1 - T16.2) = lam8 by decide])
 · exact inLd_g2_image lam8 (lam16 ^ 0) T16

/-- `g_a(√T) = 1`: level 4 prices its own new generator `√T` at exactly 1. -/
theorem grade_a_sqrtT : graded lam8 sqrtT16 = 1 := by
 apply graded_eq_of lam8_dvd_lam16_pow8
 · unfold gradeLEd
 apply mapsToLd_of_gens
 · exact inLd_g1_image (lam16 ^ 1) sqrtT16
 (by rw [show (lam16 ^ 1) * (sqrtT16.1 - sqrtT16.2) = lam16 ^ 2 by decide]
 exact lam8_dvd_lam16_sq)
 · exact inLd_g2_image lam8 (lam16 ^ 1) sqrtT16
 · intro h
 have hmem := h (1, 1) one_one_inL4a
 have hsum : (dapp (scaleD (lam16 ^ (1 - 1)) sqrtT16) (1, 1)).1
 + (dapp (scaleD (lam16 ^ (1 - 1)) sqrtT16) (1, 1)).2 = 1 + z16 := by decide
 rw [inLd, hsum] at hmem
 exact absurd (lam8_dvd_imp_crit hmem) (by decide)

/-- `g_a(ζ₁₆·I) = 0`: scalar unit. -/
theorem grade_a_zI : graded lam8 zI16 = 0 := by
 apply graded_eq_zero
 unfold gradeLEd
 apply mapsToLd_of_gens
 · exact inLd_g1_image (lam16 ^ 0) zI16
 (by rw [show (lam16 ^ 0) * (zI16.1 - zI16.2) = 0 by decide]; exact dvd_zero _)
 · exact inLd_g2_image lam8 (lam16 ^ 0) zI16

/-! ## Target B grades — lattice `L4b` (divisor `oneI16`) -/

/-- `g_b(T) = 2`: base-change doubling, `g_b(T) = 2·g₃(T)`. -/
theorem grade_b_T : graded oneI16 T16 = 2 := by
 apply graded_eq_of oneI16_dvd_lam16_pow8
 · unfold gradeLEd
 apply mapsToLd_of_gens
 · exact inLd_g1_image (lam16 ^ 2) T16
 (by rw [show (lam16 ^ 2) * (T16.1 - T16.2) = lam16 ^ 2 * lam8 by decide]
 exact oneI16_dvd_lam16_sq_mul_lam8)
 · exact inLd_g2_image oneI16 (lam16 ^ 2) T16
 · intro h
 have hmem := h (1, 1) one_one_inL4b
 have hsum : (dapp (scaleD (lam16 ^ (2 - 1)) T16) (1, 1)).1
 + (dapp (scaleD (lam16 ^ (2 - 1)) T16) (1, 1)).2 = lam16 * (1 + z8) := by decide
 rw [inLd, hsum] at hmem
 exact absurd (oneI16_dvd_imp_crit hmem) (by decide)

/-- `g_b(√T) = 3`: base-change doubling plus one new rung, `g_b(√T) = 2·g₃(T) + 1`.
This **refutes** the original queued claim `g_b(√T) ≤ 1`. -/
theorem grade_b_sqrtT : graded oneI16 sqrtT16 = 3 := by
 apply graded_eq_of oneI16_dvd_lam16_pow8
 · unfold gradeLEd
 apply mapsToLd_of_gens
 · exact inLd_g1_image (lam16 ^ 3) sqrtT16
 (by rw [show (lam16 ^ 3) * (sqrtT16.1 - sqrtT16.2) = lam16 ^ 4 by decide]
 exact oneI16_dvd_lam16_pow4)
 · exact inLd_g2_image oneI16 (lam16 ^ 3) sqrtT16
 · intro h
 have hmem := h (1, 1) one_one_inL4b
 have hsum : (dapp (scaleD (lam16 ^ (3 - 1)) sqrtT16) (1, 1)).1
 + (dapp (scaleD (lam16 ^ (3 - 1)) sqrtT16) (1, 1)).2 = lam16 ^ 2 * (1 + z16) := by decide
 rw [inLd, hsum] at hmem
 exact absurd (oneI16_dvd_imp_crit hmem) (by decide)

/-- `g_b(ζ₁₆·I) = 0`: scalar unit. -/
theorem grade_b_zI : graded oneI16 zI16 = 0 := by
 apply graded_eq_zero
 unfold gradeLEd
 apply mapsToLd_of_gens
 · exact inLd_g1_image (lam16 ^ 0) zI16
 (by rw [show (lam16 ^ 0) * (zI16.1 - zI16.2) = 0 by decide]; exact dvd_zero _)
 · exact inLd_g2_image oneI16 (lam16 ^ 0) zI16

/-! ## Theorem B.4 — the corrected slogan -/

/-- **Theorem B.4 (the corrected level-4 table).** The full kernel-confirmed grade table
for `T`, `√T`, `ζ₁₆·I` against both lattices `L4a` (`lam8`) and `L4b` (`oneI16`). -/
theorem level4_table :
 graded lam8 T16 = 0 ∧ graded lam8 sqrtT16 = 1 ∧ graded lam8 zI16 = 0 ∧
 graded oneI16 T16 = 2 ∧ graded oneI16 sqrtT16 = 3 ∧ graded oneI16 zI16 = 0 :=
 ⟨grade_a_T, grade_a_sqrtT, grade_a_zI, grade_b_T, grade_b_sqrtT, grade_b_zI⟩

/-- **Theorem B.4 (slogan).** With `g₃(T) = 1` the level-3 grade (`Roots.grade_T`):
* level self-similarity: `g_a(√T) = 1` (level 4 prices its own new generator at 1);
* base-change doubling: `g_b(T) = 2·g₃(T)` and `g_b(√T) = 2·g₃(T) + 1`. -/
theorem level4_slogan (g3T : ℕ) (hg3 : g3T = 1) :
 graded lam8 sqrtT16 = 1 ∧
 graded oneI16 T16 = 2 * g3T ∧
 graded oneI16 sqrtT16 = 2 * g3T + 1 := by
 refine ⟨grade_a_sqrtT, ?_, ?_⟩
 · rw [hg3]; exact grade_b_T
 · rw [hg3]; exact grade_b_sqrtT

end Roots
