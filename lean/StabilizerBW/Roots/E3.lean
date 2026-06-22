import StabilizerBW.Roots.Grades

/-!
# Target A — the (E3) selection truth table (Carette–Heunen–Kaarsgaard–Sabry)

Setting (all over `ℤ[ζ₈][1/2]`, handled via integral doubled representatives):
`P± = (I ± X)/2`, and the four unitary square roots of `X` are

  `V(α,β) = α·P₊ + β·P₋`,   `α ∈ {1,-1}`, `β ∈ {i,-i}`,

with doubled representative `2·V(α,β) = (α+β)I + (α-β)X = twoVab α β`.  The four
concrete roots `twoR1..twoR4` of `Roots.Grades` are `twoVab (±1) (±i)`.

For a primitive eighth root `ω` (`ω⁴ = -1`) put `S_ω = diag(1, ω²)` (`= Sdiag (ω²)`).
The CHKS nondegeneracy axiom is

  (E3):  `V ∘ S_ω ∘ V = ω² • (S_ω ∘ V ∘ S_ω)`.

Clearing the `1/2`'s in `V = (1/2)·2V` turns (E3) into the **exact integral identity**
over `ℤ[ζ₈]`

  `(2V)·S_ω·(2V) = (2·ω²) • (S_ω·(2V)·S_ω)`        (`E3holds root ω`),

so every clause below is checked by plain `decide`.

## The truth table (`E3_truth_table`)

Over the four primitive roots `ω ∈ {ζ, ζ³, ζ⁵, ζ⁷}` (so `ω² ∈ {i, -i}`):

| root          | holds for ω with… | forced ω² |
|---------------|-------------------|-----------|
| `R1 = V(1,i)`   | never           | (degenerate `1` at ω²=i) |
| `R2 = V(1,-i)`  | never           | (degenerate `1` at ω²=-i) |
| `R3 = V(-1,i)`  | ω² = i          | `i`       |
| `R4 = V(-1,-i)` | ω² = -i         | `-i`      |

i.e. **(E3) holds for exactly the two pairs `(R3, ω²=i)` and `(R4, ω²=-i)`.**

## ⚠ Discrepancy with the hand computation

The hand note claimed the *conjugate* root `V(1,-i) = R2` satisfies (E3) with `ω² = -i`.
The kernel refutes this: `R2 = V(1,-i)` satisfies (E3) for **no** primitive `ω`
(`E3_R2_none`); at `ω² = -i` it forces the degenerate scalar `1` (`R2_degenerate`).
The root that actually satisfies (E3) with `ω² = -i` is `R4 = V(-1,-i) = -V(1,i)`, the
**negated textbook root** (`E3_satisfied_R4`).  The hand note's other two clauses are
confirmed: `-V(1,-i) = V(-1,i) = R3` satisfies with `ω² = +i` (`E3_satisfied_R3`), and the
textbook root `V(1,i) = R1` forces the degenerate `ω² = 1` (`R1_degenerate`).

Clean selection slogan (`E3_selection_alpha`):
`V(α,β)` admits a primitive-`ω` solution **iff `α = -1`**, and then the forced `ω² = β`.
-/

namespace Roots
open Z8 Mat2

/-- `S_ω = diag(1, ω²)`; the argument is the value `ω²`. -/
def Sdiag (w2 : Z8) : Mat2 := ⟨1, 0, 0, w2⟩

/-- Doubled representative of `V(α,β) = α·P₊ + β·P₋`, i.e. `2V = (α+β)I + (α-β)X`. -/
def twoVab (al be : Z8) : Mat2 := ⟨al + be, al - be, al - be, al + be⟩

/-- The (E3) identity in doubled (integral) form, parametrised by the primitive root `ω`:
`(2V)·S_ω·(2V) = (2ω²)·(S_ω·(2V)·S_ω)`. -/
def E3holds (root : Mat2) (w : Z8) : Prop :=
  root * Sdiag (w ^ 2) * root
    = Mat2.smul (2 * w ^ 2) (Sdiag (w ^ 2) * root * Sdiag (w ^ 2))

instance (root : Mat2) (w : Z8) : Decidable (E3holds root w) := by
  unfold E3holds; infer_instance

/-- The (E3) identity forced with an *arbitrary* scalar `c` in place of `ω²`
(the "what scalar would the equation force" diagnosis): `(2V)·S·(2V) = (2c)·(S·(2V)·S)`
with `S = diag(1, w2)`. -/
def E3forces (root : Mat2) (w2 c : Z8) : Prop :=
  root * Sdiag w2 * root = Mat2.smul (2 * c) (Sdiag w2 * root * Sdiag w2)

instance (root : Mat2) (w2 c : Z8) : Decidable (E3forces root w2 c) := by
  unfold E3forces; infer_instance

/-! ## The `V²=X` parametrisation -/

/-
**Parametrisation.** `V(α,β)² = X` (in doubled form `(2V)² = 4X`) iff `α² = 1` and
`β² = -1`.
-/
theorem twoVab_sq (al be : Z8) :
    twoVab al be * twoVab al be = Mat2.smul 4 X ↔ al ^ 2 = 1 ∧ be ^ 2 = -1 := by
  have cancel : ∀ x y : Z8, 2 * x = 2 * y → x = y := by
    intro x y h
    have hz : (2 : Z8) * (x - y) = 0 := by linear_combination h
    have hxy : x - y = 0 := by
      have h2 : (2 : Z8) = ⟨2, 0, 0, 0⟩ := rfl
      have ha := congr_arg Z8.a hz; have hb := congr_arg Z8.b hz
      have hc := congr_arg Z8.c hz; have hd := congr_arg Z8.d hz
      apply Z8.ext' <;>
        simp [h2, Z8.mul_a, Z8.mul_b, Z8.mul_c, Z8.mul_d] at ha hb hc hd ⊢ <;> omega
    linear_combination hxy
  constructor
  · intro h
    have e00 : 2 * (al ^ 2 + be ^ 2) = 0 := by
      have := congr_arg Mat2.m00 h
      simp [twoVab, Mat2.smul, X] at this
      linear_combination this
    have e01 : 2 * (al ^ 2 - be ^ 2) = 2 * 2 := by
      have := congr_arg Mat2.m01 h
      simp [twoVab, Mat2.smul, X] at this
      linear_combination this
    have hsum : al ^ 2 + be ^ 2 = 0 := cancel _ _ (by linear_combination e00)
    have hdiff : al ^ 2 - be ^ 2 = 2 := cancel _ _ e01
    exact ⟨cancel _ _ (by linear_combination hsum + hdiff),
           cancel _ _ (by linear_combination hsum - hdiff)⟩
  · rintro ⟨ha, hb⟩
    apply Mat2.ext' <;> simp [twoVab, Mat2.smul, X]
    · linear_combination 2 * ha + 2 * hb
    · linear_combination 2 * ha - 2 * hb
    · linear_combination 2 * ha - 2 * hb
    · linear_combination 2 * ha + 2 * hb

/-- The four named roots are the four sign choices of `twoVab`. -/
theorem twoR1_eq : twoR1 = twoVab 1 iu := by decide
theorem twoR2_eq : twoR2 = twoVab 1 (-iu) := by decide
theorem twoR3_eq : twoR3 = twoVab (-1) iu := by decide
theorem twoR4_eq : twoR4 = twoVab (-1) (-iu) := by decide

/-- All four are genuine roots of `X` (sanity, restates `twoR*_sq`). -/
theorem twoVab_roots_of_X :
    (∀ al ∈ ([1, -1] : List Z8), ∀ be ∈ ([iu, -iu] : List Z8),
      twoVab al be * twoVab al be = Mat2.smul 4 X) := by decide

/-! ## The primitive eighth roots `ω` (`ω⁴ = -1`) -/

/-- The four primitive eighth roots `ζ, ζ³, ζ⁵, ζ⁷`. -/
def primOmega : List Z8 := [zeta, zeta ^ 3, zeta ^ 5, zeta ^ 7]

theorem primOmega_pow4 : ∀ w ∈ primOmega, w ^ 4 = -1 := by decide

/-- For every primitive `ω`, `ω² ∈ {i, -i}` (so `ω²` is itself primitive, `≠ 1`). -/
theorem primOmega_sq : ∀ w ∈ primOmega, w ^ 2 = iu ∨ w ^ 2 = -iu := by decide

theorem primOmega_sq_ne_one : ∀ w ∈ primOmega, w ^ 2 ≠ 1 := by decide

/-! ## Theorem A.1 — the truth table -/

/-- **Theorem A.1 (the (E3) truth table).** Over the four primitive roots
`ω ∈ {ζ, ζ³, ζ⁵, ζ⁷}`:
* `R1 = V(1,i)` and `R2 = V(1,-i)` satisfy (E3) for **no** `ω`;
* `R3 = V(-1,i)` satisfies (E3) iff `ω² = i`;
* `R4 = V(-1,-i)` satisfies (E3) iff `ω² = -i`. -/
theorem E3_truth_table :
    ∀ w ∈ primOmega,
      (¬ E3holds twoR1 w) ∧ (¬ E3holds twoR2 w) ∧
      (E3holds twoR3 w ↔ w ^ 2 = iu) ∧ (E3holds twoR4 w ↔ w ^ 2 = -iu) := by
  decide

/-! ## Theorem A.2 — selection -/

/-- **A.2(i).** `R3 = V(-1,i)` admits a primitive solution, forcing `ω² = i`. -/
theorem E3_satisfied_R3 : ∃ w ∈ primOmega, E3holds twoR3 w ∧ w ^ 2 = iu := by decide

/-- **A.2(i).** `R4 = V(-1,-i)` admits a primitive solution, forcing `ω² = -i`. -/
theorem E3_satisfied_R4 : ∃ w ∈ primOmega, E3holds twoR4 w ∧ w ^ 2 = -iu := by decide

/-- **A.2(i).** Every primitive solution of `R3` forces `ω² = i`. -/
theorem E3_R3_forces : ∀ w ∈ primOmega, E3holds twoR3 w → w ^ 2 = iu := by decide

/-- **A.2(i).** Every primitive solution of `R4` forces `ω² = -i`. -/
theorem E3_R4_forces : ∀ w ∈ primOmega, E3holds twoR4 w → w ^ 2 = -iu := by decide

/-- **A.2(ii).** The textbook root `R1 = V(1,i)` admits no primitive solution. -/
theorem E3_R1_none : ∀ w ∈ primOmega, ¬ E3holds twoR1 w := by decide

/-- **A.2(ii).** The conjugate root `R2 = V(1,-i)` admits no primitive solution.
(This *refutes* the hand claim that `V(1,-i)` works with `ω² = -i`.) -/
theorem E3_R2_none : ∀ w ∈ primOmega, ¬ E3holds twoR2 w := by decide

/-- **A.2(ii) degenerate diagnosis.** For the textbook root `R1 = V(1,i)` with the
natural `S_ω` (`ω² = i = β`), the equation forces the scalar `1` — i.e. `ω² = 1`, excluded
by primitivity (`primOmega_sq_ne_one`). -/
theorem R1_degenerate : E3forces twoR1 iu 1 := by decide

/-- **A.2(ii) degenerate diagnosis.** For the conjugate root `R2 = V(1,-i)` with the
natural `S_ω` (`ω² = -i = β`), the equation forces the scalar `1`, again excluded. -/
theorem R2_degenerate : E3forces twoR2 (-iu) 1 := by decide

/-- The forced scalar in the degenerate cases is genuinely `1` and **not** the primitive
value `ω²`: at `ω² = i` the root `R1` does not satisfy (E3) (`E3forces ... iu` fails), it
only satisfies the degenerate `E3forces ... 1`. -/
theorem R1_not_primitive : ¬ E3forces twoR1 iu iu := by decide
theorem R2_not_primitive : ¬ E3forces twoR2 (-iu) (-iu) := by decide

/-- **A.2 clean slogan.** Packaged over `α ∈ {1,-1}`, `β ∈ {i,-i}` and the primitive
roots `ω`: `V(α,β)` admits a primitive-`ω` solution of (E3) **iff `α = -1`**, and in that
case the forced value is `ω² = β`. -/
theorem E3_selection_alpha :
    ∀ al ∈ ([1, -1] : List Z8), ∀ be ∈ ([iu, -iu] : List Z8),
      ((∃ w ∈ primOmega, E3holds (twoVab al be) w) ↔ al = -1)
      ∧ (∀ w ∈ primOmega, E3holds (twoVab al be) w → w ^ 2 = be) := by
  decide

/-! ## Theorem A.3 — lattice form -/

/-
**A.3.** For the satisfying pair `(R3, ω²=i)`, the inner half-integral operator
`S_ω·(2V)·S_ω = 2·(S∘V∘S)` preserves the level-3 lattice `L₃`.
-/
theorem A3_R3_HalfMapsToL : HalfMapsToL (Sdiag iu * twoR3 * Sdiag iu) := by
  intro v hv; rw [ inL_iff ] at hv; unfold halfAction; simp +decide [ Z8.dvdOneI, Z8.half ] at *;
  simp +decide [ inL_iff, Sdiag, twoR3 ] at *;
  obtain ⟨ k₁, hk₁ ⟩ := hv.1; obtain ⟨ k₂, hk₂ ⟩ := hv.2; simp_all +decide [ Z8.dvdOneI ] ;
  omega

/-
**A.3.** For the satisfying pair `(R4, ω²=-i)`, the inner half-integral operator
`S_ω·(2V)·S_ω` preserves `L₃`.
-/
theorem A3_R4_HalfMapsToL : HalfMapsToL (Sdiag (-iu) * twoR4 * Sdiag (-iu)) := by
  intro v hv
  simp_all +decide [ inL_iff, halfAction ];
  simp_all +decide [ Z8.dvdOneI, Z8.half, Z8.iu, Sdiag, twoR4 ];
  omega

/-- **A.3.** Both sides of (E3) are equal *as matrices* (hence as maps) for the satisfying
pairs; the left side is the right side scaled by the global unit-multiple `2ω²`. -/
theorem A3_R3_sides_equal :
    twoR3 * Sdiag iu * twoR3
      = Mat2.smul (2 * iu) (Sdiag iu * twoR3 * Sdiag iu) := by decide

theorem A3_R4_sides_equal :
    twoR4 * Sdiag (-iu) * twoR4
      = Mat2.smul (2 * (-iu)) (Sdiag (-iu) * twoR4 * Sdiag (-iu)) := by decide

end Roots