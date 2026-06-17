import Mathlib

/-!
# Priority 5 — level raising: `ℤ[ζ₁₆]` and `λ₁₆² ∼ λ₈`

We build the next ring in the cyclotomic tower,

 `R' = ℤ[ζ₁₆] = ℤ[x]/(x⁸+1)`,

written `a₀ + a₁ζ + ⋯ + a₇ζ⁷` with `ζ = ζ₁₆`, `ζ⁸ = -1`, and prove the
*one-ramified-step-per-square-root* identity at this level:

 `(1 - ζ₁₆)² = (1 - ζ₈) · unit'`, `ζ₈ = ζ₁₆²`,

with `unit' = -ζ + ζ² - ζ³ + ζ⁴ - ζ⁵ + ζ⁶ - ζ⁷` a genuine unit (inverse
`ζ + ζ² + ⋯ + ζ⁷` exhibited). This realises `λ_{m+1}² ∼ λ_m`: each cyclotomic level
is a single ramified quadratic step, the arithmetic meaning of "one square root".

The level-4 two-lattice grade table over `ℤ[ζ₁₆]` (which refutes the naive grade-halving
slogan) is settled by kernel in `Roots.Level4`.
-/

namespace Roots

/-- An element of `R' = ℤ[ζ₁₆] = ℤ[x]/(x⁸+1)`, written `a₀ + a₁ζ + ⋯ + a₇ζ⁷`. -/
structure Z16 where
 a0 : ℤ
 a1 : ℤ
 a2 : ℤ
 a3 : ℤ
 a4 : ℤ
 a5 : ℤ
 a6 : ℤ
 a7 : ℤ
deriving DecidableEq, Repr

namespace Z16

@[ext] theorem ext' {x y : Z16} (h0 : x.a0 = y.a0) (h1 : x.a1 = y.a1) (h2 : x.a2 = y.a2)
 (h3 : x.a3 = y.a3) (h4 : x.a4 = y.a4) (h5 : x.a5 = y.a5) (h6 : x.a6 = y.a6)
 (h7 : x.a7 = y.a7) : x = y := by
 cases x; cases y; simp_all

instance : Zero Z16 := ⟨⟨0,0,0,0,0,0,0,0⟩⟩
instance : One Z16 := ⟨1,0,0,0,0,0,0,0⟩
instance : Add Z16 := ⟨fun x y =>
 ⟨x.a0+y.a0,x.a1+y.a1,x.a2+y.a2,x.a3+y.a3,x.a4+y.a4,x.a5+y.a5,x.a6+y.a6,x.a7+y.a7⟩⟩
instance : Neg Z16 := ⟨fun x => ⟨-x.a0,-x.a1,-x.a2,-x.a3,-x.a4,-x.a5,-x.a6,-x.a7⟩⟩
instance : Sub Z16 := ⟨fun x y =>
 ⟨x.a0-y.a0,x.a1-y.a1,x.a2-y.a2,x.a3-y.a3,x.a4-y.a4,x.a5-y.a5,x.a6-y.a6,x.a7-y.a7⟩⟩
/-- Multiplication modulo `x⁸+1` (so `ζ⁸ = -1`). -/
instance : Mul Z16 := ⟨fun x y =>
 ⟨ x.a0*y.a0 - (x.a1*y.a7+x.a2*y.a6+x.a3*y.a5+x.a4*y.a4+x.a5*y.a3+x.a6*y.a2+x.a7*y.a1),
 x.a0*y.a1+x.a1*y.a0 - (x.a2*y.a7+x.a3*y.a6+x.a4*y.a5+x.a5*y.a4+x.a6*y.a3+x.a7*y.a2),
 x.a0*y.a2+x.a1*y.a1+x.a2*y.a0 - (x.a3*y.a7+x.a4*y.a6+x.a5*y.a5+x.a6*y.a4+x.a7*y.a3),
 x.a0*y.a3+x.a1*y.a2+x.a2*y.a1+x.a3*y.a0 - (x.a4*y.a7+x.a5*y.a6+x.a6*y.a5+x.a7*y.a4),
 x.a0*y.a4+x.a1*y.a3+x.a2*y.a2+x.a3*y.a1+x.a4*y.a0 - (x.a5*y.a7+x.a6*y.a6+x.a7*y.a5),
 x.a0*y.a5+x.a1*y.a4+x.a2*y.a3+x.a3*y.a2+x.a4*y.a1+x.a5*y.a0 - (x.a6*y.a7+x.a7*y.a6),
 x.a0*y.a6+x.a1*y.a5+x.a2*y.a4+x.a3*y.a3+x.a4*y.a2+x.a5*y.a1+x.a6*y.a0 - (x.a7*y.a7),
 x.a0*y.a7+x.a1*y.a6+x.a2*y.a5+x.a3*y.a4+x.a4*y.a3+x.a5*y.a2+x.a6*y.a1+x.a7*y.a0 ⟩⟩

@[simp] theorem zero_a0 : (0:Z16).a0 = 0 := rfl
@[simp] theorem zero_a1 : (0:Z16).a1 = 0 := rfl
@[simp] theorem zero_a2 : (0:Z16).a2 = 0 := rfl
@[simp] theorem zero_a3 : (0:Z16).a3 = 0 := rfl
@[simp] theorem zero_a4 : (0:Z16).a4 = 0 := rfl
@[simp] theorem zero_a5 : (0:Z16).a5 = 0 := rfl
@[simp] theorem zero_a6 : (0:Z16).a6 = 0 := rfl
@[simp] theorem zero_a7 : (0:Z16).a7 = 0 := rfl
@[simp] theorem add_a0 (x y:Z16) : (x+y).a0 = x.a0+y.a0 := rfl
@[simp] theorem add_a1 (x y:Z16) : (x+y).a1 = x.a1+y.a1 := rfl
@[simp] theorem add_a2 (x y:Z16) : (x+y).a2 = x.a2+y.a2 := rfl
@[simp] theorem add_a3 (x y:Z16) : (x+y).a3 = x.a3+y.a3 := rfl
@[simp] theorem add_a4 (x y:Z16) : (x+y).a4 = x.a4+y.a4 := rfl
@[simp] theorem add_a5 (x y:Z16) : (x+y).a5 = x.a5+y.a5 := rfl
@[simp] theorem add_a6 (x y:Z16) : (x+y).a6 = x.a6+y.a6 := rfl
@[simp] theorem add_a7 (x y:Z16) : (x+y).a7 = x.a7+y.a7 := rfl
@[simp] theorem neg_a0 (x:Z16) : (-x).a0 = -x.a0 := rfl
@[simp] theorem neg_a1 (x:Z16) : (-x).a1 = -x.a1 := rfl
@[simp] theorem neg_a2 (x:Z16) : (-x).a2 = -x.a2 := rfl
@[simp] theorem neg_a3 (x:Z16) : (-x).a3 = -x.a3 := rfl
@[simp] theorem neg_a4 (x:Z16) : (-x).a4 = -x.a4 := rfl
@[simp] theorem neg_a5 (x:Z16) : (-x).a5 = -x.a5 := rfl
@[simp] theorem neg_a6 (x:Z16) : (-x).a6 = -x.a6 := rfl
@[simp] theorem neg_a7 (x:Z16) : (-x).a7 = -x.a7 := rfl
@[simp] theorem sub_a0 (x y:Z16) : (x-y).a0 = x.a0-y.a0 := rfl
@[simp] theorem sub_a1 (x y:Z16) : (x-y).a1 = x.a1-y.a1 := rfl
@[simp] theorem sub_a2 (x y:Z16) : (x-y).a2 = x.a2-y.a2 := rfl
@[simp] theorem sub_a3 (x y:Z16) : (x-y).a3 = x.a3-y.a3 := rfl
@[simp] theorem sub_a4 (x y:Z16) : (x-y).a4 = x.a4-y.a4 := rfl
@[simp] theorem sub_a5 (x y:Z16) : (x-y).a5 = x.a5-y.a5 := rfl
@[simp] theorem sub_a6 (x y:Z16) : (x-y).a6 = x.a6-y.a6 := rfl
@[simp] theorem sub_a7 (x y:Z16) : (x-y).a7 = x.a7-y.a7 := rfl
@[simp] theorem one_a0 : (1:Z16).a0 = 1 := rfl
@[simp] theorem one_a1 : (1:Z16).a1 = 0 := rfl
@[simp] theorem one_a2 : (1:Z16).a2 = 0 := rfl
@[simp] theorem one_a3 : (1:Z16).a3 = 0 := rfl
@[simp] theorem one_a4 : (1:Z16).a4 = 0 := rfl
@[simp] theorem one_a5 : (1:Z16).a5 = 0 := rfl
@[simp] theorem one_a6 : (1:Z16).a6 = 0 := rfl
@[simp] theorem one_a7 : (1:Z16).a7 = 0 := rfl
@[simp] theorem mul_a0 (x y:Z16) : (x*y).a0 =
 x.a0*y.a0 - (x.a1*y.a7+x.a2*y.a6+x.a3*y.a5+x.a4*y.a4+x.a5*y.a3+x.a6*y.a2+x.a7*y.a1) := rfl
@[simp] theorem mul_a1 (x y:Z16) : (x*y).a1 =
 x.a0*y.a1+x.a1*y.a0 - (x.a2*y.a7+x.a3*y.a6+x.a4*y.a5+x.a5*y.a4+x.a6*y.a3+x.a7*y.a2) := rfl
@[simp] theorem mul_a2 (x y:Z16) : (x*y).a2 =
 x.a0*y.a2+x.a1*y.a1+x.a2*y.a0 - (x.a3*y.a7+x.a4*y.a6+x.a5*y.a5+x.a6*y.a4+x.a7*y.a3) := rfl
@[simp] theorem mul_a3 (x y:Z16) : (x*y).a3 =
 x.a0*y.a3+x.a1*y.a2+x.a2*y.a1+x.a3*y.a0 - (x.a4*y.a7+x.a5*y.a6+x.a6*y.a5+x.a7*y.a4) := rfl
@[simp] theorem mul_a4 (x y:Z16) : (x*y).a4 =
 x.a0*y.a4+x.a1*y.a3+x.a2*y.a2+x.a3*y.a1+x.a4*y.a0 - (x.a5*y.a7+x.a6*y.a6+x.a7*y.a5) := rfl
@[simp] theorem mul_a5 (x y:Z16) : (x*y).a5 =
 x.a0*y.a5+x.a1*y.a4+x.a2*y.a3+x.a3*y.a2+x.a4*y.a1+x.a5*y.a0 - (x.a6*y.a7+x.a7*y.a6) := rfl
@[simp] theorem mul_a6 (x y:Z16) : (x*y).a6 =
 x.a0*y.a6+x.a1*y.a5+x.a2*y.a4+x.a3*y.a3+x.a4*y.a2+x.a5*y.a1+x.a6*y.a0 - (x.a7*y.a7) := rfl
@[simp] theorem mul_a7 (x y:Z16) : (x*y).a7 =
 x.a0*y.a7+x.a1*y.a6+x.a2*y.a5+x.a3*y.a4+x.a4*y.a3+x.a5*y.a2+x.a6*y.a1+x.a7*y.a0 := rfl

instance commRing : CommRing Z16 where
 add_assoc := by intros; ext <;> simp <;> ring
 zero_add := by intros; ext <;> simp
 add_zero := by intros; ext <;> simp
 add_comm := by intros; ext <;> simp <;> ring
 neg_add_cancel := by intros; ext <;> simp
 mul_assoc := by intros; ext <;> simp <;> ring
 one_mul := by intros; ext <;> simp
 mul_one := by intros; ext <;> simp
 left_distrib := by intros; ext <;> simp <;> ring
 right_distrib := by intros; ext <;> simp <;> ring
 mul_comm := by intros; ext <;> simp <;> ring
 sub_eq_add_neg := by intros; ext <;> simp <;> ring
 zero_mul := by intros; ext <;> simp
 mul_zero := by intros; ext <;> simp
 nsmul := nsmulRec
 zsmul := zsmulRec

/-- `ζ₁₆`. -/
def z16 : Z16 := ⟨0,1,0,0,0,0,0,0⟩
/-- `ζ₈ = ζ₁₆²`. -/
def z8 : Z16 := ⟨0,0,1,0,0,0,0,0⟩
/-- `λ₁₆ = 1 - ζ₁₆`. -/
def lam16 : Z16 := (1 : Z16) - z16
/-- `λ₈ = 1 - ζ₈`. -/
def lam8 : Z16 := (1 : Z16) - z8
/-- The level-raising unit `u' = -ζ + ζ² - ζ³ + ζ⁴ - ζ⁵ + ζ⁶ - ζ⁷`. -/
def unit' : Z16 := ⟨0,-1,1,-1,1,-1,1,-1⟩
/-- Its inverse `ζ + ζ² + ⋯ + ζ⁷`. -/
def unitInv : Z16 := ⟨0,1,1,1,1,1,1,1⟩

/-- `ζ₁₆² = ζ₈`: the tower `ℤ[ζ₈] ⊂ ℤ[ζ₁₆]`. -/
theorem z16_sq : z16 * z16 = z8 := by decide

/-- **Priority 5: `(1-ζ₁₆)² = (1-ζ₈)·u'`** — one ramified quadratic step per √. -/
theorem lam16_sq : lam16 * lam16 = lam8 * unit' := by decide

/-- `u'` is a unit, with explicit inverse. -/
theorem unit'_mul_unitInv : unit' * unitInv = 1 := by decide

/-- Restatement: `λ₁₆² = λ₈ · v` for a unit `v` (i.e. `λ₁₆² ∼ λ₈`). -/
theorem lam16_sq_assoc : ∃ v vinv : Z16, v * vinv = 1 ∧ lam16 * lam16 = lam8 * v :=
 ⟨unit', unitInv, unit'_mul_unitInv, lam16_sq⟩

end Z16
end Roots
