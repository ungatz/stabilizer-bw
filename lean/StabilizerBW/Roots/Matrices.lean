import StabilizerBW.Roots.Core

/-!
# 2×2 matrices over `R = ℤ[ζ₈]` and the √Π dictionary (Priority 1.1)

We use a concrete `Mat2` of four `Z8` entries with explicit multiplication and
action on vectors `Z8 × Z8`. All entries here are integral; the matrices that
"morally" carry a `1/2` or `1/√2` factor are represented by their integer
multiples (`2·V`, `√2·H`) so that every identity below is an honest equation in
`R` and is checked by `decide`.

Dictionary verified:
* `(2V)² = 4X`,
* `2V = (√2H)·S·(√2H)`,
* `S·(2V)·S = (1+i)·(√2H)` (i.e. `S V S = ζ₈ H`).
-/

namespace Roots

/-- A 2×2 matrix over `R = ℤ[ζ₈]`. -/
structure Mat2 where
 m00 : Z8
 m01 : Z8
 m10 : Z8
 m11 : Z8
deriving DecidableEq, Repr

namespace Mat2

@[ext] theorem ext' {M N : Mat2} (h00 : M.m00 = N.m00) (h01 : M.m01 = N.m01)
 (h10 : M.m10 = N.m10) (h11 : M.m11 = N.m11) : M = N := by
 cases M; cases N; simp_all

/-- Matrix multiplication. -/
def mul (M N : Mat2) : Mat2 :=
 ⟨M.m00*N.m00 + M.m01*N.m10, M.m00*N.m01 + M.m01*N.m11,
 M.m10*N.m00 + M.m11*N.m10, M.m10*N.m01 + M.m11*N.m11⟩

instance : Mul Mat2 := ⟨mul⟩
@[simp] theorem mul_m00 (M N : Mat2) : (M*N).m00 = M.m00*N.m00 + M.m01*N.m10 := rfl
@[simp] theorem mul_m01 (M N : Mat2) : (M*N).m01 = M.m00*N.m01 + M.m01*N.m11 := rfl
@[simp] theorem mul_m10 (M N : Mat2) : (M*N).m10 = M.m10*N.m00 + M.m11*N.m10 := rfl
@[simp] theorem mul_m11 (M N : Mat2) : (M*N).m11 = M.m10*N.m01 + M.m11*N.m11 := rfl

/-- Scalar multiple of a matrix. -/
def smul (r : Z8) (M : Mat2) : Mat2 := ⟨r*M.m00, r*M.m01, r*M.m10, r*M.m11⟩

/-- Action on a column vector `(x, y)`. -/
def mulVec (M : Mat2) (v : Z8 × Z8) : Z8 × Z8 :=
 (M.m00*v.1 + M.m01*v.2, M.m10*v.1 + M.m11*v.2)

@[simp] theorem mulVec_fst (M : Mat2) (v : Z8 × Z8) :
 (M.mulVec v).1 = M.m00*v.1 + M.m01*v.2 := rfl
@[simp] theorem mulVec_snd (M : Mat2) (v : Z8 × Z8) :
 (M.mulVec v).2 = M.m10*v.1 + M.m11*v.2 := rfl

/-! ## Named matrices (integral representatives) -/

/-- Identity. -/
def II : Mat2 := ⟨1,0,0,1⟩
/-- Pauli `X` (swap on `1+1`). -/
def X : Mat2 := ⟨0,1,1,0⟩
/-- `2V = (1+i)I + (1-i)X`. -/
def twoV : Mat2 := ⟨Z8.oneI, 1 - Z8.iu, 1 - Z8.iu, Z8.oneI⟩
/-- `√2·H = [[1,1],[1,-1]]`. -/
def sqrt2H : Mat2 := ⟨1,1,1,-1⟩
/-- Phase gate `S = diag(1, i)`. -/
def S : Mat2 := ⟨1,0,0,Z8.iu⟩
/-- `T = diag(1, ζ₈)`. -/
def T : Mat2 := ⟨1,0,0,Z8.zeta⟩

/-! ## Priority 1.1 — the dictionary identities -/

/-- `(2V)² = 4X`, i.e. `V² = X`. -/
theorem twoV_sq : twoV * twoV = smul 4 X := by decide

/-- `2V = (√2H)·S·(√2H)`. -/
theorem twoV_eq_HSH : twoV = sqrt2H * S * sqrt2H := by decide

/-- `S·(2V)·S = (1+i)·(√2H)`, i.e. `S V S = ζ₈ H` (Euler/nondegeneracy identity). -/
theorem S_twoV_S : S * twoV * S = smul Z8.oneI sqrt2H := by decide

/-- `(√2H)² = 2I`, i.e. `H² = I`. -/
theorem sqrt2H_sq : sqrt2H * sqrt2H = smul 2 II := by decide

/-- `S² = diag(1,-1) = Z`. -/
theorem S_sq : S * S = ⟨1,0,0,-1⟩ := by decide

/-- `X² = I`. -/
theorem X_sq : X * X = II := by decide

end Mat2
end Roots
