import Mathlib

/-!
# A self-contained computable model of the complex Barnes–Wall lattice and the
  λ-grade of diagonal monomial characters.

This file rebuilds, from scratch, the infrastructure that the R8 round was meant
to extend (the R7 files `BWn.lean` / `Zeta16.lean` / `LowerBoundAllN.lean` /
`UpperBoundAllN.lean` were **not** present in the delivered project).  Rather
than depend on absent files, we give a concrete, *kernel-computable* model and
validate it against the published R7 anchor values:

* `g(D_{x_{1⋯n}}) = 2n − 1`   (ν = 0),
* `g(D_{2·x_{1⋯n}}) = 2n − 2` (ν = 1),
* `g(D_{4·x_{1⋯n}}) = 2n − 4` (ν = 2).

All three families are reproduced exactly by the definitions below (see the
`#eval` checks at the end and the theorems in the sibling files), which fixes the
conventions and certifies that the model is the intended one.

## The mathematics

* Work in `R = ℤ[ζ₈] = ℤ[x]/(x⁴+1)` (`Z8` below); an element is the integer
  coefficient vector `(a,b,c,d)` of `1, ζ, ζ², ζ³`.
* `μ = 1 + i` (with `i = ζ²`) is the prime above 2 in `ℤ[i] ⊂ R`; it is the
  scaling element of the recursive complex Barnes–Wall construction.
* `λ = 1 − ζ` is the totally ramified prime above 2 in `R`, with `λ⁴ ∼ 2`,
  `v_λ(μ) = 2`.  Grades are measured in `λ`-units.
* The Barnes–Wall lattice `BW_n ⊆ R^{2ⁿ}` is the `R`-span of the columns of
  `Bₙ = ⊗ⁿ [[1,0],[1,μ]]`.  Equivalently (the recursion used by `inBWb`):
  a vector `v = (v₀, v₁)` (each half of length `2^{n-1}`) lies in `BW_n` iff
  `v₀ ∈ BW_{n-1}` and `v₁ − v₀ ∈ μ · BW_{n-1}`, with `BW_0 = R`.
* A diagonal character `D_e = diag(ζ₈^{e(b)})_{b ∈ 𝔽₂ⁿ}` has **grade**
  `g(D_e) = ` the least `j` such that `λ^j · D_e · BW_n ⊆ BW_n`.  Because
  `BW_n` is an `R`-module and multiplication by `λ` preserves it, this `j` is
  attained and `mapsIn` below is monotone in `j`, so the least such `j` is the
  genuine grade.  `mapsIn n j D = true` ⇔ `g(D) ≤ j`.
-/

namespace BWModel

/-- Element of `ℤ[ζ₈] = ℤ[x]/(x⁴+1)`: the integer coefficients of `1, ζ, ζ², ζ³`. -/
structure Z8 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

namespace Z8

def zero : Z8 := ⟨0, 0, 0, 0⟩
def one : Z8 := ⟨1, 0, 0, 0⟩
def add (x y : Z8) : Z8 := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def sub (x y : Z8) : Z8 := ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩
def smul (k : Int) (x : Z8) : Z8 := ⟨k * x.a, k * x.b, k * x.c, k * x.d⟩

/-- Multiplication by `ζ`: uses `ζ⁴ = -1`, i.e. `(a,b,c,d) ↦ (-d, a, b, c)`. -/
def mulZeta (x : Z8) : Z8 := ⟨-x.d, x.a, x.b, x.c⟩

/-- Ring multiplication in `ℤ[ζ₈]`. -/
def mul (x y : Z8) : Z8 :=
  let t0 := smul y.a x
  let x1 := mulZeta x
  let t1 := smul y.b x1
  let x2 := mulZeta x1
  let t2 := smul y.c x2
  let x3 := mulZeta x2
  let t3 := smul y.d x3
  add (add t0 t1) (add t2 t3)

/-- `ζ₈^k`. -/
def zpow (k : Nat) : Z8 := (mulZeta)^[k % 8] one

def zeta : Z8 := zpow 1
/-- The imaginary unit `i = ζ²`. -/
def iU : Z8 := zpow 2
/-- The complex Barnes–Wall scaling element `μ = 1 + i`. -/
def mu : Z8 := add one iU
/-- `μ̄ = 1 − i`, with `μ · μ̄ = 2`. -/
def muBar : Z8 := sub one iU
/-- The ramified prime `λ = 1 − ζ` (grades are measured in `λ`-units). -/
def lam : Z8 := sub one zeta

/-- `λ^k`. -/
def lamPow (k : Nat) : Z8 := (fun y => mul lam y)^[k] one

instance : Add Z8 := ⟨add⟩
instance : Sub Z8 := ⟨sub⟩
instance : Mul Z8 := ⟨mul⟩

/-- Divide by `μ = 1 + i` when possible.  Since `μ · μ̄ = 2`, an element `x`
is divisible by `μ` iff `x · μ̄` has all-even coefficients, with quotient
`x · μ̄ / 2`. -/
def divMu? (x : Z8) : Option Z8 :=
  let y := mul x muBar
  if y.a % 2 == 0 ∧ y.b % 2 == 0 ∧ y.c % 2 == 0 ∧ y.d % 2 == 0 then
    some ⟨y.a / 2, y.b / 2, y.c / 2, y.d / 2⟩
  else none

end Z8

open Z8

/-- Membership in `BW_n` for a length-`2ⁿ` vector, via the recursion
`v = (v₀, v₁) ∈ BW_n ↔ v₀ ∈ BW_{n-1} ∧ (v₁ − v₀) ∈ μ · BW_{n-1}`, `BW_0 = R`. -/
def inBWb : Nat → List Z8 → Bool
  | 0, _ => true
  | (n + 1), v =>
      let h := 2 ^ n
      let v0 := v.take h
      let v1 := v.drop h
      let diff := List.zipWith (· - ·) v1 v0
      let qs := diff.map Z8.divMu?
      if qs.all Option.isSome then inBWb n v0 && inBWb n (qs.filterMap id) else false

/-- The columns of `Bₙ = ⊗ⁿ [[1,0],[1,μ]]`, an `R`-generating set of `BW_n`. -/
def bcols : Nat → List (List Z8)
  | 0 => [[Z8.one]]
  | (n + 1) =>
      let cs := bcols n
      let h := 2 ^ n
      let left := cs.map (fun c => c ++ c)
      let right := cs.map (fun c => List.replicate h Z8.zero ++ c.map (fun e => Z8.mul Z8.mu e))
      left ++ right

/-- Diagonal of the character `D_e` for `e = Σ (coef, S)`, i.e. phase polynomial
`e(b) = Σ_t coefₜ · ∏_{i ∈ Sₜ} b_i` (mod 8), with `D_e(b) = ζ₈^{e(b)}`. -/
def deVec (n : Nat) (terms : List (Nat × List Nat)) : List Z8 :=
  (List.range (2 ^ n)).map (fun idx =>
    let e := terms.foldl
      (fun acc t => acc + t.1 * (t.2.foldl (fun a i => a * ((idx / 2 ^ i) % 2)) 1)) 0
    Z8.zpow (e % 8))

/-- Single monomial `D_{x_S}` with coefficient `coef`. -/
def deMon (n coef : Nat) (S : List Nat) : List Z8 := deVec n [(coef, S)]

/-- Apply a diagonal `D` to a column (entrywise product). -/
def applyD (D col : List Z8) : List Z8 := List.zipWith Z8.mul D col

/-- Scale a vector by `λ^k`. -/
def scaleVec (k : Nat) (col : List Z8) : List Z8 := col.map (fun e => Z8.mul (Z8.lamPow k) e)

/-- `mapsIn n j D = true` ⇔ `λ^j · D · BW_n ⊆ BW_n` ⇔ `g(D) ≤ j`. -/
def mapsIn (n j : Nat) (D : List Z8) : Bool :=
  (bcols n).all (fun col => inBWb n (scaleVec j (applyD D col)))

/-- The grade computed by bounded search; for `bound > g(D)` this is the genuine
grade (least `j` with `mapsIn`). -/
def gradeUpTo (n bound : Nat) (D : List Z8) : Nat :=
  ((List.range (bound + 1)).find? (fun j => mapsIn n j D)).getD bound

/-- The grade of a diagonal character, with a search bound generous enough
(`2n + 2 > 2n − 1`) for all single-monomial characters. -/
def grade (n : Nat) (D : List Z8) : Nat := gradeUpTo n (2 * n + 2) D

section Sanity
-- Convention-fixing checks: these reproduce the R7 anchors exactly.
/-- info: 1 -/
#guard_msgs in #eval grade 1 (deMon 1 1 [0])           -- 2·1−1
/-- info: 3 -/
#guard_msgs in #eval grade 2 (deMon 2 1 [0, 1])        -- 2·2−1
/-- info: 5 -/
#guard_msgs in #eval grade 3 (deMon 3 1 [0, 1, 2])     -- 2·3−1
/-- info: 2 -/
#guard_msgs in #eval grade 2 (deMon 2 2 [0, 1])        -- ν=1: 2·2−2
/-- info: 2 -/
#guard_msgs in #eval grade 3 (deMon 3 4 [0, 1, 2])     -- ν=2: 2·3−4
end Sanity

end BWModel
