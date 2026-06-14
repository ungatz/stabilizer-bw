/-
# PauliLogic/Syntax.lean

Signed Pauli words over the symplectic F₂ representation. A direct Lean
port of `haskell/src/PauliLogic.hs`'s `Pauli` datatype and arithmetic.

Reference: the development `def:av-pl-syntax` (§sec:av-pauli-logic).

This file defines:
- `Pauli n`: a signed n-qubit Pauli word as (sign, xs, zs). The two F₂
 components are represented as `Fin n → Bool`, which is mathematically the
 same data as `Vector Bool n` but gives clean `Finset.univ` sums for the
 symplectic form and the i-exponent bookkeeping (the Array-backed `Vector`
 does not reduce under `decide`, so a function representation is used).
- `pauliI n`: the identity word +I
- `pX`, `pZ`, `pY`: single-qubit letters at a chosen position
- `Pauli.commutes`: the symplectic-form commutator detection
- `gExp`: the single-qubit i-exponent table (the Haskell `gExp`)
- `Pauli.mul`: product of two commuting Hermitian Pauli words, with the
 commutation precondition carried as a hypothesis.

## Sign convention

A signed Hermitian Pauli word is `(-1)^sign · i^{#Y} · ⊗_j X^{x_j} Z^{z_j}`,
where `#Y` is the number of qubits carrying a `Y` (i.e. `x_j = z_j = true`).
The product of two such words multiplies the bit-vectors by XOR and accrues a
global phase `i^{E}` with

 `E(p,q) = #Y(p) + #Y(q) − #Y(p·q) + 2·⟨z_p, x_q⟩` (over ℤ),

where `⟨z_p, x_q⟩ = Σ_j (z_p)_j (x_q)_j`. When `p` and `q` commute, `E` is
even and the product is Hermitian with sign bit `(E/2) mod 2`, encoded here as
`decide (E % 4 = 2)`. This `E`-formula is the Aaronson–Gottesman row
multiplication phase; `gExp` is its per-qubit table (see `gExp_phase` for the
equivalence with the Haskell sum-of-`gExp` form).

-/

import Mathlib

open scoped BigOperators

namespace PauliLogic

/-- A signed n-qubit Pauli word in the symplectic representation:
 `sign × x-bits × z-bits`, with the two F₂ⁿ components as `Fin n → Bool`. -/
structure Pauli (n : ℕ) where
 sign : Bool
 xs : Fin n → Bool
 zs : Fin n → Bool

namespace Pauli

@[ext] theorem ext {n : ℕ} {p q : Pauli n}
 (hs : p.sign = q.sign) (hx : p.xs = q.xs) (hz : p.zs = q.zs) : p = q := by
 cases p; cases q; cases hs; cases hx; cases hz; rfl

end Pauli

/-- The identity word `+I^⊗n = (false, 0, 0)`. -/
def pauliI (n : ℕ) : Pauli n :=
 ⟨false, fun _ => false, fun _ => false⟩

/-- Single-qubit `X` at position `q`. -/
def pX (n : ℕ) (q : Fin n) : Pauli n :=
 ⟨false, fun i => decide (i = q), fun _ => false⟩

/-- Single-qubit `Z` at position `q`. -/
def pZ (n : ℕ) (q : Fin n) : Pauli n :=
 ⟨false, fun _ => false, fun i => decide (i = q)⟩

/-- Single-qubit `Y` at position `q`. -/
def pY (n : ℕ) (q : Fin n) : Pauli n :=
 ⟨false, fun i => decide (i = q), fun i => decide (i = q)⟩

/-- `⟨z_p, x_q⟩ = Σ_j (z_p)_j (x_q)_j` over ℕ. -/
def crossZX {n : ℕ} (p q : Pauli n) : ℕ := ∑ j, (p.zs j && q.xs j).toNat

/-- `#Y(p)`: number of qubits where `p` carries a `Y` (both x and z set). -/
def numY {n : ℕ} (p : Pauli n) : ℕ := ∑ j, (p.xs j && p.zs j).toNat

/-- x-component of the product `p·q` (XOR of x-bits). -/
def mulXs {n : ℕ} (p q : Pauli n) : Fin n → Bool := fun j => xor (p.xs j) (q.xs j)

/-- z-component of the product `p·q` (XOR of z-bits). -/
def mulZs {n : ℕ} (p q : Pauli n) : Fin n → Bool := fun j => xor (p.zs j) (q.zs j)

/-- `#Y(p·q)`. -/
def numYmul {n : ℕ} (p q : Pauli n) : ℕ := ∑ j, (mulXs p q j && mulZs p q j).toNat

/-- The integer i-exponent `E(p,q)` of the product `p·q`. -/
def phaseZ {n : ℕ} (p q : Pauli n) : ℤ :=
 (numY p : ℤ) + (numY q : ℤ) - (numYmul p q : ℤ) + 2 * (crossZX p q : ℤ)

/-- Two Pauli words commute iff the symplectic form `⟨z_p,x_q⟩ + ⟨z_q,x_p⟩`
 is even over F₂. -/
def Pauli.commutes {n : ℕ} (p q : Pauli n) : Bool :=
 (crossZX p q + crossZX q p) % 2 == 0

/-- Product of two commuting Hermitian Pauli words (the MUL rule). The
 commutation precondition guarantees `phaseZ` is even, so the result is
 Hermitian with sign bit `decide (phaseZ p q % 4 = 2)`. -/
def Pauli.mul {n : ℕ} (p q : Pauli n) (_h : p.commutes q = true) : Pauli n :=
 { sign := xor (xor p.sign q.sign) (decide (phaseZ p q % 4 = 2))
 xs := mulXs p q
 zs := mulZs p q }

/-- Negation: flip the global sign. -/
def Pauli.negate {n : ℕ} (p : Pauli n) : Pauli n := { p with sign := !p.sign }

/-- The per-qubit i-exponent table (mod 4) for the product of two single-qubit
 Hermitian Pauli letters, encoded as `(x,z)` bits: I=(F,F), X=(T,F), Z=(F,T),
 Y=(T,T). This is the Haskell reference's `gExp`. -/
def gExp : (Bool × Bool) → (Bool × Bool) → Fin 4 := fun a b =>
 match a, b with
 | (false, false), _ => 0
 | _, (false, false) => 0
 | (true, false), (true, false) => 0 -- X X
 | (true, true), (true, true) => 0 -- Y Y
 | (false, true), (false, true) => 0 -- Z Z
 | (true, false), (true, true) => 1 -- X Y
 | (true, true), (false, true) => 1 -- Y Z
 | (false, true), (true, false) => 1 -- Z X
 | (true, true), (true, false) => 3 -- Y X
 | (false, true), (true, true) => 3 -- Z Y
 | (true, false), (false, true) => 3 -- X Z

/-- The Haskell sum-of-`gExp` i-exponent. -/
def iexpSum {n : ℕ} (p q : Pauli n) : ℕ :=
 ∑ j, (gExp (p.xs j, p.zs j) (q.xs j, q.zs j)).val

/-! ## Basic arithmetic facts -/

@[simp] theorem crossZX_self {n : ℕ} (p : Pauli n) : crossZX p p = numY p := by
 unfold crossZX numY
 exact Finset.sum_congr rfl (fun j _ => by rw [Bool.and_comm])

@[simp] theorem numYmul_self {n : ℕ} (p : Pauli n) : numYmul p p = 0 := by
 unfold numYmul mulXs mulZs
 apply Finset.sum_eq_zero
 intro j _
 simp

theorem numYmul_comm {n : ℕ} (p q : Pauli n) : numYmul p q = numYmul q p := by
 unfold numYmul mulXs mulZs
 refine Finset.sum_congr rfl (fun j _ => ?_)
 rw [Bool.xor_comm (p.xs j) (q.xs j), Bool.xor_comm (p.zs j) (q.zs j)]

@[simp] theorem phaseZ_self {n : ℕ} (p : Pauli n) : phaseZ p p = 4 * (numY p : ℤ) := by
 unfold phaseZ
 rw [crossZX_self, numYmul_self]
 push_cast
 ring

/-! ## Required theorems -/

/-- Commutation is symmetric. -/
theorem Pauli.commutes_symm {n : ℕ} (p q : Pauli n) : p.commutes q = q.commutes p := by
 unfold Pauli.commutes
 rw [Nat.add_comm]

/-- A Hermitian Pauli word squares to the identity. -/
theorem Pauli.mul_self {n : ℕ} (p : Pauli n) (h : p.commutes p = true) :
 Pauli.mul p p h = pauliI n := by
 apply Pauli.ext
 · show xor (xor p.sign p.sign) (decide (phaseZ p p % 4 = 2)) = false
 have : ¬ (phaseZ p p % 4 = 2) := by rw [phaseZ_self]; omega
 rw [decide_eq_false this]
 simp
 · funext j; simp [Pauli.mul, pauliI, mulXs]
 · funext j; simp [Pauli.mul, pauliI, mulZs]

/-- `crossZX p q` and `crossZX q p` have the same parity exactly when `p,q`
 commute (this is the definition unfolded). -/
theorem crossZX_add_even_of_commutes {n : ℕ} {p q : Pauli n}
 (h : p.commutes q = true) : (crossZX p q + crossZX q p) % 2 = 0 := by
 unfold Pauli.commutes at h
 simpa using h

/-
For commuting words, `phaseZ p q ≡ phaseZ q p (mod 4)`.
-/
theorem phaseZ_comm_mod4 {n : ℕ} {p q : Pauli n} (h : p.commutes q = true) :
 phaseZ p q % 4 = phaseZ q p % 4 := by
 unfold Pauli.commutes at h;
 unfold phaseZ;
 norm_num [ numYmul_comm ];
 grind

/-- MUL is commutative for commuting operands. -/
theorem Pauli.mul_comm {n : ℕ} (p q : Pauli n)
 (h : p.commutes q = true) (h' : q.commutes p = true) :
 Pauli.mul p q h = Pauli.mul q p h' := by
 apply Pauli.ext
 · show xor (xor p.sign q.sign) (decide (phaseZ p q % 4 = 2))
 = xor (xor q.sign p.sign) (decide (phaseZ q p % 4 = 2))
 rw [phaseZ_comm_mod4 h, Bool.xor_comm p.sign q.sign]
 · funext j; simp [Pauli.mul, mulXs, Bool.xor_comm]
 · funext j; simp [Pauli.mul, mulZs, Bool.xor_comm]

/-
For commuting words, `phaseZ` is even.
-/
theorem phaseZ_even {n : ℕ} {p q : Pauli n} (h : p.commutes q = true) :
 phaseZ p q % 2 = 0 := by
 unfold phaseZ;
 have h_numYmul : (numYmul p q) % 2 = (numY p + crossZX q p + crossZX p q + numY q) % 2 := by
 have h_numYmul : ∀ j, ((xor (p.xs j) (q.xs j)) && (xor (p.zs j) (q.zs j))).toNat % 2 = ((p.xs j && p.zs j).toNat + (p.xs j && q.zs j).toNat + (q.xs j && p.zs j).toNat + (q.xs j && q.zs j).toNat) % 2 := by
 intro j; cases p.xs j <;> cases q.xs j <;> cases p.zs j <;> cases q.zs j <;> trivial;
 simp +decide [ Finset.sum_nat_mod, numYmul, numY, crossZX ];
 simp +decide [ ← Finset.sum_add_distrib, h_numYmul, mulXs, mulZs ];
 simp +decide [ ← Finset.sum_nat_mod, Bool.and_comm ];
 grind +suggestions

/-
The product of two operators each commuting with `r` commutes with `r`.
-/
theorem commutes_mul_left {n : ℕ} {p q r : Pauli n}
 (hpq : p.commutes q = true)
 (hpr : p.commutes r = true) (hqr : q.commutes r = true) :
 (Pauli.mul p q hpq).commutes r = true := by
 unfold Pauli.commutes at *;
 unfold crossZX; simp +decide [ *, Nat.add_mod ] ;
 simp +decide [ Pauli.mul ] at *;
 simp +decide [ mulZs, mulXs, Nat.add_mod ] at *;
 -- By definition of `crossZX`, we can expand the sums.
 have h_expand : ∀ (u v w : Fin n → Bool), (∑ j, ((u j ^^ v j) && w j).toNat) % 2 = ((∑ j, (u j && w j).toNat) + (∑ j, (v j && w j).toNat)) % 2 ∧ (∑ j, (w j && (u j ^^ v j)).toNat) % 2 = ((∑ j, (w j && u j).toNat) + (∑ j, (w j && v j).toNat)) % 2 := by
 intros u v w; exact ⟨by
 rw [ ← Finset.sum_add_distrib ] ; exact Nat.ModEq.sum fun i _ => by cases u i <;> cases v i <;> cases w i <;> rfl;, by
 rw [ ← Finset.sum_add_distrib ] ; exact Nat.ModEq.sum fun i _ => by cases w i <;> cases u i <;> cases v i <;> rfl;⟩;
 simp_all +decide [ crossZX ];
 omega

/-- The product of two operators each commuted-with by `p` is commuted-with
 by `p`. -/
theorem commutes_mul_right {n : ℕ} {p q r : Pauli n}
 (hqr : q.commutes r = true)
 (hpq : p.commutes q = true) (hpr : p.commutes r = true) :
 p.commutes (Pauli.mul q r hqr) = true := by
 rw [Pauli.commutes_symm]
 exact commutes_mul_left hqr (by rw [Pauli.commutes_symm]; exact hpq)
 (by rw [Pauli.commutes_symm]; exact hpr)

/-
The phase cocycle identity (associativity of the i-exponent), the
 arithmetic heart of `mul_assoc`.
-/
theorem phaseZ_cocycle {n : ℕ} (p q r : Pauli n)
 (hpq : p.commutes q = true) (hqr : q.commutes r = true) :
 (phaseZ p q + phaseZ (Pauli.mul p q hpq) r) % 4
 = (phaseZ q r + phaseZ p (Pauli.mul q r hqr)) % 4 := by
 unfold phaseZ;
 norm_num [ Pauli.mul ];
 unfold numY numYmul crossZX mulXs mulZs; norm_num [ Finset.sum_add_distrib, two_mul ] ;
 norm_num [ ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib ];
 refine' Int.ModEq.sum _;
 intro x hx; cases p.xs x <;> cases p.zs x <;> cases q.xs x <;> cases q.zs x <;> cases r.xs x <;> cases r.zs x <;> trivial;

/-
MUL is associative for pairwise commuting operands.
-/
theorem Pauli.mul_assoc {n : ℕ} (p q r : Pauli n)
 (hpq : p.commutes q = true) (hpr : p.commutes r = true) (hqr : q.commutes r = true) :
 Pauli.mul (Pauli.mul p q hpq) r (commutes_mul_left hpq hpr hqr)
 = Pauli.mul p (Pauli.mul q r hqr) (commutes_mul_right hqr hpq hpr) := by
 refine' Pauli.ext _ _ _;
 · -- By definition of `phaseZ`, we know that `phaseZ p q % 2 = 0` and `phaseZ q r % 2 = 0`.
 have h_even : phaseZ p q % 2 = 0 ∧ phaseZ q r % 2 = 0 ∧ phaseZ (Pauli.mul p q hpq) r % 2 = 0 ∧ phaseZ p (Pauli.mul q r hqr) % 2 = 0 := by
 exact ⟨ phaseZ_even hpq, phaseZ_even hqr, phaseZ_even ( commutes_mul_left hpq hpr hqr ), phaseZ_even ( commutes_mul_right hqr hpq hpr ) ⟩;
 have := phaseZ_cocycle p q r hpq hqr;
 unfold Pauli.mul at *;
 grind;
 · funext j; simp only [Pauli.mul, mulXs, Bool.xor_assoc]
 · funext j; simp only [Pauli.mul, mulZs, Bool.xor_assoc]

end PauliLogic