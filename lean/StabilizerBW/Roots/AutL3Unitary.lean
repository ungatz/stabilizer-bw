import Mathlib

/-!
# Unitary `Aut(L₃)` converse at one qubit

This file formalises the *unitary* version of the Kliuchnikov–Schönnenbeck 2024
converse at the single–qubit level:

> every **unitary** integral automorphism of the level-3 Barnes–Wall lattice
> `L₃` is a phased Clifford.

We work over the ring `R = ℤ[ζ₈]`, modelled concretely as the structure `Z8`
of quadruples `(a,b,c,d)` standing for `a + b·ζ + c·ζ² + d·ζ³` with `ζ⁴ = -1`.
Here `ζ = ζ₈` is a primitive `8`-th root of unity, `i = ζ²`, `√2 = ζ - ζ³`.

`L₃ = {(a,b) ∈ R² : (1+i) ∣ a + b}`.

## Main results

* `det_root_of_unity` (foundational round): a unitary integral matrix has `det ∈ ⟨ζ₈⟩`.
* `finite_integral_su2_aut_L3` (finiteness of integral SU(2)): the integral special-unitary
  lattice-automorphism group is finite, of cardinality `≤ 24`
  (in fact exactly `16`).
* `aut_L3_unitary_is_phased_clifford` (unitary converse): every unitary integral
  automorphism of `L₃` is a phase `ζ₈^k` times an (integral) Clifford.

## A note on the count — this is NOT the standard K–S theorem

The **integral-over-`ℤ[ζ₈]`** unitary `Aut(L₃)` is the **monomial Clifford
subgroup** of order `16` (projective image `8`).  This is a *strict subgroup* of
the full single-qubit Clifford group that K–S 2024 enumerate over
`ℤ[1/√2, i]` (order `24`, projective).  The reason is **integrality**: a unitary
matrix over `ℤ[ζ₈]` is forced to be *monomial* with root-of-unity entries
(`unitary_is_monomial`), because each Hermitian row norm is a sum of integer
squares equal to `1`.  The Hadamard gate `(1/√2)·[[1,1],[1,-1]]` has entries
`±1/√2`, which are not algebraic integers and in particular do **not** lie in
`ℤ[ζ₈]`; so Hadamard — the unique non-monomial Clifford generator — is excluded,
and the integral count collapses from `24` to `16` (projective `8`).

This is therefore **not** "discharging K–S".  It is best read as a **companion
theorem to `grade1_n3_stratum_infinite`** (the integral Cliff+ T2
falsification): both are integral-over-`ℤ[ζ₈]` restrictions of standard
answers, and both surface a single feature excluded by integrality over
`ℤ[ζ₈]` — the Hadamard gate here, the infinite real-unit ladder (`1+√2`) there.
The standard K–S theorem (over `ℤ[1/√2, ζ₈]`, where Hadamard *is* in the ring)
is a separate statement; its single-qubit form is delivered in the companion
file `StabilizerBW.Roots.AutL3HalfSqrt2` as
`aut_L3_unitary_over_Z_halfsqrt2_is_full_clifford`.

Consequently the integral unitary automorphism group has order `64`
(`8` phases `×` the monomial Clifford subgroup of order `8`... here the
*linear* monomial Clifford group `cliffFinset` has order `32`), its projective
image has order `8`, and the integral special-unitary (`det = 1`) part has
order `16` — **not** `24` (`finite_integral_su2_aut_L3`).  The unitary converse
itself remains **true**: every unitary integral `L₃`-automorphism is a phased
Clifford (a monomial one).
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace AutL3

/-! ## The ring `R = ℤ[ζ₈]` -/

/-- `R = ℤ[ζ₈]`: a quadruple `(a,b,c,d)` standing for `a + bζ + cζ² + dζ³`,
with `ζ⁴ = -1`. -/
structure Z8 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

namespace Z8

instance : Zero Z8 := ⟨⟨0,0,0,0⟩⟩
instance : One Z8 := ⟨⟨1,0,0,0⟩⟩
instance : Add Z8 := ⟨fun x y => ⟨x.a+y.a, x.b+y.b, x.c+y.c, x.d+y.d⟩⟩
instance : Neg Z8 := ⟨fun x => ⟨-x.a,-x.b,-x.c,-x.d⟩⟩
instance : Mul Z8 := ⟨fun x y =>
  ⟨x.a*y.a - (x.b*y.d + x.c*y.c + x.d*y.b),
   x.a*y.b + x.b*y.a - (x.c*y.d + x.d*y.c),
   x.a*y.c + x.b*y.b + x.c*y.a - x.d*y.d,
   x.a*y.d + x.b*y.c + x.c*y.b + x.d*y.a⟩⟩

@[ext] theorem ext {x y : Z8} (ha:x.a=y.a)(hb:x.b=y.b)(hc:x.c=y.c)(hd:x.d=y.d):x=y:=by
  cases x; cases y; simp_all

@[simp] theorem add_a (x y:Z8):(x+y).a=x.a+y.a:=rfl
@[simp] theorem add_b (x y:Z8):(x+y).b=x.b+y.b:=rfl
@[simp] theorem add_c (x y:Z8):(x+y).c=x.c+y.c:=rfl
@[simp] theorem add_d (x y:Z8):(x+y).d=x.d+y.d:=rfl
@[simp] theorem neg_a (x:Z8):(-x).a=-x.a:=rfl
@[simp] theorem neg_b (x:Z8):(-x).b=-x.b:=rfl
@[simp] theorem neg_c (x:Z8):(-x).c=-x.c:=rfl
@[simp] theorem neg_d (x:Z8):(-x).d=-x.d:=rfl
@[simp] theorem zero_a:(0:Z8).a=0:=rfl
@[simp] theorem zero_b:(0:Z8).b=0:=rfl
@[simp] theorem zero_c:(0:Z8).c=0:=rfl
@[simp] theorem zero_d:(0:Z8).d=0:=rfl
@[simp] theorem one_a:(1:Z8).a=1:=rfl
@[simp] theorem one_b:(1:Z8).b=0:=rfl
@[simp] theorem one_c:(1:Z8).c=0:=rfl
@[simp] theorem one_d:(1:Z8).d=0:=rfl
@[simp] theorem mul_a (x y:Z8):(x*y).a=x.a*y.a - (x.b*y.d + x.c*y.c + x.d*y.b):=rfl
@[simp] theorem mul_b (x y:Z8):(x*y).b=x.a*y.b + x.b*y.a - (x.c*y.d + x.d*y.c):=rfl
@[simp] theorem mul_c (x y:Z8):(x*y).c=x.a*y.c + x.b*y.b + x.c*y.a - x.d*y.d:=rfl
@[simp] theorem mul_d (x y:Z8):(x*y).d=x.a*y.d + x.b*y.c + x.c*y.b + x.d*y.a:=rfl

instance : CommRing Z8 where
  add_assoc := by intro a b c; ext <;> simp <;> ring
  zero_add := by intro a; ext <;> simp
  add_zero := by intro a; ext <;> simp
  add_comm := by intro a b; ext <;> simp <;> ring
  left_distrib := by intro a b c; ext <;> simp <;> ring
  right_distrib := by intro a b c; ext <;> simp <;> ring
  zero_mul := by intro a; ext <;> simp
  mul_zero := by intro a; ext <;> simp
  mul_assoc := by intro a b c; ext <;> simp <;> ring
  one_mul := by intro a; ext <;> simp
  mul_one := by intro a; ext <;> simp
  mul_comm := by intro a b; ext <;> simp <;> ring
  neg_add_cancel := by intro a; ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- `ζ = ζ₈`, a primitive `8`-th root of unity. -/
def zeta : Z8 := ⟨0,1,0,0⟩
/-- `i = ζ²`. -/
def imv : Z8 := ⟨0,0,1,0⟩
/-- `1 + i = 1 + ζ²`. -/
def onePlusI : Z8 := ⟨1,0,1,0⟩
/-- `1 - i = 1 - ζ²`. -/
def oneMinusI : Z8 := ⟨1,0,-1,0⟩

/-- Complex conjugation on `ℤ[ζ₈]`: `ζ ↦ ζ⁻¹ = -ζ³`, i.e.
`(a,b,c,d) ↦ (a,-d,-c,-b)`. -/
def conj (x : Z8) : Z8 := ⟨x.a, -x.d, -x.c, -x.b⟩

@[simp] theorem conj_a (x:Z8):(conj x).a = x.a := rfl
@[simp] theorem conj_b (x:Z8):(conj x).b = -x.d := rfl
@[simp] theorem conj_c (x:Z8):(conj x).c = -x.c := rfl
@[simp] theorem conj_d (x:Z8):(conj x).d = -x.b := rfl

/-- The integer "squared modulus" `|x|² = a²+b²+c²+d²` (the trace form). -/
def nsq (x : Z8) : Int := x.a^2 + x.b^2 + x.c^2 + x.d^2

theorem nsq_nonneg (x : Z8) : 0 ≤ nsq x := by
  unfold nsq; positivity

theorem conj_zero : conj 0 = 0 := by ext <;> simp [conj]

theorem conj_add (x y : Z8) : conj (x+y) = conj x + conj y := by
  ext <;> simp [conj] <;> ring

theorem conj_mul (x y : Z8) : conj (x*y) = conj x * conj y := by
  ext <;> simp [conj] <;> ring

theorem conj_one : conj 1 = 1 := by ext <;> simp [conj]

theorem conj_sub (x y : Z8) : conj (x-y) = conj x - conj y := by
  ext <;> simp [conj, sub_eq_add_neg] <;> ring

@[simp] theorem conj_eq_zero {x : Z8} : conj x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h1 := congrArg Z8.a h
    have h2 := congrArg Z8.b h
    have h3 := congrArg Z8.c h
    have h4 := congrArg Z8.d h
    simp only [conj_a, conj_b, conj_c, conj_d, zero_a, zero_b, zero_c, zero_d] at h1 h2 h3 h4
    ext
    · simpa using h1
    · simp only [zero_b]; omega
    · simp only [zero_c]; omega
    · simp only [zero_d]; omega
  · rintro rfl; exact conj_zero

/-- The first ("real") coordinate of `x · conj x` is `|x|²`. -/
theorem coord_a_mul_conj (x : Z8) : (x * conj x).a = nsq x := by
  simp [conj, nsq]; ring

/-- `x = 0` iff `|x|² = 0`. -/
theorem nsq_eq_zero {x : Z8} : nsq x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have : x.a^2 = 0 ∧ x.b^2 = 0 ∧ x.c^2 = 0 ∧ x.d^2 = 0 := by
      unfold nsq at h
      refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg x.a, sq_nonneg x.b, sq_nonneg x.c, sq_nonneg x.d]
    ext <;> simp_all
  · rintro rfl; simp [nsq]

/-- The eight roots of unity `ζ^0,…,ζ^7` as the only solutions of `|x|² = 1`. -/
theorem nsq_eq_one_root {x : Z8} (h : nsq x = 1) : ∃ k : Fin 8, x = zeta ^ (k:ℕ) := by
  revert x;
  -- By definition of nsq, we know that x.a^2 + x.b^2 + x.c^2 + x.d^2 = 1.
  intro x hx
  have h_bounds : x.a^2 ≤ 1 ∧ x.b^2 ≤ 1 ∧ x.c^2 ≤ 1 ∧ x.d^2 ≤ 1 := by
    unfold Z8.nsq at hx; exact ⟨ by linarith [ sq_nonneg x.a, sq_nonneg x.b, sq_nonneg x.c, sq_nonneg x.d ], by linarith [ sq_nonneg x.a, sq_nonneg x.b, sq_nonneg x.c, sq_nonneg x.d ], by linarith [ sq_nonneg x.a, sq_nonneg x.b, sq_nonneg x.c, sq_nonneg x.d ], by linarith [ sq_nonneg x.a, sq_nonneg x.b, sq_nonneg x.c, sq_nonneg x.d ] ⟩ ;
  obtain ⟨ha, hb, hc, hd⟩ : x.a ∈ Set.Icc (-1 : ℤ) 1 ∧ x.b ∈ Set.Icc (-1 : ℤ) 1 ∧ x.c ∈ Set.Icc (-1 : ℤ) 1 ∧ x.d ∈ Set.Icc (-1 : ℤ) 1 := by
    exact ⟨ ⟨ by nlinarith only [ h_bounds.1 ], by nlinarith only [ h_bounds.1 ] ⟩, ⟨ by nlinarith only [ h_bounds.2.1 ], by nlinarith only [ h_bounds.2.1 ] ⟩, ⟨ by nlinarith only [ h_bounds.2.2.1 ], by nlinarith only [ h_bounds.2.2.1 ] ⟩, ⟨ by nlinarith only [ h_bounds.2.2.2 ], by nlinarith only [ h_bounds.2.2.2 ] ⟩ ⟩;
  rcases ha with ⟨ ha₁, ha₂ ⟩ ; rcases hb with ⟨ hb₁, hb₂ ⟩ ; rcases hc with ⟨ hc₁, hc₂ ⟩ ; rcases hd with ⟨ hd₁, hd₂ ⟩ ; interval_cases _ : x.a <;> interval_cases _ : x.b <;> interval_cases _ : x.c <;> interval_cases _ : x.d <;> simp_all +decide only [nsq] ;
  all_goals rw [ show x = ⟨ x.a, x.b, x.c, x.d ⟩ from rfl ] ; simp +decide [ * ]

/-- For a root of unity, `x · conj x = 1`. -/
theorem mul_conj_root {x : Z8} (h : nsq x = 1) : x * conj x = 1 := by
  obtain ⟨k, rfl⟩ := nsq_eq_one_root h
  fin_cases k <;> decide

/-! ## Divisibility by `1+i` -/

/-- `(1+i)·(1-i) = 2`. -/
theorem onePlusI_mul_oneMinusI : onePlusI * oneMinusI = (2 : Z8) := by decide

/-- Forward criterion for divisibility by `1+i`: if `(1+i) ∣ x` then every
coordinate of `x·(1-i)` is even. -/
theorem dvd_onePlusI_coords {x : Z8} (h : onePlusI ∣ x) :
    2 ∣ (x*oneMinusI).a ∧ 2 ∣ (x*oneMinusI).b ∧ 2 ∣ (x*oneMinusI).c ∧ 2 ∣ (x*oneMinusI).d := by
  obtain ⟨q, rfl⟩ := h
  have : onePlusI * q * oneMinusI = (2:Z8) * q := by
    rw [mul_right_comm, onePlusI_mul_oneMinusI]
  rw [this]
  refine ⟨⟨q.a, ?_⟩, ⟨q.b, ?_⟩, ⟨q.c, ?_⟩, ⟨q.d, ?_⟩⟩ <;>
    · simp [show (2:Z8) = ⟨2,0,0,0⟩ from rfl]

/-- A decidable predicate equivalent to divisibility by `1+i`: every coordinate of
`z·(1-i)` is even. -/
def DvdOnePlusI (z : Z8) : Prop :=
  2 ∣ (z*oneMinusI).a ∧ 2 ∣ (z*oneMinusI).b ∧ 2 ∣ (z*oneMinusI).c ∧ 2 ∣ (z*oneMinusI).d

instance : DecidablePred DvdOnePlusI := fun z => by unfold DvdOnePlusI; infer_instance

/-- Multiplying a `Z8` element by `2` doubles every coordinate; hence `2` is
not a zero divisor for the purposes of this argument. -/
theorem two_mul_eq_zero {d : Z8} (h : d * (2:Z8) = 0) : d = 0 := by
  have ha := congrArg Z8.a h
  have hb := congrArg Z8.b h
  have hc := congrArg Z8.c h
  have hd := congrArg Z8.d h
  simp only [mul_a, mul_b, mul_c, mul_d, show (2:Z8).a = 2 from rfl,
    show (2:Z8).b = 0 from rfl, show (2:Z8).c = 0 from rfl, show (2:Z8).d = 0 from rfl,
    zero_a, zero_b, zero_c, zero_d] at ha hb hc hd
  ext <;> simp only [zero_a, zero_b, zero_c, zero_d] <;> omega

/-- The coordinate criterion characterises divisibility by `1+i`. -/
theorem dvdOnePlusI_iff (z : Z8) : onePlusI ∣ z ↔ DvdOnePlusI z := by
  constructor
  · intro h; exact dvd_onePlusI_coords h
  · rintro ⟨⟨wa, ha⟩, ⟨wb, hb⟩, ⟨wc, hc⟩, ⟨wd, hd⟩⟩
    set w : Z8 := ⟨wa, wb, wc, wd⟩ with hw
    refine ⟨w, ?_⟩
    -- `z*(1-i) = 2*w = (1+i)*w*(1-i)`
    have h2 : z * oneMinusI = (2 : Z8) * w := by
      ext <;> simp only [hw, mul_a, mul_b, mul_c, mul_d, show (2:Z8).a = 2 from rfl,
        show (2:Z8).b = 0 from rfl, show (2:Z8).c = 0 from rfl, show (2:Z8).d = 0 from rfl] <;>
        simp_all
    have h3 : z * oneMinusI = (onePlusI * w) * oneMinusI := by
      rw [h2, mul_right_comm, onePlusI_mul_oneMinusI]
    -- cancel `oneMinusI` via the `2` trick
    have h4 : (z - onePlusI * w) * oneMinusI = 0 := by
      rw [sub_mul, h3, sub_self]
    have h5 : (z - onePlusI * w) * (oneMinusI * onePlusI) = 0 := by
      rw [← mul_assoc, h4, zero_mul]
    have h6 : (z - onePlusI * w) * (2:Z8) = 0 := by
      rw [show oneMinusI * onePlusI = (2:Z8) from by
        rw [mul_comm]; exact onePlusI_mul_oneMinusI] at h5
      exact h5
    have := two_mul_eq_zero h6
    rw [sub_eq_zero] at this
    exact this

end Z8

open Z8

/-! ## 2×2 matrices over `R` -/

/-- A `2×2` matrix over `R = ℤ[ζ₈]`. -/
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

/-- Identity matrix. -/
def II : Mat2 := ⟨1,0,0,1⟩

/-- Matrix multiplication. -/
instance : Mul Mat2 := ⟨fun M N =>
  ⟨M.m00*N.m00 + M.m01*N.m10, M.m00*N.m01 + M.m01*N.m11,
   M.m10*N.m00 + M.m11*N.m10, M.m10*N.m01 + M.m11*N.m11⟩⟩

@[simp] theorem mul_m00 (M N : Mat2) : (M*N).m00 = M.m00*N.m00 + M.m01*N.m10 := rfl
@[simp] theorem mul_m01 (M N : Mat2) : (M*N).m01 = M.m00*N.m01 + M.m01*N.m11 := rfl
@[simp] theorem mul_m10 (M N : Mat2) : (M*N).m10 = M.m10*N.m00 + M.m11*N.m10 := rfl
@[simp] theorem mul_m11 (M N : Mat2) : (M*N).m11 = M.m10*N.m01 + M.m11*N.m11 := rfl

/-- Scalar multiple of a matrix by a ring element. -/
instance : SMul Z8 Mat2 := ⟨fun r M => ⟨r*M.m00, r*M.m01, r*M.m10, r*M.m11⟩⟩

@[simp] theorem smul_m00 (r:Z8)(M:Mat2):(r • M).m00 = r*M.m00 := rfl
@[simp] theorem smul_m01 (r:Z8)(M:Mat2):(r • M).m01 = r*M.m01 := rfl
@[simp] theorem smul_m10 (r:Z8)(M:Mat2):(r • M).m10 = r*M.m10 := rfl
@[simp] theorem smul_m11 (r:Z8)(M:Mat2):(r • M).m11 = r*M.m11 := rfl

/-- Determinant. -/
def det (M : Mat2) : Z8 := M.m00*M.m11 - M.m01*M.m10

/-- Conjugate transpose (dagger). -/
def dagger (M : Mat2) : Mat2 := ⟨conj M.m00, conj M.m10, conj M.m01, conj M.m11⟩

@[simp] theorem dagger_m00 (M:Mat2):(dagger M).m00 = conj M.m00 := rfl
@[simp] theorem dagger_m01 (M:Mat2):(dagger M).m01 = conj M.m10 := rfl
@[simp] theorem dagger_m10 (M:Mat2):(dagger M).m10 = conj M.m01 := rfl
@[simp] theorem dagger_m11 (M:Mat2):(dagger M).m11 = conj M.m11 := rfl

/-- Unitarity: `M · M† = I`. -/
def IsUnitary (M : Mat2) : Prop := M * dagger M = II

/-- Action on a column vector `(x,y)`. -/
def mulVec (M : Mat2) (v : Z8 × Z8) : Z8 × Z8 :=
  (M.m00*v.1 + M.m01*v.2, M.m10*v.1 + M.m11*v.2)

@[simp] theorem mulVec_fst (M : Mat2) (v : Z8 × Z8) :
    (M.mulVec v).1 = M.m00*v.1 + M.m01*v.2 := rfl
@[simp] theorem mulVec_snd (M : Mat2) (v : Z8 × Z8) :
    (M.mulVec v).2 = M.m10*v.1 + M.m11*v.2 := rfl

theorem det_mul (M N : Mat2) : det (M*N) = det M * det N := by
  simp [det]; ring

theorem det_dagger (M : Mat2) : det (dagger M) = conj (det M) := by
  simp [det, conj_sub, conj_mul]; ring

theorem det_II : det II = 1 := by decide

end Mat2

/-! ## The lattice `L₃` and its automorphisms -/

/-- Membership in `L₃ = {(a,b) : (1+i) ∣ a+b}`. -/
def InL3 (v : Z8 × Z8) : Prop := onePlusI ∣ (v.1 + v.2)

/-- `M` maps `L₃` into `L₃`. -/
def MapsToL (M : Mat2) : Prop := ∀ v, InL3 v → InL3 (M.mulVec v)

/-! ## The finite Clifford / automorphism enumerations -/

/-- The four units `{1, i, -1, -i}` (the `4`-th roots of unity). -/
def r4 : List Z8 := [1, imv, -1, -imv]

/-- The `32` integral single-qubit Clifford matrices: monomial matrices whose
nonzero entries are `4`-th roots of unity.  This is the monoid `⟨S, X⟩` (the
*integral* single-qubit Clifford group); the Hadamard gate is not integral and
hence not here. -/
def cliffList : List Mat2 :=
  (do let p ← r4; let q ← r4; pure (⟨p,0,0,q⟩:Mat2)) ++
  (do let p ← r4; let q ← r4; pure (⟨0,p,q,0⟩:Mat2))

/-- The integral single-qubit Clifford group as a `Finset`. -/
def cliffFinset : Finset Mat2 := cliffList.toFinset

/-- The `64` unitary integral automorphisms of `L₃`: monomial matrices with
`8`-th root entries `ζ^i, ζ^j` of equal parity `i ≡ j (mod 2)`. -/
def autList : List Mat2 :=
  (do let i ← List.range 8; let j ← List.range 8;
      if (i+j) % 2 == 0 then pure (⟨Z8.zeta^i,0,0,Z8.zeta^j⟩:Mat2) else []) ++
  (do let i ← List.range 8; let j ← List.range 8;
      if (i+j) % 2 == 0 then pure (⟨0,Z8.zeta^i,Z8.zeta^j,0⟩:Mat2) else [])

/-- The unitary integral automorphism group of `L₃` as a `Finset`. -/
def autFinset : Finset Mat2 := autList.toFinset

/-- A **phased (integral) Clifford**: an element of the integral Clifford group
`⟨S, X⟩`. -/
structure PhasedClifford where
  toMat : Mat2
  mem : toMat ∈ cliffFinset

/-- The phase gate `S = diag(1, i)`, an integral Clifford generator. -/
def Smat : Mat2 := ⟨1, 0, 0, imv⟩
/-- The Pauli `X` gate, an integral Clifford generator. -/
def Xmat : Mat2 := ⟨0, 1, 1, 0⟩

theorem Smat_mem_cliff : Smat ∈ cliffFinset := by decide
theorem Xmat_mem_cliff : Xmat ∈ cliffFinset := by decide
theorem II_mem_cliff : Mat2.II ∈ cliffFinset := by decide

/-- `cliffFinset` is closed under multiplication: it is the integral Clifford
monoid `⟨S, X⟩` (it contains `S`, `X`, the identity, and all products). -/
theorem cliffFinset_mul_closed :
    ∀ C ∈ cliffFinset, ∀ D ∈ cliffFinset, C * D ∈ cliffFinset := by decide

/-! ## Structure of unitary integral matrices -/

/-- A unitary integral matrix over `ℤ[ζ₈]` is **monomial** with root-of-unity
entries: either diagonal or antidiagonal, with the two nonzero entries having
`|·|² = 1`. -/
theorem unitary_is_monomial {M : Mat2} (h : M.IsUnitary) :
    (M.m01 = 0 ∧ M.m10 = 0 ∧ nsq M.m00 = 1 ∧ nsq M.m11 = 1) ∨
    (M.m00 = 0 ∧ M.m11 = 0 ∧ nsq M.m01 = 1 ∧ nsq M.m10 = 1) := by
  -- The two row norms are sums of integer squares equal to `1`.
  have e00 : nsq M.m00 + nsq M.m01 = 1 := by
    have h00 : (M * Mat2.dagger M).m00.a = (Mat2.II).m00.a :=
      congrArg (fun N => (Mat2.m00 N).a) h
    rw [Mat2.mul_m00, Z8.add_a, Mat2.dagger_m00, Mat2.dagger_m10,
      coord_a_mul_conj, coord_a_mul_conj] at h00
    simpa [Mat2.II] using h00
  have e11 : nsq M.m10 + nsq M.m11 = 1 := by
    have h11 : (M * Mat2.dagger M).m11.a = (Mat2.II).m11.a :=
      congrArg (fun N => (Mat2.m11 N).a) h
    rw [Mat2.mul_m11, Z8.add_a, Mat2.dagger_m01, Mat2.dagger_m11,
      coord_a_mul_conj, coord_a_mul_conj] at h11
    simpa [Mat2.II] using h11
  -- The off-diagonal Hermitian inner product vanishes.
  have e01 : M.m00 * conj M.m10 + M.m01 * conj M.m11 = 0 := by
    have h01 := congrArg (fun N => Mat2.m01 N) h
    simpa [Mat2.mul_m01, Mat2.dagger_m01, Mat2.dagger_m11, Mat2.II] using h01
  rcases (show nsq M.m00 = 1 ∧ nsq M.m01 = 0 ∨ nsq M.m00 = 0 ∧ nsq M.m01 = 1 by
      have := nsq_nonneg M.m00; have := nsq_nonneg M.m01; omega) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- diagonal case
    left
    have hm01 : M.m01 = 0 := nsq_eq_zero.mp hb
    have hu : M.m00 * conj M.m00 = 1 := mul_conj_root ha
    have hmul : M.m00 * conj M.m10 = 0 := by rw [hm01, zero_mul, add_zero] at e01; exact e01
    have hcm10 : conj M.m10 = 0 := by
      have h2 := congrArg (fun z => conj M.m00 * z) hmul
      simp only [mul_zero] at h2
      rw [← mul_assoc, mul_comm (conj M.m00) M.m00, hu, one_mul] at h2
      exact h2
    have hm10 : M.m10 = 0 := conj_eq_zero.mp hcm10
    have hn10 : nsq M.m10 = 0 := nsq_eq_zero.mpr hm10
    exact ⟨hm01, hm10, ha, by omega⟩
  · -- antidiagonal case
    right
    have hm00 : M.m00 = 0 := nsq_eq_zero.mp ha
    have hu : M.m01 * conj M.m01 = 1 := mul_conj_root hb
    have hmul : M.m01 * conj M.m11 = 0 := by rw [hm00, zero_mul, zero_add] at e01; exact e01
    have hcm11 : conj M.m11 = 0 := by
      have h2 := congrArg (fun z => conj M.m01 * z) hmul
      simp only [mul_zero] at h2
      rw [← mul_assoc, mul_comm (conj M.m01) M.m01, hu, one_mul] at h2
      exact h2
    have hm11 : M.m11 = 0 := conj_eq_zero.mp hcm11
    have hn11 : nsq M.m11 = 0 := nsq_eq_zero.mpr hm11
    exact ⟨hm00, hm11, hb, by omega⟩

/-- Membership of a unitary integral `L₃`-automorphism in `autFinset`. -/
theorem aut_mem {M : Mat2} (hUni : M.IsUnitary) (hAut : MapsToL M) :
    M ∈ autFinset := by
  rcases unitary_is_monomial hUni with h | h;
  · obtain ⟨i, hi⟩ := nsq_eq_one_root h.2.2.1
    obtain ⟨j, hj⟩ := nsq_eq_one_root h.2.2.2
    have hM : M = ⟨Z8.zeta^i.val, 0, 0, Z8.zeta^j.val⟩ := by
      grind +extAll;
    have h_div : onePlusI ∣ (Z8.zeta^i.val + Z8.zeta^j.val * imv) := by
      convert hAut ( 1, imv ) _ using 1;
      · simp +decide [ hM, Mat2.mulVec, InL3 ];
      · exact ⟨ 1, by decide ⟩;
    have := dvd_onePlusI_coords h_div; fin_cases i <;> fin_cases j <;> simp +decide at this ⊢;
    all_goals simp +decide [ hM, autFinset ] ;
  · obtain ⟨ i, hi ⟩ := nsq_eq_one_root h.2.2.1; obtain ⟨ j, hj ⟩ := nsq_eq_one_root h.2.2.2; simp_all +decide [autFinset] ;
    have h_div : onePlusI ∣ (zeta ^ (i : ℕ) * imv + zeta ^ (j : ℕ)) := by
      convert hAut ( 1, imv ) _ using 1;
      · simp +decide [ InL3, Mat2.mulVec, h, hi, hj ];
      · exact ⟨ 1, by decide ⟩;
    have := dvd_onePlusI_coords h_div; fin_cases i <;> fin_cases j <;> simp +decide at this ⊢;
    all_goals rw [ show M = ⟨ 0, M.m01, M.m10, 0 ⟩ from by cases M; aesop ] ; simp +decide [ * ] ;

/-! ## foundational round: determinant is a root of unity -/

/-- **foundational round .**  Every unitary integral matrix over `ℤ[ζ₈]` has
determinant equal to a power of `ζ₈`.  (The `MapsToL` hypothesis from the
the strawman framing as an *automorphism* is not needed for the result and is
omitted; cf. `det_root_of_unity'` for the stated form.) -/
theorem det_root_of_unity {M : Mat2} (hUni : M.IsUnitary) :
    ∃ k : Fin 8, M.det = Z8.zeta ^ (k:ℕ) := by
  have hdet : M.det * conj M.det = 1 := by
    have h := congrArg Mat2.det hUni
    rw [Mat2.det_mul, Mat2.det_dagger, Mat2.det_II] at h
    exact h
  have : nsq M.det = 1 := by
    have := congrArg Z8.a hdet
    rwa [coord_a_mul_conj] at this
  exact nsq_eq_one_root this

/-- The literal form, carrying the (unnecessary) automorphism
hypothesis. -/
theorem det_root_of_unity' {M : Mat2} (hUni : M.IsUnitary) (_hAut : MapsToL M) :
    ∃ k : Fin 8, M.det = Z8.zeta ^ (k:ℕ) :=
  det_root_of_unity hUni

/-! ## `MapsToL` for the enumerated automorphisms -/

/-- A diagonal matrix with `(1+i) ∣ (m00 - m11)` maps `L₃` into `L₃`. -/
theorem mapsToL_of_diag (M : Mat2) (h01 : M.m01 = 0) (h10 : M.m10 = 0)
    (hdvd : onePlusI ∣ (M.m00 - M.m11)) : MapsToL M := by
  intro v hv
  rw [InL3] at hv ⊢
  simp only [Mat2.mulVec_fst, Mat2.mulVec_snd, h01, h10, zero_mul, add_zero, zero_add]
  -- `m00*x + m11*y = m11*(x+y) + (m00-m11)*x`
  have hrw : M.m00 * v.1 + M.m11 * v.2 = M.m11 * (v.1 + v.2) + (M.m00 - M.m11) * v.1 := by ring
  rw [hrw]
  exact dvd_add (Dvd.dvd.mul_left hv _) (Dvd.dvd.mul_right hdvd _)

/-- An antidiagonal matrix with `(1+i) ∣ (m01 - m10)` maps `L₃` into `L₃`. -/
theorem mapsToL_of_antidiag (M : Mat2) (h00 : M.m00 = 0) (h11 : M.m11 = 0)
    (hdvd : onePlusI ∣ (M.m01 - M.m10)) : MapsToL M := by
  intro v hv
  rw [InL3] at hv ⊢
  simp only [Mat2.mulVec_fst, Mat2.mulVec_snd, h00, h11, zero_mul, add_zero, zero_add]
  have hrw : M.m01 * v.2 + M.m10 * v.1 = M.m10 * (v.1 + v.2) + (M.m01 - M.m10) * v.2 := by ring
  rw [hrw]
  exact dvd_add (Dvd.dvd.mul_left hv _) (Dvd.dvd.mul_right hdvd _)

/-- Each enumerated `M` is monomial with the relevant `1+i`-divisibility (computation). -/
theorem autFinset_monomial_dvd : ∀ M ∈ autFinset,
    (M.m01 = 0 ∧ M.m10 = 0 ∧ DvdOnePlusI (M.m00 - M.m11)) ∨
    (M.m00 = 0 ∧ M.m11 = 0 ∧ DvdOnePlusI (M.m01 - M.m10)) := by decide

/-- Every enumerated unitary automorphism preserves `L₃`. -/
theorem autFinset_mapsToL : ∀ M ∈ autFinset, MapsToL M := by
  intro M hM
  rcases autFinset_monomial_dvd M hM with ⟨h01, h10, hd⟩ | ⟨h00, h11, hd⟩
  · exact mapsToL_of_diag M h01 h10 ((dvdOnePlusI_iff _).mpr hd)
  · exact mapsToL_of_antidiag M h00 h11 ((dvdOnePlusI_iff _).mpr hd)

/-- Every enumerated automorphism is unitary. -/
theorem autFinset_unitary : ∀ M ∈ autFinset, M.IsUnitary := by
  have : ∀ M ∈ autFinset, M * M.dagger = Mat2.II := by decide
  exact this

/-- The integral special-unitary set equals the `det = 1` slice of `autFinset`. -/
theorem su2_set_eq :
    {M : Mat2 | M.IsUnitary ∧ MapsToL M ∧ M.det = 1}
      = ↑(autFinset.filter (fun M => M.det = 1)) := by
  ext M
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hu, ha, hd⟩
    exact ⟨aut_mem hu ha, hd⟩
  · rintro ⟨hmem, hd⟩
    exact ⟨autFinset_unitary M hmem, autFinset_mapsToL M hmem, hd⟩

/-! ## Finiteness of the integral special-unitary group -/

/-- **Finiteness of integral SU(2) .**  The integral special-unitary lattice-automorphism group
`{M : unitary, L₃-automorphism, det = 1}` is finite, of cardinality **exactly `16`**.

The strawman's proof sketch anticipated `24` (the order of the full projective
single-qubit Clifford group `≅ S₄` of K–S 2024).  But over the integer ring
`ℤ[ζ₈]` the Hadamard gate is **not** integral, so it is excluded and the count
collapses to `16` (projective image `8`).  See the module docstring. -/
theorem finite_integral_su2_aut_L3 :
    {M : Mat2 | M.IsUnitary ∧ MapsToL M ∧ M.det = 1}.Finite ∧
    Nat.card {M : Mat2 | M.IsUnitary ∧ MapsToL M ∧ M.det = 1} = 16 := by
  rw [su2_set_eq]
  refine ⟨(autFinset.filter (fun M => M.det = 1)).finite_toSet, ?_⟩
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

/-! ## The unitary converse -/

/-- Every element of `autFinset` is a phase `ζ₈^k` times an integral Clifford.
This is a finite computation. -/
theorem autFinset_phased_clifford :
    ∀ M ∈ autFinset, ∃ k ∈ List.range 8, ∃ C ∈ cliffFinset,
      M = Z8.zeta ^ k • C := by decide

/-- **Unitary converse .**  Every unitary integral automorphism of `L₃` is a phased
Clifford: it factors as `ζ₈^k` times an element of the integral Clifford
group. -/
theorem aut_L3_unitary_is_phased_clifford
    (M : Mat2) (hUni : M.IsUnitary) (hAut : MapsToL M) :
    ∃ (k : Fin 8) (C : PhasedClifford), M = Z8.zeta ^ (k : ℕ) • C.toMat := by
  obtain ⟨k, hk, C, hCmem, hMC⟩ := autFinset_phased_clifford M (aut_mem hUni hAut)
  refine ⟨⟨k % 8, Nat.mod_lt _ (by norm_num)⟩, ⟨C, hCmem⟩, ?_⟩
  rw [List.mem_range] at hk
  simp only [Nat.mod_eq_of_lt hk]
  exact hMC

end AutL3