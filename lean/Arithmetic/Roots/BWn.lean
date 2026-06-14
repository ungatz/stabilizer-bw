import RequestProject.Roots.Core

/-!
# The Barnes–Wall tower `BW_n = L_{2^n}` at all `n`, and the all-`n` geometric ceiling

This file develops the level-3 Barnes–Wall lattice tower over `R = ℤ[ζ₈]` for *every*
`n`, abstracting the concrete recursion mechanized at `n ≤ 4` in `BW2.lean`, `BW3.lean`
and `BW4.lean`. A `BW_n`-vector is a binary tree of depth `n` with `R`-leaves
(`BWVec 0 = R`, `BWVec (n+1) = BWVec n × BWVec n`), exactly the nested-pair model used
concretely (`Vec4 ≅ BWVec 2`, `Vec8 ≅ BWVec 3`, `Vec16 ≅ BWVec 4`).

The lattice is the iterated `(1+i)`-divisibility tower:

```
BW₀ = R, BW_{n+1} = { (h₀, h₁) : h₀, h₁ ∈ BW_n, h₀ − h₁ ∈ (1+i)·BW_n }.
```

This is **Angle B** of the round prompt — the inductive lattice recursion. The main
result is the all-`n` geometric a-priori ceiling

```
graden_le_top : ∀ (n) (D : BWVec n), graden n D ≤ 2 * n,
```

i.e. `λ^{2n}·D` preserves `BW_n` for *every* diagonal operator `D` on `n` qubits. This
generalizes the kernel-checked `gradeLE2_top` (`≤ 4`), `gradeLE3_top` (`≤ 6`) and
`gradeLE4_top` (`≤ 8`) to all `n`, and is the geometric bound `2n` cited as the
a-priori ceiling in the `n = 4` analysis.

The engine is the **conductor lemma** `conductor : (1+i)^n · R^{2^n} ⊆ BW_n`, proved by
induction; combined with `λ² = (1+i)·u` (`Z8.lam_sq`) it shows that scaling by
`λ^{2n} = (1+i)^n · u^n` lands the difference syndrome `n` levels deep, exactly into
`(1+i)·BW_n`.
-/

namespace Roots
open Z8

/-- A `BW_n`-vector: a binary tree of depth `n` with `R`-leaves. -/
def BWVec : ℕ → Type
 | 0 => Z8
 | n + 1 => BWVec n × BWVec n

/-- Vector addition on `BW_n`. -/
def bwAdd : (n : ℕ) → BWVec n → BWVec n → BWVec n
 | 0 => fun a b => (show Z8 from a) + (show Z8 from b)
 | n + 1 => fun a b => (bwAdd n a.1 b.1, bwAdd n a.2 b.2)

/-- Coordinatewise difference on `BW_n`. -/
def bwSub : (n : ℕ) → BWVec n → BWVec n → BWVec n
 | 0 => fun a b => (show Z8 from a) - (show Z8 from b)
 | n + 1 => fun a b => (bwSub n a.1 b.1, bwSub n a.2 b.2)

/-- Scalar action of `R` on `BW_n`. -/
def bwSmul : (n : ℕ) → Z8 → BWVec n → BWVec n
 | 0 => fun r a => r * (show Z8 from a)
 | n + 1 => fun r a => (bwSmul n r a.1, bwSmul n r a.2)

/-- Pointwise product (diagonal-operator action) on `BW_n`. -/
def bwMul : (n : ℕ) → BWVec n → BWVec n → BWVec n
 | 0 => fun a b => (show Z8 from a) * (show Z8 from b)
 | n + 1 => fun a b => (bwMul n a.1 b.1, bwMul n a.2 b.2)

/-- Membership in the level-3 Barnes–Wall lattice `BW_n = L_{2^n}`. -/
def inBW : (n : ℕ) → BWVec n → Prop
 | 0 => fun _ => True
 | n + 1 => fun a => inBW n a.1 ∧ inBW n a.2 ∧
 ∃ w : BWVec n, inBW n w ∧ bwSub n a.1 a.2 = bwSmul n oneI w

/-! ## Definitional equation lemmas (the `n+1` step) -/

@[simp] theorem bwAdd_succ (n a b) :
 bwAdd (n + 1) a b = (bwAdd n a.1 b.1, bwAdd n a.2 b.2) := rfl
@[simp] theorem bwSub_succ (n a b) :
 bwSub (n + 1) a b = (bwSub n a.1 b.1, bwSub n a.2 b.2) := rfl
@[simp] theorem bwSmul_succ (n r a) :
 bwSmul (n + 1) r a = (bwSmul n r a.1, bwSmul n r a.2) := rfl
@[simp] theorem bwMul_succ (n a b) :
 bwMul (n + 1) a b = (bwMul n a.1 b.1, bwMul n a.2 b.2) := rfl
theorem inBW_succ_iff (n a) :
 inBW (n + 1) a ↔ inBW n a.1 ∧ inBW n a.2 ∧
 ∃ w : BWVec n, inBW n w ∧ bwSub n a.1 a.2 = bwSmul n oneI w := Iff.rfl
theorem bwAdd_zero_eq (a b : BWVec 0) : bwAdd 0 a b = (show Z8 from a) + (show Z8 from b) := rfl
theorem bwSub_zero_eq (a b : BWVec 0) : bwSub 0 a b = (show Z8 from a) - (show Z8 from b) := rfl
theorem bwSmul_zero_eq (r : Z8) (a : BWVec 0) : bwSmul 0 r a = r * (show Z8 from a) := rfl
theorem bwMul_zero_eq (a b : BWVec 0) : bwMul 0 a b = (show Z8 from a) * (show Z8 from b) := rfl
theorem inBW_zero (a : BWVec 0) : inBW 0 a := trivial

/-! ## Algebraic identities (all by induction on `n`) -/

/-- `bwSmul` is associative in the scalar. -/
theorem bwSmul_bwSmul (n : ℕ) (r s : Z8) (v : BWVec n) :
 bwSmul n r (bwSmul n s v) = bwSmul n (r * s) v := by
 induction n with
 | zero => simp only [bwSmul_zero_eq, mul_assoc]
 | succ m ih => obtain ⟨v1, v2⟩ := v; simp only [bwSmul_succ, ih]

/-- `bwSmul` distributes over `bwSub`. -/
theorem bwSmul_bwSub (n : ℕ) (r : Z8) (a b : BWVec n) :
 bwSub n (bwSmul n r a) (bwSmul n r b) = bwSmul n r (bwSub n a b) := by
 induction n with
 | zero => simp only [bwSmul_zero_eq, bwSub_zero_eq, mul_sub]
 | succ m ih => obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; simp only [bwSmul_succ, bwSub_succ, ih]

/-- `bwSmul` distributes over `bwAdd`. -/
theorem bwSmul_bwAdd (n : ℕ) (r : Z8) (a b : BWVec n) :
 bwAdd n (bwSmul n r a) (bwSmul n r b) = bwSmul n r (bwAdd n a b) := by
 induction n with
 | zero => simp only [bwSmul_zero_eq, bwAdd_zero_eq, mul_add]
 | succ m ih => obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; simp only [bwSmul_succ, bwAdd_succ, ih]

/-- `bwSub` over `bwAdd`: `(a+c) - (b+d) = (a-b) + (c-d)`. -/
theorem bwSub_bwAdd (n : ℕ) (a b c d : BWVec n) :
 bwSub n (bwAdd n a c) (bwAdd n b d) = bwAdd n (bwSub n a b) (bwSub n c d) := by
 induction n with
 | zero => simp only [bwAdd_zero_eq, bwSub_zero_eq, add_sub_add_comm]
 | succ m ih =>
 obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d
 simp only [bwAdd_succ, bwSub_succ, ih]

/-- The scalar of a `bwSmul`-ed diagonal operator pulls out of `bwMul`. -/
theorem bwSmul_bwMul_left (n : ℕ) (r : Z8) (E v : BWVec n) :
 bwMul n (bwSmul n r E) v = bwSmul n r (bwMul n E v) := by
 induction n with
 | zero => simp only [bwSmul_zero_eq, bwMul_zero_eq, mul_assoc]
 | succ m ih => obtain ⟨E1, E2⟩ := E; obtain ⟨v1, v2⟩ := v; simp only [bwSmul_succ, bwMul_succ, ih]

/-! ## `R`-submodule laws -/

/-- `BW_n` is closed under the scalar action. -/
theorem bwSmul_inBW (n : ℕ) (r : Z8) {v : BWVec n} (h : inBW n v) :
 inBW n (bwSmul n r v) := by
 induction n with
 | zero => trivial
 | succ m ih =>
 obtain ⟨h1, h2, w, hw, hwd⟩ := h
 refine ⟨ih h1, ih h2, bwSmul m r w, ih hw, ?_⟩
 simp only [bwSmul_succ]
 rw [bwSmul_bwSub, hwd, bwSmul_bwSmul, bwSmul_bwSmul, mul_comm]

/-- `BW_n` is closed under addition. -/
theorem bwAdd_inBW (n : ℕ) {v w : BWVec n} (hv : inBW n v) (hw : inBW n w) :
 inBW n (bwAdd n v w) := by
 induction n with
 | zero => trivial
 | succ m ih =>
 obtain ⟨hv1, hv2, wv, hwv, hvd⟩ := hv
 obtain ⟨hw1, hw2, ww, hww, hwd⟩ := hw
 refine ⟨ih hv1 hw1, ih hv2 hw2, bwAdd m wv ww, ih hwv hww, ?_⟩
 simp only [bwAdd_succ]
 rw [bwSub_bwAdd, hvd, hwd, bwSmul_bwAdd]

/-! ## The conductor lemma: `(1+i)^n · R^{2^n} ⊆ BW_n` -/

/-- **Conductor lemma.** Scaling any `BW_n`-vector by `(1+i)^n` lands it in `BW_n`.
The conductor depth of `BW_n` is exactly `n`; this is the engine of the top bound. -/
theorem conductor (n : ℕ) (v : BWVec n) : inBW n (bwSmul n (oneI ^ n) v) := by
 induction n with
 | zero => trivial
 | succ m ih =>
 obtain ⟨v1, v2⟩ := v
 refine ⟨?_, ?_, bwSmul m (oneI ^ m) (bwSub m v1 v2), ih _, ?_⟩
 · simp only [bwSmul_succ]
 have h : bwSmul m (oneI ^ (m + 1)) v1 = bwSmul m oneI (bwSmul m (oneI ^ m) v1) := by
 rw [bwSmul_bwSmul, pow_succ, mul_comm]
 rw [h]; exact bwSmul_inBW m oneI (ih v1)
 · simp only [bwSmul_succ]
 have h : bwSmul m (oneI ^ (m + 1)) v2 = bwSmul m oneI (bwSmul m (oneI ^ m) v2) := by
 rw [bwSmul_bwSmul, pow_succ, mul_comm]
 rw [h]; exact bwSmul_inBW m oneI (ih v2)
 · simp only [bwSmul_succ]
 rw [bwSmul_bwSub, bwSmul_bwSmul]
 congr 1
 rw [pow_succ, mul_comm]

/-! ## The grade and the all-`n` geometric ceiling -/

/-- `λ^{2n} = (1+i)^n · u^n`, the power form of the ramification identity `λ² = (1+i)·u`. -/
theorem lam_pow_two_mul (n : ℕ) : Z8.lam ^ (2 * n) = oneI ^ n * uu ^ n := by
 induction n with
 | zero => simp
 | succ m ih =>
 have : Z8.lam ^ (2 * (m + 1)) = Z8.lam ^ (2 * m) * Z8.lam ^ 2 := by ring
 rw [this, ih, Z8.lam_sq]; ring

/-- A diagonal operator maps `BW_n` into `BW_n`. -/
def MapsToBW (n : ℕ) (D : BWVec n) : Prop := ∀ v, inBW n v → inBW n (bwMul n D v)

/-- Scaling preserves `MapsToBW`. -/
theorem mapsToBW_bwSmul (n : ℕ) (r : Z8) {D : BWVec n} (h : MapsToBW n D) :
 MapsToBW n (bwSmul n r D) := by
 intro v hv
 rw [bwSmul_bwMul_left]
 exact bwSmul_inBW n r (h v hv)

/-- `gradeLEn D k`: the operator `λ^k · D` maps `BW_n` into `BW_n`. -/
def gradeLEn (n : ℕ) (D : BWVec n) (k : ℕ) : Prop := MapsToBW n (bwSmul n (Z8.lam ^ k) D)

/-- `gradeLEn` is upward closed. -/
theorem gradeLEn_succ {n : ℕ} {D : BWVec n} {k : ℕ} (h : gradeLEn n D k) :
 gradeLEn n D (k + 1) := by
 unfold gradeLEn at *
 have : bwSmul n (Z8.lam ^ (k + 1)) D = bwSmul n Z8.lam (bwSmul n (Z8.lam ^ k) D) := by
 rw [bwSmul_bwSmul, pow_succ, mul_comm]
 rw [this]
 exact mapsToBW_bwSmul n Z8.lam h

theorem gradeLEn_of_le {n : ℕ} {D : BWVec n} {a b : ℕ} (h : gradeLEn n D a) (hab : a ≤ b) :
 gradeLEn n D b := by
 induction hab with
 | refl => exact h
 | step _ ih => exact gradeLEn_succ ih

/-- **Angle B — the all-`n` geometric ceiling.** Every diagonal operator on `n` qubits
has grade `≤ 2n`: scaling by `λ^{2n}` preserves `BW_n`. Generalizes `gradeLE2_top`,
`gradeLE3_top`, `gradeLE4_top` to all `n`. -/
theorem gradeLEn_top (n : ℕ) (D : BWVec n) : gradeLEn n D (2 * n) := by
 induction n with
 | zero => intro v _; trivial
 | succ m ih =>
 intro v hv
 obtain ⟨hv1, hv2, w, hw, hwd⟩ := hv
 have key1 : MapsToBW m (bwSmul m (Z8.lam ^ (2 * (m + 1))) D.1) :=
 gradeLEn_of_le (ih D.1) (by omega)
 have key2 : MapsToBW m (bwSmul m (Z8.lam ^ (2 * (m + 1))) D.2) :=
 gradeLEn_of_le (ih D.2) (by omega)
 refine ⟨?_, ?_, ?_⟩
 · simp only [bwSmul_succ, bwMul_succ]
 exact key1 v.1 hv1
 · simp only [bwSmul_succ, bwMul_succ]
 exact key2 v.2 hv2
 · simp only [bwSmul_succ, bwMul_succ]
 set raw := bwSub m (bwMul m D.1 v.1) (bwMul m D.2 v.2) with hraw
 refine ⟨bwSmul m (oneI ^ m) (bwSmul m (uu ^ (m + 1)) raw), conductor m _, ?_⟩
 rw [bwSmul_bwMul_left, bwSmul_bwMul_left, bwSmul_bwSub, ← hraw,
 bwSmul_bwSmul, bwSmul_bwSmul]
 congr 1
 rw [lam_pow_two_mul]; ring

/-- The grade `g(D) = min k with λ^k·D·BW_n ⊆ BW_n`. -/
noncomputable def graden (n : ℕ) (D : BWVec n) : ℕ := sInf {k | gradeLEn n D k}

theorem gradeLEn_nonempty (n : ℕ) (D : BWVec n) : ∃ k, gradeLEn n D k :=
 ⟨2 * n, gradeLEn_top n D⟩

theorem graden_le {n : ℕ} {D : BWVec n} {k : ℕ} (h : gradeLEn n D k) : graden n D ≤ k :=
 Nat.sInf_le h

/-- **The all-`n` geometric a-priori bound:** `g(D) ≤ 2n` for every diagonal `D`. -/
theorem graden_le_top (n : ℕ) (D : BWVec n) : graden n D ≤ 2 * n :=
 graden_le (gradeLEn_top n D)

/-! ## Angle A — the `ν = 0` single-monomial linear bound `g ≤ 2n − 1` at all `n`

The genuinely `n`-qubit `T`-type monomial `D_{x₁⋯xₙ} = diag(1,…,1,ζ)` is built
recursively as `bwT (n+1) = (bwId n, bwT n)` (identity on the low half, the lower
monomial on the high half), with `bwT 0 = ζ`. This reproduces `bwT 1 = T`,
`bwT 2 = cT`, `bwT 3 = ccT`, `bwT 4 = cccT`, whose grades `1,3,5,7` are kernel-checked
in `BW2`/`BW3`/`BW4`.

We prove `gradeLEn (n+1) (bwT (n+1)) (2*n+1)`, i.e. `g(bwT_{n+1}) ≤ 2(n+1) − 1`, for
*every* `n`. This is the linear closed form `w(d,0) = 2d − 1` for the maximal-degree
`ν = 0` monomial, at all `n` — the publication-grade objective of the round.

The proof is the recursion sketch: the low half is `bwId` (grade 0), the high half is
`bwT n` (grade `≤ 2n` by the ceiling, monotone to `2n+1`), and the difference syndrome
`h₀ − bwT·h₁ = (1+i)w + (bwId − bwT)·h₁` lands in `(1+i)·BW_n` because
`bwId − bwT = λ·(corner projector)` (lemma `bwSub_bwId_bwT`) and `λ^{2n+2} = (1+i)^{n+1}u^{n+1}`
puts the corner term `n+1` levels deep (one `(1+i)` explicit, the remaining `(1+i)^n`
absorbed by the `conductor`).
-/

/-- The all-zeros `BW_n`-vector. -/
def bwZero : (n : ℕ) → BWVec n
 | 0 => (0 : Z8)
 | n + 1 => (bwZero n, bwZero n)

/-- The identity diagonal `diag(1,…,1)` on `BW_n`. -/
def bwId : (n : ℕ) → BWVec n
 | 0 => (1 : Z8)
 | n + 1 => (bwId n, bwId n)

/-- The top-corner projector `diag(0,…,0,1)` on `BW_n`. -/
def bwCorner : (n : ℕ) → BWVec n
 | 0 => (1 : Z8)
 | n + 1 => (bwZero n, bwCorner n)

/-- The `T`-type monomial `diag(1,…,1,ζ)` on `BW_n` (degree-`n` `ν = 0` character). -/
def bwT : (n : ℕ) → BWVec n
 | 0 => zeta
 | n + 1 => (bwId n, bwT n)

@[simp] theorem bwZero_succ (n) : bwZero (n + 1) = (bwZero n, bwZero n) := rfl
@[simp] theorem bwId_succ (n) : bwId (n + 1) = (bwId n, bwId n) := rfl
@[simp] theorem bwCorner_succ (n) : bwCorner (n + 1) = (bwZero n, bwCorner n) := rfl
@[simp] theorem bwT_succ (n) : bwT (n + 1) = (bwId n, bwT n) := rfl

/-- Scaling the zero vector gives zero. -/
theorem bwSmul_bwZero (n : ℕ) (r : Z8) : bwSmul n r (bwZero n) = bwZero n := by
 induction n with
 | zero => simp only [bwSmul_zero_eq]; show r * (0 : Z8) = 0; exact mul_zero r
 | succ m ih => simp only [bwZero_succ, bwSmul_succ, ih]

/-- `a − a = 0` in `BW_n`. -/
theorem bwSub_self (n : ℕ) (a : BWVec n) : bwSub n a a = bwZero n := by
 induction n with
 | zero => simp only [bwSub_zero_eq]; show (show Z8 from a) - (show Z8 from a) = (0 : Z8); exact sub_self _
 | succ m ih => obtain ⟨a1, a2⟩ := a; simp only [bwSub_succ, bwZero_succ, ih]

/-- The identity diagonal acts trivially: `bwId · v = v`. -/
theorem bwId_mul (n : ℕ) (v : BWVec n) : bwMul n (bwId n) v = v := by
 induction n with
 | zero => simp only [bwMul_zero_eq]; show (1 : Z8) * (show Z8 from v) = v; exact one_mul _
 | succ m ih => obtain ⟨v1, v2⟩ := v; simp only [bwId_succ, bwMul_succ, ih]

/-- Pointwise distributivity of `bwMul` over `bwSub` in the operator slot. -/
theorem bwSub_bwMul (n : ℕ) (A B v : BWVec n) :
 bwSub n (bwMul n A v) (bwMul n B v) = bwMul n (bwSub n A B) v := by
 induction n with
 | zero => simp only [bwMul_zero_eq, bwSub_zero_eq, sub_mul]
 | succ m ih =>
 obtain ⟨A1, A2⟩ := A; obtain ⟨B1, B2⟩ := B; obtain ⟨v1, v2⟩ := v
 simp only [bwMul_succ, bwSub_succ, ih]

/-- Telescoping: `(a − b) + (b − c) = a − c`. -/
theorem bwAdd_bwSub_telescope (n : ℕ) (a b c : BWVec n) :
 bwAdd n (bwSub n a b) (bwSub n b c) = bwSub n a c := by
 induction n with
 | zero => simp only [bwAdd_zero_eq, bwSub_zero_eq, sub_add_sub_cancel]
 | succ m ih =>
 obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
 simp only [bwAdd_succ, bwSub_succ, ih]

/-- The defect `bwId − bwT = λ · (corner projector)`. -/
theorem bwSub_bwId_bwT (n : ℕ) :
 bwSub n (bwId n) (bwT n) = bwSmul n Z8.lam (bwCorner n) := by
 induction n with
 | zero =>
 simp only [bwSmul_zero_eq]
 show (show Z8 from bwId 0) - (show Z8 from bwT 0) = Z8.lam * (show Z8 from bwCorner 0)
 decide
 | succ m ih =>
 simp only [bwId_succ, bwT_succ, bwCorner_succ, bwSub_succ, bwSmul_succ, ih]
 rw [Prod.mk.injEq]
 refine ⟨?_, rfl⟩
 rw [bwSmul_bwZero, bwSub_self]

/-- `(1+i)·BW_n` is closed under `bwAdd`. -/
theorem inOneIBW_add {n : ℕ} {x y : BWVec n}
 (hx : ∃ a, inBW n a ∧ x = bwSmul n oneI a)
 (hy : ∃ b, inBW n b ∧ y = bwSmul n oneI b) :
 ∃ c, inBW n c ∧ bwAdd n x y = bwSmul n oneI c := by
 obtain ⟨a, ha, rfl⟩ := hx
 obtain ⟨b, hb, rfl⟩ := hy
 exact ⟨bwAdd n a b, bwAdd_inBW n ha hb, (bwSmul_bwAdd n oneI a b)⟩

/-
**Angle A — the `ν = 0` single-monomial linear bound at all `n`.**
`g(bwT_{n+1}) ≤ 2(n+1) − 1`: the maximal-degree `T`-type monomial on `n+1` qubits has
grade at most `2(n+1) − 1`, one below the geometric ceiling. This is the linear closed
form `w(d, 0) = 2d − 1` at all `n`.
-/
theorem bwT_gradeLE (n : ℕ) : gradeLEn (n + 1) (bwT (n + 1)) (2 * n + 1) := by
 intro v hv
 obtain ⟨hv1, hv2, w, hw, hwd⟩ := hv
 refine ⟨?_, ?_, ?_⟩;
 · convert bwSmul_inBW n ( lam ^ ( 2 * n + 1 ) ) hv1 using 1;
 convert bwSmul_bwMul_left n ( lam ^ ( 2 * n + 1 ) ) ( bwId n ) v.1 using 1;
 rw [ bwId_mul ];
 · have h_grade : gradeLEn n (bwT n) (2 * n + 1) := by
 exact gradeLEn_of_le ( gradeLEn_top n ( bwT n ) ) ( by linarith );
 convert h_grade v.2 hv2 using 1;
 · -- By `bwAdd_bwSub_telescope`, this is exactly `bwAdd n (bwSmul n oneI w) (bwSmul n lam (bwMul n (bwCorner n) v.2))`.
 have h_telescope : bwSub n v.1 (bwMul n (bwT n) v.2) = bwAdd n (bwSmul n oneI w) (bwSmul n lam (bwMul n (bwCorner n) v.2)) := by
 rw [ ← hwd, ← bwAdd_bwSub_telescope ];
 rw [ show bwSub n v.2 ( bwMul n ( bwT n ) v.2 ) = bwMul n ( bwSub n ( bwId n ) ( bwT n ) ) v.2 from ?_ ];
 · rw [ bwSub_bwId_bwT ];
 rw [ bwSmul_bwMul_left ];
 · rw [ ← bwSub_bwMul ];
 rw [ bwId_mul ];
 -- By `inOneIBW_add`, this is exactly `bwSmul n oneI (bwAdd n (bwSmul n c w) (bwSmul n (oneI^n) (bwSmul n (uu^(n+1)) (bwMul n (bwCorner n) v.2))))`.
 obtain ⟨z, hz⟩ : ∃ z : BWVec n, inBW n z ∧ bwAdd n (bwSmul n (lam ^ (2 * n + 1)) (bwSmul n oneI w)) (bwSmul n (lam ^ (2 * n + 1)) (bwSmul n lam (bwMul n (bwCorner n) v.2))) = bwSmul n oneI z := by
 apply inOneIBW_add;
 · use bwSmul n (lam ^ (2 * n + 1)) w;
 exact ⟨ bwSmul_inBW n _ hw, by rw [ bwSmul_bwSmul, bwSmul_bwSmul, mul_comm ] ⟩;
 · use bwSmul n (oneI ^ n) (bwSmul n (uu ^ (n + 1)) (bwMul n (bwCorner n) v.2));
 refine' ⟨ _, _ ⟩;
 · apply conductor;
 · simp +decide only [bwSmul_bwSmul, ← mul_assoc];
 rw [ show lam ^ ( 2 * n + 1 ) * lam = oneI ^ ( n + 1 ) * uu ^ ( n + 1 ) by
 rw [ ← pow_succ, show 2 * n + 2 = 2 * ( n + 1 ) by ring, lam_pow_two_mul ] ];
 rw [ pow_succ' ];
 grind +suggestions

/-- The grade of the all-`n` `T`-type monomial is at most `2(n+1) − 1`. -/
theorem bwT_graden_le (n : ℕ) : graden (n + 1) (bwT (n + 1)) ≤ 2 * (n + 1) - 1 := by
 have h := graden_le (bwT_gradeLE n)
 omega

end Roots