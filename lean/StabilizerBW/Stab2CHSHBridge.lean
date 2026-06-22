import Mathlib

/-!
# Stabilizer-to-CHSH Compatibility Bridge

The CHSH functional `f = T_ZZ + T_ZX + T_XZ − T_XX` witnesses both entanglement
and magic.  This file formalizes the connection between the two-qubit stabilizer
polytope and the CHSH compatibility predicate.

## Strategy

1. **Pauli algebra** is represented decidably so the finite verification can
   run inside Lean's kernel.
2. **Stabilizer tableaux** — pairs of commuting, independent, non-identity
   signed two-qubit Pauli operators — enumerate all 60 pure stabilizer states
   (with overcounting).
3. A kernel-checked structural case-split (no `native_decide`) verifies that
   every valid tableau has |CHSH| ≤ 2.
4. The bound is lifted to `ℝ`-valued profiles and extended to the convex hull.
5. The separable (LHV) bound |CHSH| ≤ 2 for product states is proved
   analytically.
6. **Bridge corollary**: |CHSH| > 2 ⟹ entangled ∧ non-stabilizer (magic).

## Main results

* `stab_tableau_chsh_le`  — kernel-checked verification via structural case-split
* `stab_profile_chsh_bound` — every stabilizer profile satisfies |CHSH| ≤ 2
* `stab2_polytope_chsh_bound` — the bound extends to the convex hull
* `separable_profile_chsh_bound` — product states satisfy |CHSH| ≤ 2
* `chsh_violation_witnesses_entanglement_and_magic` — the bridge corollary
-/

open BigOperators Finset

namespace Stab2CHSHBridge

-- ════════════════════════════════════════════════════════════════════════
-- §1  Single-qubit Pauli type
-- ════════════════════════════════════════════════════════════════════════

/-- Single-qubit Pauli operators {I, X, Y, Z}. -/
inductive P1 : Type
  | I | X | Y | Z
  deriving DecidableEq, Repr, BEq, Inhabited

instance : Fintype P1 where
  elems := {.I, .X, .Y, .Z}
  complete x := by cases x <;> simp [Finset.mem_insert, Finset.mem_singleton]

/-- Pauli product with phase: `A · B = i ^ (phase) · result`.
    Only `phase ∈ {0,1,2,3}` is used. -/
def P1.mulPhase : P1 → P1 → ℕ × P1
  | .I, q => (0, q)
  | p, .I => (0, p)
  | .X, .X | .Y, .Y | .Z, .Z => (0, .I)
  | .X, .Y => (1, .Z) | .Y, .Z => (1, .X) | .Z, .X => (1, .Y)
  | .Y, .X => (3, .Z) | .Z, .Y => (3, .X) | .X, .Z => (3, .Y)

/-- Two single-qubit Paulis anticommute iff both are distinct non-identity. -/
def P1.ac : P1 → P1 → Bool
  | .I, _ | _, .I | .X, .X | .Y, .Y | .Z, .Z => false
  | _, _ => true

-- ════════════════════════════════════════════════════════════════════════
-- §2  Signed two-qubit Pauli
-- ════════════════════════════════════════════════════════════════════════

/-- A signed two-qubit Pauli `s · (P ⊗ Q)` where `s ∈ {+1, −1}`.
    `pos = true` means `s = +1`. -/
structure SP2 where
  pos : Bool
  p   : P1
  q   : P1
  deriving DecidableEq, Repr, BEq

/-- Equivalence with `Bool × P1 × P1` for `Fintype`. -/
private def SP2.equivProd : SP2 ≃ Bool × P1 × P1 where
  toFun a := (a.pos, a.p, a.q)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun (_, _, _) => rfl

instance : Fintype SP2 := Fintype.ofEquiv _ SP2.equivProd.symm

/-- Is this ±(I ⊗ I)? -/
def SP2.isId (a : SP2) : Bool := a.p == .I && a.q == .I

/-- Negate the sign. -/
def SP2.neg (a : SP2) : SP2 := { a with pos := !a.pos }

/-- Product of two signed two-qubit Paulis.  The result is correct when
    the two operators commute (total phase is real). -/
def SP2.mul (a b : SP2) : SP2 :=
  let (ph1, r1) := a.p.mulPhase b.p
  let (ph2, r2) := a.q.mulPhase b.q
  let totalPh := (ph1 + ph2) % 4
  let phasePos : Bool := totalPh == 0
  let inputPos : Bool := a.pos == b.pos
  { pos := phasePos == inputPos, p := r1, q := r2 }

/-- Two signed two-qubit Paulis commute iff an even number of qubit-wise
    factor pairs anticommute. -/
def SP2.comm (a b : SP2) : Bool :=
  a.p.ac b.p == a.q.ac b.q

-- ════════════════════════════════════════════════════════════════════════
-- §3  Stabilizer tableaux and CHSH extraction
-- ════════════════════════════════════════════════════════════════════════

/-- A pair `(g₁, g₂)` forms a valid 2-qubit stabilizer tableau when:
    * neither generator is ±I⊗I,
    * they commute, and
    * they are independent (g₂ ≠ ±g₁). -/
def isValidTableau (g1 g2 : SP2) : Bool :=
  !g1.isId && !g2.isId && g1.comm g2 && !(g1 == g2) && !(g1 == g2.neg)

/-- Expectation value of the Pauli observable `obsP ⊗ obsQ` in the pure
    stabilizer state defined by generators `(g₁, g₂)`.
    Returns `+1`, `−1`, or `0`. -/
def stabExpect (g1 g2 : SP2) (obsP obsQ : P1) : Int :=
  let g12 := g1.mul g2
  if g1.p == obsP && g1.q == obsQ then (if g1.pos then 1 else -1)
  else if g2.p == obsP && g2.q == obsQ then (if g2.pos then 1 else -1)
  else if g12.p == obsP && g12.q == obsQ then (if g12.pos then 1 else -1)
  else 0

/-- The CHSH_{Z,X} value extracted from a stabilizer tableau:
    `T_ZZ + T_ZX + T_XZ − T_XX`. -/
def stabCHSH (g1 g2 : SP2) : Int :=
  stabExpect g1 g2 .Z .Z + stabExpect g1 g2 .Z .X +
  stabExpect g1 g2 .X .Z - stabExpect g1 g2 .X .X

-- ════════════════════════════════════════════════════════════════════════
-- §4  Computational verification (kernel decide, structural case-split)
-- ════════════════════════════════════════════════════════════════════════

/-- **Verified by exhaustive kernel computation**: every valid stabilizer
    tableau gives |CHSH_{Z,X}| ≤ 2.

    The proof performs a structural case-split over the finitely many signed
    two-qubit Pauli generators `(g₁, g₂)` and discharges each fully concrete
    instance with the kernel `decide`, so the result depends only on the
    standard logical axioms (no `native_decide` / compiler trust). -/
theorem stab_tableau_chsh_le :
    ∀ g1 g2 : SP2, isValidTableau g1 g2 = true →
      (stabCHSH g1 g2).natAbs ≤ 2 := by
  rintro ⟨b1, p1, q1⟩ ⟨b2, p2, q2⟩
  cases b1 <;> cases b2 <;> cases p1 <;> cases q1 <;> cases p2 <;> cases q2 <;> decide

-- ════════════════════════════════════════════════════════════════════════
-- §5  Real-valued CHSH profile
-- ════════════════════════════════════════════════════════════════════════

/-- A CHSH-sector profile `(T_ZZ, T_ZX, T_XZ, T_XX)`. -/
structure CHSHProfile where
  zz : ℝ
  zx : ℝ
  xz : ℝ
  xx : ℝ

/-- The CHSH_{Z,X} functional on a profile. -/
def chshF (c : CHSHProfile) : ℝ :=
  c.zz + c.zx + c.xz - c.xx

/-- A real-valued profile arises from a valid stabilizer tableau. -/
def IsStabProfile (c : CHSHProfile) : Prop :=
  ∃ g1 g2 : SP2, isValidTableau g1 g2 = true ∧
    c.zz = ↑(stabExpect g1 g2 .Z .Z) ∧
    c.zx = ↑(stabExpect g1 g2 .Z .X) ∧
    c.xz = ↑(stabExpect g1 g2 .X .Z) ∧
    c.xx = ↑(stabExpect g1 g2 .X .X)

/-
Every stabilizer profile satisfies |CHSH| ≤ 2.
-/
theorem stab_profile_chsh_bound (c : CHSHProfile) (hc : IsStabProfile c) :
    |chshF c| ≤ 2 := by
      obtain ⟨g1, g2, hvalid, hz, hz', hxz, hxx⟩ := hc
      have h_bound : Int.natAbs (stabCHSH g1 g2) ≤ 2 :=
        stab_tableau_chsh_le g1 g2 hvalid
      simp [chshF, hz, hz', hxz, hxx] at *;
      norm_cast; simp_all +decide [ stabCHSH ] ;
      linarith [ abs_nonneg ( stabExpect g1 g2 P1.Z P1.Z + stabExpect g1 g2 P1.Z P1.X + stabExpect g1 g2 P1.X P1.Z - stabExpect g1 g2 P1.X P1.X ) ]

-- ════════════════════════════════════════════════════════════════════════
-- §6  Stabilizer polytope (convex hull of stabilizer profiles)
-- ════════════════════════════════════════════════════════════════════════

/-- A profile is in the two-qubit stabilizer polytope if it is a finite
    convex combination of pure stabilizer profiles. -/
def InStab2Polytope (c : CHSHProfile) : Prop :=
  ∃ (n : ℕ) (verts : Fin n → CHSHProfile) (w : Fin n → ℝ),
    (∀ i, IsStabProfile (verts i)) ∧
    (∀ i, 0 ≤ w i) ∧
    (∑ i, w i = 1) ∧
    c.zz = ∑ i, w i * (verts i).zz ∧
    c.zx = ∑ i, w i * (verts i).zx ∧
    c.xz = ∑ i, w i * (verts i).xz ∧
    c.xx = ∑ i, w i * (verts i).xx

/-- The CHSH functional is affine on the convex hull. -/
private lemma chshF_affine (n : ℕ) (verts : Fin n → CHSHProfile)
    (w : Fin n → ℝ)
    (hzz : c.zz = ∑ i, w i * (verts i).zz)
    (hzx : c.zx = ∑ i, w i * (verts i).zx)
    (hxz : c.xz = ∑ i, w i * (verts i).xz)
    (hxx : c.xx = ∑ i, w i * (verts i).xx) :
    chshF c = ∑ i, w i * chshF (verts i) := by
  simp only [chshF, hzz, hzx, hxz, hxx]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  congr 1; ext i; ring

/-- **Polytope CHSH bound**: any profile in the stabilizer polytope satisfies
    |CHSH| ≤ 2. -/
theorem stab2_polytope_chsh_bound (c : CHSHProfile) (hc : InStab2Polytope c) :
    |chshF c| ≤ 2 := by
  obtain ⟨n, verts, w, hstab, hw_nn, hw_sum, hzz, hzx, hxz, hxx⟩ := hc
  rw [chshF_affine n verts w hzz hzx hxz hxx]
  calc |∑ i, w i * chshF (verts i)|
      ≤ ∑ i, |w i * chshF (verts i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |chshF (verts i)| := by
        congr 1; ext i
        rw [abs_mul, abs_of_nonneg (hw_nn i)]
    _ ≤ ∑ i, w i * 2 := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_left (stab_profile_chsh_bound _ (hstab i)) (hw_nn i)
    _ = 2 := by rw [← Finset.sum_mul, hw_sum]; ring

-- ════════════════════════════════════════════════════════════════════════
-- §7  Separable (LHV) bound
-- ════════════════════════════════════════════════════════════════════════

/-- A profile arises from a product state with Bloch vectors `a`, `b`
    (each coordinate bounded by 1 in absolute value). -/
def IsSeparableProfile (c : CHSHProfile) : Prop :=
  ∃ a b : Fin 3 → ℝ,
    (∀ i, |a i| ≤ 1) ∧ (∀ i, |b i| ≤ 1) ∧
    c.zz = a 2 * b 2 ∧ c.zx = a 2 * b 0 ∧
    c.xz = a 0 * b 2 ∧ c.xx = a 0 * b 0

/-
Product states satisfy |CHSH| ≤ 2 (the LHV bound).
-/
theorem separable_profile_chsh_bound (c : CHSHProfile)
    (hc : IsSeparableProfile c) : |chshF c| ≤ 2 := by
      rcases hc with ⟨ a, b, ha, hb, h₁, h₂, h₃, h₄ ⟩;
      rw [ abs_le ];
      constructor <;> norm_num [ chshF, h₁, h₂, h₃, h₄ ];
      · simp_all +decide [ abs_le ];
        cases le_or_gt 0 ( a 0 + a 2 ) <;> cases le_or_gt 0 ( b 0 + b 2 ) <;> nlinarith [ ha 0, ha 2, hb 0, hb 2 ];
      · simp_all +decide [ Fin.forall_fin_succ, abs_le ];
        cases le_or_gt 0 ( a 2 + a 0 ) <;> cases le_or_gt 0 ( b 2 + b 0 ) <;> nlinarith

-- ════════════════════════════════════════════════════════════════════════
-- §8  Bridge corollary: CHSH violation witnesses entanglement AND magic
-- ════════════════════════════════════════════════════════════════════════

/-- **Bridge Theorem**: If |CHSH(ρ)| > 2 then ρ is both entangled (violates
    the LHV bound) and non-stabilizer (magic). -/
theorem chsh_violation_witnesses_entanglement_and_magic (c : CHSHProfile)
    (hviol : 2 < |chshF c|) :
    ¬ InStab2Polytope c ∧ ¬ IsSeparableProfile c :=
  ⟨fun h => absurd (stab2_polytope_chsh_bound c h) (not_le.mpr hviol),
   fun h => absurd (separable_profile_chsh_bound c h) (not_le.mpr hviol)⟩

/-- One-sided version: CHSH > 2 witnesses entanglement and magic. -/
theorem chsh_gt_two_witnesses (c : CHSHProfile) (hviol : 2 < chshF c) :
    ¬ InStab2Polytope c ∧ ¬ IsSeparableProfile c :=
  chsh_violation_witnesses_entanglement_and_magic c (lt_of_lt_of_le hviol (le_abs_self _))

#print axioms stab_tableau_chsh_le
#print axioms stab2_polytope_chsh_bound
#print axioms separable_profile_chsh_bound
#print axioms chsh_violation_witnesses_entanglement_and_magic

end Stab2CHSHBridge