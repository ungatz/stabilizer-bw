import StabilizerBW.SqrtPi.Pi3
import StabilizerBW.SqrtPi.Level2.Lattice

/-!
# The level-2 free model `Π₂`: syntax, congruence, denotation, grade

`Pi2 m n` is the exact level-2 analogue of `Pi3`: the free bipermutative category at level
`k = 2`, where the scalar generator is `ζ₂ = ζ₄ = i` (instead of `ζ₃ = ζ₈`).  Constructors:

* `idn n`  — identity;
* `swp`    — additive symmetry `σ_⊕ : 2 → 2`;
* `zet`    — the phase generator `ζ₂ = i : 1 → 1`;
* `vv`     — the square-root-of-swap `V : 2 → 2`;
* `cmp`, `opl` — composition and additive product.

The denotation `⟦·⟧₂` lands in `Matrix (Fin n) (Fin m) ℚ[ζ₈]` (the same field as `Π₃`, since
`ℚ(ζ₈) = ℚ(i, √2) ⊇ ℚ(i)` and the level-2 `V = √X` already has entries `(1±i)/2 ∈ ℚ(i)`);
the integral lattice is taken over `ℤ[i]`.  The level-2 grade `grade₂` measures factors of the
level-2 prime `λ₂ = 1 - i` needed to push an operator back into the level-2 Barnes–Wall lattice.
-/

set_option maxRecDepth 4000

open Pi3

/-- Morphisms `m → n` of the free bipermutative category `Π₂` at level `k = 2`. -/
inductive Pi2 : ℕ → ℕ → Type
  | idn (n : ℕ) : Pi2 n n
  | swp : Pi2 2 2
  | zet : Pi2 1 1
  | vv : Pi2 2 2
  | cmp {m n p : ℕ} : Pi2 m n → Pi2 n p → Pi2 m p
  | opl {m n m' n' : ℕ} : Pi2 m n → Pi2 m' n' → Pi2 (m + m') (n + n')

namespace Pi2

open Pi3 Pi3.Zi

/-- Composition in `Π₂`. -/
infixr:70 " ⊚₂ " => Pi2.cmp
/-- Additive monoidal product `⊕` in `Π₂`. -/
infixr:65 " ⊞₂ " => Pi2.opl

/-- `ζ₄` composed `4` times, used to state axiom (E1) at level 2. -/
def zetaPow4 : Pi2 1 1 := zet ⊚₂ zet ⊚₂ zet ⊚₂ zet

/-- The equational congruence `≈₂` of `Π₂`: the smallest congruence containing the three
defining axioms (E1) `ζ₄⁴ = id`, (E2) `V² = σ_⊕`, (E3) the `√Π` relation at level 2. -/
inductive Cong : {m n : ℕ} → Pi2 m n → Pi2 m n → Prop
  | refl {m n} (a : Pi2 m n) : Cong a a
  | symm {m n} {a b : Pi2 m n} : Cong a b → Cong b a
  | trans {m n} {a b c : Pi2 m n} : Cong a b → Cong b c → Cong a c
  | cmp_congr {m n p} {a a' : Pi2 m n} {b b' : Pi2 n p} :
      Cong a a' → Cong b b' → Cong (a ⊚₂ b) (a' ⊚₂ b')
  | opl_congr {m n m' n'} {a a' : Pi2 m n} {b b' : Pi2 m' n'} :
      Cong a a' → Cong b b' → Cong (a ⊞₂ b) (a' ⊞₂ b')
  | id_cmp {m n} (a : Pi2 m n) : Cong (idn m ⊚₂ a) a
  | cmp_id {m n} (a : Pi2 m n) : Cong (a ⊚₂ idn n) a
  | cmp_assoc {m n p q} (a : Pi2 m n) (b : Pi2 n p) (c : Pi2 p q) :
      Cong ((a ⊚₂ b) ⊚₂ c) (a ⊚₂ (b ⊚₂ c))
  -- (E1): ζ₄⁴ = id
  | e1 : Cong zetaPow4 (idn 1)
  -- (E2): V² = σ_⊕
  | e2 : Cong (vv ⊚₂ vv) swp
  -- (E3): the √Π relation (congruence axiom slot at level 2)
  | e3 : Cong (vv ⊚₂ (idn 1 ⊞₂ (zet ⊚₂ zet)) ⊚₂ vv)
             ((idn 1 ⊞₂ (zet ⊚₂ zet)) ⊚₂ vv ⊚₂ (idn 1 ⊞₂ (zet ⊚₂ zet)))

@[inherit_doc] infix:50 " ≈₂ " => Cong

/-! ### Denotation -/

/-- `ζ₄ = i` as a `1×1` matrix over `ℚ[ζ₈]`. -/
def zeta2Mat : Matrix (Fin 1) (Fin 1) Q8 := Matrix.of ![![Q8.ofZ8 Z8.imag]]

/-- Denotation `⟦·⟧₂ : Pi2 m n → Matrix (Fin n) (Fin m) ℚ[ζ₈]`. -/
def denote : {m n : ℕ} → Pi2 m n → Matrix (Fin n) (Fin m) Q8
  | _, _, .idn _ => 1
  | _, _, .swp => Pi3.swapMat
  | _, _, .zet => zeta2Mat
  | _, _, .vv => Pi3.vMat
  | _, _, .cmp a b => denote b * denote a
  | _, _, .opl a b =>
      (Matrix.fromBlocks (denote a) 0 0 (denote b)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm

@[simp] lemma denote_id (n : ℕ) : denote (Pi2.idn n) = 1 := rfl
@[simp] lemma denote_sigma : denote Pi2.swp = Pi3.swapMat := rfl
@[simp] lemma denote_zeta2 : denote Pi2.zet = zeta2Mat := rfl
@[simp] lemma denote_V : denote Pi2.vv = Pi3.vMat := rfl
@[simp] lemma denote_circ {m n p : ℕ} (a : Pi2 m n) (b : Pi2 n p) :
    denote (a ⊚₂ b) = denote b * denote a := rfl
lemma denote_oplus {m n m' n' : ℕ} (a : Pi2 m n) (b : Pi2 m' n') :
    denote (a ⊞₂ b) = (Matrix.fromBlocks (denote a) 0 0 (denote b)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := rfl

/-! ### Grade -/

/-- The level-2 grade of a single-qubit (`2 → 2`) morphism, w.r.t. the single-qubit lattice `L₂`. -/
noncomputable def grade2sq (a : Pi2 2 2) : ℕ∞ := gradeWrt2 L2 (denote a)

/-- The level-2 grade of a two-qubit (`4 → 4`) morphism, w.r.t. the Barnes–Wall lattice `BW2L`.
This is the codomain of the catalytic embedding `Φ₃` on single-qubit `Π₃` morphisms. -/
noncomputable def grade2 (a : Pi2 4 4) : ℕ∞ := gradeWrt2 BW2L (denote a)

end Pi2
