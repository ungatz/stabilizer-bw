/-
# The category of PL_n entailments, and its symplectic strictification

This file builds the Lambek side of the Curry-Howard-Lambek correspondence
for stabilizer entailment.  Two related categories are constructed.

## `Cat_PL_n` — the stabilizer-entailment groupoid

Objects are signed Pauli words `Pauli n`.  A morphism `P ⟶ Q` is a proof that
`P` and `Q` are *stabilizer equivalent*, i.e. `V [P] = V [Q]` (their model
spaces coincide).  By soundness and completeness this is exactly mutual
derivability `[P] ⊢ Q` and `[Q] ⊢ P`, so a morphism is a derivation modulo
cut-elimination: distinct cut-equivalent derivations of the same entailment
collapse to a single morphism (`Hom` is a subsingleton).  Identity and
composition are reflexivity and transitivity of `=` on model spaces — the
cut-and-normalise composition viewed under soundness/completeness.  The
dagger sends `P ⟶ Q` to `Q ⟶ P` by symmetry of `=`, encoding the
reversibility of the Aaronson-Gottesman tableau steps; every morphism is
unitary and `Cat_PL_n` is a groupoid.

## `SymCat_PL_n` — the symplectic strictification

The signed product `Pauli.mul` is not associative up to stabilizer equivalence
(the order-dependent `i`-phase changes the sign, and `+P`/`-P` have disjoint
model spaces), so `(Pauli n, Pauli.mul)` is not monoidal.  The honest
monoidal / compact structure lives on the symplectic `F₂`-representation,
where signs are quotiented out: objects are `Multiplicative ((Fin n → ZMod 2)²)`,
an elementary abelian 2-group under XOR.  The discrete category on this group
is dagger symmetric monoidal (tensor = XOR) and self-dual dagger compact
closed: each object squares to the unit, giving the self-pairing `η_x : I ⟶ x ⊗ x`,
with snake and dagger-compatibility equations holding by subsingleton homs.

The categorical face of the slogan *Clifford dynamics is gauge*: the
compact-closed tensor structure is exactly the sign-free symplectic group.
-/

import StabilizerBW.PauliLogic.Categorical.DaggerCompact
import StabilizerBW.PauliLogic.Soundness

open CategoryTheory MonoidalCategory

namespace PauliLogic
namespace PLnCategory

open Categorical

/-! ## Objects and the stabilizer-entailment groupoid -/

/-- Objects of `Cat_PL_n`: signed Pauli words. -/
structure PLObj (n : ℕ) where
  /-- The underlying signed Pauli word. -/
  word : Pauli n

/-- Two Pauli words are **stabilizer equivalent** when their model spaces (sets
of joint `+1`-eigenvectors) coincide.  By soundness + completeness this is
mutual derivability. -/
def StabEquiv {n : ℕ} (P Q : Pauli n) : Prop :=
  V ([P] : List (Pauli n)) = V ([Q] : List (Pauli n))

/-- `Cat_PL_n` as a category: a thin groupoid of stabilizer entailments. -/
instance category (n : ℕ) : Category (PLObj n) where
  Hom P Q := PLift (StabEquiv P.word Q.word)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Hom-sets of `Cat_PL_n` are subsingletons (thinness / proof-irrelevance of
stabilizer entailment). -/
instance homSubsingleton {n : ℕ} {P Q : PLObj n} : Subsingleton (P ⟶ Q) :=
  inferInstanceAs (Subsingleton (PLift (StabEquiv P.word Q.word)))

/-- **Target 4 — `Cat_PL_n` is a category.**  The thin groupoid of stabilizer
entailments on signed Pauli words. -/
def is_category (n : ℕ) : Category (PLObj n) := category n

/-- The dagger on `Cat_PL_n`: reverse a stabilizer-entailment morphism, by
symmetry of `=` on model spaces (reversibility of the tableau steps). -/
instance daggerCategory (n : ℕ) : DaggerCategory (PLObj n) where
  dagger {_ _} f := ⟨f.down.symm⟩
  dagger_id _ := Subsingleton.elim _ _
  dagger_comp _ _ := Subsingleton.elim _ _
  dagger_dagger _ := Subsingleton.elim _ _

/-- **Target 5 — `Cat_PL_n` is a dagger category.** -/
def dagger_category (n : ℕ) : DaggerCategory (PLObj n) := daggerCategory n

/-- Every morphism of `Cat_PL_n` is unitary: `Cat_PL_n` is a dagger groupoid. -/
theorem isUnitary {n : ℕ} {P Q : PLObj n} (f : P ⟶ Q) :
    DaggerCategory.IsUnitary f :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-! ## The symplectic strictification: monoidal & compact closed structure -/

/-- Symplectic `F₂` vectors: the `(x, z)` bits of an unsigned Pauli word, an
elementary abelian `2`-group under coordinatewise XOR. -/
abbrev SymVec (n : ℕ) := (Fin n → ZMod 2) × (Fin n → ZMod 2)

/-- The symplectic group of unsigned `n`-qubit Pauli words (XOR group). -/
abbrev SymPL (n : ℕ) := Multiplicative (SymVec n)

/-- Each symplectic vector is its own inverse (`x · x = 1`): the algebraic core
of self-duality. -/
theorem symPL_self_inv {n : ℕ} (x : SymPL n) : x * x = 1 := by
  have key : ∀ a : ZMod 2, a + a = 0 := by decide
  apply Multiplicative.toAdd.injective
  show Multiplicative.toAdd x + Multiplicative.toAdd x = 0
  ext i <;> simp [key]

/-- The symplectic strictification `SymCat_PL_n := Discrete (SymPL n)`. -/
abbrev SymCat (n : ℕ) := Discrete (SymPL n)

/-- **Target 6 — `SymCat_PL_n` is dagger symmetric monoidal.**  The tensor is
XOR of symplectic vectors; the braiding is symmetric; the dagger is compatible
with both. -/
noncomputable def dagger_symmetric_monoidal (n : ℕ) :
    DaggerSymmetricMonoidalCategory (SymCat n) :=
  Categorical.discreteDaggerSymmetricMonoidal (SymPL n)

/-- **Target 7 — `SymCat_PL_n` is self-dual dagger compact closed.**  Each
symplectic object is its own dual, with coevaluation `η_x : I ⟶ x ⊗ x` (valid
since `x · x = 1`) and the snake/dagger equations. -/
noncomputable def compact_closed (n : ℕ) :
    @SelfDualDaggerCompactClosed (SymCat n) _ _ _ (dagger_symmetric_monoidal n) :=
  Categorical.discreteSelfDualDaggerCompactClosed (SymPL n) symPL_self_inv

/-- Forget the sign of a Pauli word, landing in the symplectic group. -/
def toSym {n : ℕ} (P : Pauli n) : SymPL n :=
  Multiplicative.ofAdd (fun i => if P.xs i then (1 : ZMod 2) else 0,
    fun i => if P.zs i then (1 : ZMod 2) else 0)

end PLnCategory
end PauliLogic
