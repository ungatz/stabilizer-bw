/-
# PauliLogic/Categorical/DaggerCompact.lean — the Lambek side, Target 3

## Dagger compact closed categories

A **dagger compact closed category** (Selinger 2007, Defs. 3.1–3.3;
Heunen–Vicary 2019, Ch. 3) is a dagger symmetric monoidal category in which
every object `X` has a dual `X*` with a unit (coevaluation)
`η_X : 𝟙_ ⟶ X ⊗ X*` and counit (evaluation) `ε_X : X* ⊗ X ⟶ 𝟙_` satisfying

1. the **snake / zig-zag (compact closure) equations**, packaged by Mathlib's
   `CategoryTheory.ExactPairing X X*`;
2. the **dagger compatibility**: the dagger of the coevaluation is the
   evaluation composed with the braiding,
   `dagger η_X = (β_ X X*).hom ≫ ε_X`.

For the PL_n / stabilizer setting every generating object is **self-dual**
(`X* = X`, because a Hermitian Pauli word is its own inverse), so we also
record the specialisation `SelfDualDaggerCompactClosed`.

We reuse Mathlib's `ExactPairing` for the snake equations rather than restating
them (per the standard convention to reuse rigid-monoidal infrastructure
where present).
-/

import StabilizerBW.PauliLogic.Categorical.DaggerMonoidal

open CategoryTheory MonoidalCategory

namespace PauliLogic.Categorical

universe v u

/-- A **dagger compact closed category**: a dagger symmetric monoidal category
with a chosen dual for every object, an exact pairing realising compact
closure, and dagger compatibility of the coevaluation. -/
class DaggerCompactClosed (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] [DaggerSymmetricMonoidalCategory C] where
  /-- The chosen dual object. -/
  dual : C → C
  /-- The compact-closure data (coevaluation, evaluation, snake equations). -/
  pairing : ∀ X : C, ExactPairing X (dual X)
  /-- Dagger compatibility of the coevaluation/evaluation. -/
  dagger_coevaluation : ∀ X : C,
    DaggerCategory.dagger (pairing X).coevaluation'
      = (β_ X (dual X)).hom ≫ (pairing X).evaluation'

namespace DaggerCompactClosed

/-- The coevaluation `η_X : 𝟙_ ⟶ X ⊗ X*`. -/
def coev {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [DaggerSymmetricMonoidalCategory C] [DaggerCompactClosed C] (X : C) :
    𝟙_ C ⟶ X ⊗ dual X := (pairing X).coevaluation'

/-- The evaluation `ε_X : X* ⊗ X ⟶ 𝟙_`. -/
def eval {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [DaggerSymmetricMonoidalCategory C] [DaggerCompactClosed C] (X : C) :
    dual X ⊗ X ⟶ 𝟙_ C := (pairing X).evaluation'

end DaggerCompactClosed

/-- A **self-dual** dagger compact closed category: every object is its own
dual.  This is the relevant specialisation for stabilizer quantum mechanics,
where each Hermitian Pauli word equals its own inverse. -/
class SelfDualDaggerCompactClosed (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [SymmetricCategory C]
    [DaggerSymmetricMonoidalCategory C] extends DaggerCompactClosed C where
  /-- Each object is its own dual. -/
  self_dual : ∀ X : C, dual X = X

/-! ## A genuine self-dual witness

Let `M` be a commutative monoid in which every element is its own inverse
(`x * x = 1`), i.e. an elementary abelian `2`-group — precisely the algebraic
shape of the symplectic `F₂`-representation of unsigned Pauli words.  Then the
discrete category `Discrete M` is self-dual dagger compact closed: each object
is its own dual, the coevaluation `𝟙_ ⟶ X ⊗ X` exists because `X.as² = 1`, and
all coherence/snake/dagger equations hold because hom-sets are subsingletons. -/

/-- The exact self-pairing on `Discrete M` when `x * x = 1`. -/
noncomputable def discreteSelfPairing (M : Type u) [CommMonoid M]
    (h : ∀ x : M, x * x = 1) (X : Discrete M) : ExactPairing X X where
  coevaluation' := Discrete.eqToHom (by
    show (1 : M) = X.as * X.as; exact (h X.as).symm)
  evaluation' := Discrete.eqToHom (by
    show X.as * X.as = (1 : M); exact h X.as)
  coevaluation_evaluation' := Subsingleton.elim _ _
  evaluation_coevaluation' := Subsingleton.elim _ _

/-- `Discrete M` (with `x * x = 1`) is dagger compact closed, self-dually. -/
noncomputable def discreteDaggerCompactClosed (M : Type u) [CommMonoid M]
    (h : ∀ x : M, x * x = 1) : DaggerCompactClosed (Discrete M) where
  dual X := X
  pairing X := discreteSelfPairing M h X
  dagger_coevaluation _ := Subsingleton.elim _ _

/-- `Discrete M` (with `x * x = 1`) is self-dual dagger compact closed. -/
noncomputable def discreteSelfDualDaggerCompactClosed (M : Type u) [CommMonoid M]
    (h : ∀ x : M, x * x = 1) :
    @SelfDualDaggerCompactClosed (Discrete M) _ _ _ _ :=
  letI := discreteDaggerCompactClosed M h
  { self_dual := fun _ => rfl }

end PauliLogic.Categorical
