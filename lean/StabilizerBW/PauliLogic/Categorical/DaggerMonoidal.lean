/-
# PauliLogic/Categorical/DaggerMonoidal.lean — the Lambek side, Target 2

## Dagger symmetric monoidal categories

A **dagger symmetric monoidal category** (Selinger 2007, §3; Heunen–Vicary
2019, Def. 3.x) is a symmetric monoidal category that is simultaneously a
dagger category, in a way compatible with the monoidal structure:

* the dagger preserves the tensor of morphisms:
  `dagger (f ⊗ₘ g) = dagger f ⊗ₘ dagger g`;
* the structural isomorphisms (associator, unitors) and the braiding are
  *unitary*, i.e. their dagger equals their inverse; concretely the braiding
  satisfies `dagger (β_ X Y).hom = (β_ X Y).inv`.

We build on Mathlib's `CategoryTheory.SymmetricCategory` and the
`DaggerCategory` class of `Dagger.lean`.
-/

import StabilizerBW.PauliLogic.Categorical.Dagger

open CategoryTheory MonoidalCategory

namespace PauliLogic.Categorical

universe v u

/-- A **dagger symmetric monoidal category**: a symmetric monoidal category
together with a compatible dagger.  The dagger preserves the monoidal product
of morphisms and makes the braiding unitary. -/
class DaggerSymmetricMonoidalCategory (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [SymmetricCategory C] extends DaggerCategory C where
  /-- The dagger preserves the tensor of morphisms. -/
  dagger_tensor : ∀ {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z),
    DaggerCategory.dagger (f ⊗ₘ g)
      = DaggerCategory.dagger f ⊗ₘ DaggerCategory.dagger g
  /-- The braiding is unitary: its dagger is its inverse. -/
  dagger_braiding : ∀ X Y : C,
    DaggerCategory.dagger (β_ X Y).hom = (β_ X Y).inv

namespace DaggerSymmetricMonoidalCategory

@[simp]
theorem dagger_tensor' {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] [DaggerSymmetricMonoidalCategory C]
    {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    DaggerCategory.dagger (f ⊗ₘ g)
      = DaggerCategory.dagger f ⊗ₘ DaggerCategory.dagger g :=
  dagger_tensor f g

@[simp]
theorem dagger_braiding' {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] [DaggerSymmetricMonoidalCategory C] (X Y : C) :
    DaggerCategory.dagger (β_ X Y).hom = (β_ X Y).inv :=
  dagger_braiding X Y

end DaggerSymmetricMonoidalCategory

/-! ## A genuine witness: the discrete category on a commutative monoid

For any commutative monoid `M`, the discrete category `Discrete M` is symmetric
monoidal (tensor = monoid multiplication) with subsingleton hom-sets, so it
carries a (necessarily trivial) compatible dagger.  This confirms the class is
inhabited by a non-degenerate symmetric monoidal category. -/

/-- The symmetric structure on `Discrete M` (all coherences are trivial since
hom-sets are subsingletons). -/
noncomputable instance discreteSymmetric (M : Type u) [CommMonoid M] :
    SymmetricCategory (Discrete M) where
  symmetry _ _ := Subsingleton.elim _ _

noncomputable instance discreteDaggerSymmetricMonoidal (M : Type u) [CommMonoid M] :
    DaggerSymmetricMonoidalCategory (Discrete M) where
  toDaggerCategory := instDiscreteDagger M
  dagger_tensor _ _ := Subsingleton.elim _ _
  dagger_braiding _ _ := Subsingleton.elim _ _

end PauliLogic.Categorical
