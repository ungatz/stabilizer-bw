/-
# Dagger categories

A dagger category (Selinger 2007; Heunen–Vicary 2019) is a category `C`
equipped with an involutive, identity-on-objects, contravariant functor
`† : C → Cᵒᵖ`.  Concretely, a family of maps `dagger : (X ⟶ Y) → (Y ⟶ X)`
satisfying

  `dagger (𝟙 X) = 𝟙 X`,
  `dagger (f ≫ g) = dagger g ≫ dagger f`,
  `dagger (dagger f) = f`.

Mathlib has rich monoidal infrastructure but not a dagger-category typeclass,
so we define it here, on top of `CategoryTheory.Category`.

This is the scaffolding for the PL_n derivation category (see `PLnCategory`).
The dagger encodes the reversibility of the Aaronson–Gottesman tableau steps:
the dagger of a derivation of `[P] ⊢ Q` is a derivation of `[Q] ⊢ P`.
-/

import Mathlib

open CategoryTheory

namespace PauliLogic.Categorical

universe v u

/-- A **dagger category**: a category with an involutive, identity-on-objects,
contravariant self-functor `dagger`.  (Selinger 2007, Definition 2.1.) -/
class DaggerCategory (C : Type u) [Category.{v} C] where
  /-- The dagger of a morphism, reversing its direction. -/
  dagger : ∀ {X Y : C}, (X ⟶ Y) → (Y ⟶ X)
  /-- The dagger fixes identities. -/
  dagger_id : ∀ X : C, dagger (𝟙 X) = 𝟙 X
  /-- The dagger is contravariant on composition. -/
  dagger_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    dagger (f ≫ g) = dagger g ≫ dagger f
  /-- The dagger is involutive. -/
  dagger_dagger : ∀ {X Y : C} (f : X ⟶ Y), dagger (dagger f) = f

namespace DaggerCategory

/-- Notation `f†` for the dagger of a morphism `f`. -/
scoped postfix:max "†" => DaggerCategory.dagger

@[simp]
theorem dagger_id' {C : Type u} [Category.{v} C] [DaggerCategory C] (X : C) :
    DaggerCategory.dagger (𝟙 X) = 𝟙 X := dagger_id X

@[simp]
theorem dagger_dagger' {C : Type u} [Category.{v} C] [DaggerCategory C]
    {X Y : C} (f : X ⟶ Y) : DaggerCategory.dagger (DaggerCategory.dagger f) = f :=
  dagger_dagger f

theorem dagger_comp' {C : Type u} [Category.{v} C] [DaggerCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    DaggerCategory.dagger (f ≫ g)
      = DaggerCategory.dagger g ≫ DaggerCategory.dagger f := dagger_comp f g

/-- The dagger is a bijection on hom-sets, with itself as inverse. -/
theorem dagger_injective {C : Type u} [Category.{v} C] [DaggerCategory C]
    {X Y : C} : Function.Injective (DaggerCategory.dagger (X := X) (Y := Y)) := by
  intro f g h
  have := congrArg DaggerCategory.dagger h
  simpa using this

/-- A morphism `f` is **unitary** when `f† ≫ f = 𝟙` and `f ≫ f† = 𝟙`. -/
def IsUnitary {C : Type u} [Category.{v} C] [DaggerCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  DaggerCategory.dagger f ≫ f = 𝟙 Y ∧ f ≫ DaggerCategory.dagger f = 𝟙 X

/-- A morphism `f` is **self-adjoint** when `f† = f` (requires `X = Y`). -/
def IsSelfAdjoint {C : Type u} [Category.{v} C] [DaggerCategory C]
    {X : C} (f : X ⟶ X) : Prop :=
  DaggerCategory.dagger f = f

end DaggerCategory

/-! ## A canonical witness: every discrete category is a dagger category

For any type `α`, the discrete category `Discrete α` carries a dagger: a
morphism is an equality of objects, and the dagger reverses it.  All dagger
axioms hold because hom-sets are subsingletons.  This both confirms
`DaggerCategory` is inhabited and supplies the dagger used by the discrete
stabilizer/symplectic models downstream. -/

instance instDiscreteDagger (α : Type u) : DaggerCategory (Discrete α) where
  dagger {_ _} f := Discrete.eqToHom (Discrete.eq_of_hom f).symm
  dagger_id _ := Subsingleton.elim _ _
  dagger_comp _ _ := Subsingleton.elim _ _
  dagger_dagger _ := Subsingleton.elim _ _

end PauliLogic.Categorical
