/-
# The interpretation functor `[[-]] : Cat_PL_n → Stab_n`

We define the stabilizer category `Stab_n` concretely as the discrete category
on stabilizer subspaces of `ℂ^(2ⁿ)` (model spaces `V Γ ⊆ Vec n`), and define
the interpretation functor sending

  an object (signed Pauli word `P`) to its model space `V [P]` — the
    `+1`-eigenspace of `pauliAction P`, i.e. the stabilizer code it defines;
  a morphism `P ⟶ Q` (a stabilizer entailment `V [P] = V [Q]`) to the
    corresponding identification of stabilizer subspaces.

Because `Cat_PL_n` is the thin entailment groupoid and `Stab_n` is discrete,
the functor is automatically well-defined and faithful, and it commutes with
the dagger (reversal of entailments), so it is a dagger functor.

The operator-level content (`pauliAction`) is supplied by `Soundness.lean`.
-/

import StabilizerBW.PauliLogic.Categorical.PLnCategory

open CategoryTheory

namespace PauliLogic
namespace PLnCategory

open Categorical

/-- The **stabilizer category** `Stab_n`: the discrete category of stabilizer
subspaces (model spaces) of `ℂ^(2ⁿ)`. -/
abbrev StabN (n : ℕ) := Discrete (Set (Vec n))

/-- **Target 8 — the interpretation functor `[[-]] : Cat_PL_n → Stab_n`.**
Objects map to their model space (stabilizer code), morphisms to the induced
identification of stabilizer subspaces. -/
def interpret_functor (n : ℕ) : PLObj n ⥤ StabN n where
  obj P := Discrete.mk (V ([P.word] : List (Pauli n)))
  map {_ _} f := Discrete.eqToHom f.down
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp] theorem interpret_obj {n : ℕ} (P : PLObj n) :
    (interpret_functor n).obj P = Discrete.mk (V ([P.word] : List (Pauli n))) := rfl

/-- The interpretation functor is **faithful** (it reflects equality of
morphisms): equal interpretations come from equal entailment morphisms. -/
instance interpret_faithful (n : ℕ) : (interpret_functor n).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- **The interpretation is a dagger functor**: it commutes with the dagger,
sending the reverse of an entailment to the reverse of its interpretation. -/
theorem interpret_dagger {n : ℕ} {P Q : PLObj n} (f : P ⟶ Q) :
    (interpret_functor n).map (DaggerCategory.dagger f)
      = DaggerCategory.dagger ((interpret_functor n).map f) :=
  Subsingleton.elim _ _

/-- The interpretation preserves units: it sends a morphism to a morphism
between the asserted stabilizer codes (`map` is, on the nose, the transport of
the entailment equality). -/
theorem interpret_map_eq {n : ℕ} {P Q : PLObj n} (f : P ⟶ Q) :
    V ([P.word] : List (Pauli n)) = V ([Q.word] : List (Pauli n)) := f.down

end PLnCategory
end PauliLogic
