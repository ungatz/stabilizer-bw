/-
# PauliLogic/Categorical/ZXComparison.lean — the Lambek side, Target 10

## Comparison with Backens 2014 (ZX-stabilizer completeness)

Backens' theorem (*The ZX-calculus is complete for stabilizer quantum
mechanics*, NJP 2014) states that the stabilizer fragment of the ZX-calculus,
as a dagger compact closed category, is complete for stabilizer quantum
mechanics.  A *fully formal* proof of equivalence with the ZX-calculus is out
of reach here because the ZX-calculus (and Backens' rewrite system) is not
formalised in Lean — this is flagged as out of scope.

Following the Tier-C prescription we therefore:

* make the comparison **statement** precise, carrying the ZX side as an
  explicit **`Prop` hypothesis** (never an `axiom`): a `StabilizerZXModel`
  bundles a Backens-style ZX interpretation `zxInterp` of Pauli words together
  with the carried completeness/soundness fact `backens` (ZX-diagram equality
  modulo Backens' rewrite rules ⇔ `Cat_PL_n` morphism existence);
* **prove** the structural comparison theorem `zx_stabilizer_comparison`: under
  any such model, ZX-stabilizer equality coincides with our stabilizer-subspace
  interpretation `[[-]] : Cat_PL_n → Stab_n` (Target 8) — using the
  unconditional `universality_categorical`;
* **prove the trivial/consistency direction** (`stabModelOfInterpret`): a
  `StabilizerZXModel` actually exists, taking the ZX interpretation to be our
  own stabilizer interpretation, so the carried hypothesis is satisfiable and
  the comparison is non-vacuous.
-/

import StabilizerBW.PauliLogic.Categorical.Universality

open CategoryTheory

namespace PauliLogic
namespace PLnCategory

/-- A **stabilizer ZX model** (Backens 2014, abstracted).  It records a
ZX-diagram interpretation of signed Pauli words and the carried completeness +
soundness fact (`backens`): two Pauli words have *equal* ZX-stabilizer diagrams
(modulo Backens' rewrite rules) iff there is a `Cat_PL_n` morphism between them.

The field `backens` is the **carried `Prop`** standing in for the unformalised
ZX-calculus completeness theorem; it is *not* an `axiom`, and the structure is
shown inhabited below. -/
structure StabilizerZXModel (n : ℕ) where
  /-- The type of (equivalence classes of) ZX-stabilizer diagrams. -/
  ZXObj : Type
  /-- Backens' interpretation of a signed Pauli word as a ZX-stabilizer diagram. -/
  zxInterp : PLObj n → ZXObj
  /-- Carried ZX-stabilizer completeness + soundness (Backens 2014): ZX-diagram
  equality coincides with `Cat_PL_n` morphism existence. -/
  backens : ∀ P Q : PLObj n, zxInterp P = zxInterp Q ↔ Nonempty (P ⟶ Q)

/-- **Target 10 — comparison with Backens 2014.**  Under any stabilizer ZX
model, ZX-stabilizer diagram equality (modulo Backens' rewrite rules) coincides
with the stabilizer-subspace interpretation `[[-]] : Cat_PL_n → Stab_n`.  Thus
`Cat_PL_n` is the common dagger-compact-closed core of the two semantics. -/
theorem zx_stabilizer_comparison {n : ℕ} (M : StabilizerZXModel n) (P Q : PLObj n) :
    M.zxInterp P = M.zxInterp Q ↔
      (interpret_functor n).obj P = (interpret_functor n).obj Q := by
  rw [M.backens, universality_categorical]

/-- **Consistency / trivial direction.**  A `StabilizerZXModel` exists: taking
the ZX interpretation to be our own stabilizer-subspace interpretation, the
carried Backens hypothesis is discharged by the unconditional
`universality_categorical`.  This shows the comparison is non-vacuous. -/
def stabModelOfInterpret (n : ℕ) : StabilizerZXModel n where
  ZXObj := StabN n
  zxInterp P := (interpret_functor n).obj P
  backens P Q := (universality_categorical P Q).symm

/-- The comparison is realised concretely by the stabilizer interpretation. -/
theorem zx_comparison_realised (n : ℕ) (P Q : PLObj n) :
    (stabModelOfInterpret n).zxInterp P = (stabModelOfInterpret n).zxInterp Q ↔
      Nonempty (P ⟶ Q) :=
  (stabModelOfInterpret n).backens P Q

end PLnCategory
end PauliLogic
