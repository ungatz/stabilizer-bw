/-
# PauliLogic/Rules.lean

The sequent calculus `PL_n` for stabilizer entailment, as an inductive
datatype of derivations (Curry–Howard: a value of `Derivation Γ Q` IS a
proof of the sequent `Γ ⊢ Q`).

The rules of `PL_n`:
- `ax` : a literal of the ambient theory is derivable;
- `unitI` : `+I` is always derivable;
- `mul` : commuting `P`, `Q` give `P·Q` (the commutation precondition is a
 kernel-discharged hypothesis on the constructor);
- `cut` : the structural cut rule (eliminated in `CutElimination.lean`);
- `botElim` : ⊥-elimination (explosion): from a contradictory theory anything
 follows.

The falsum judgment `Γ ⊢ ⊥` (`BotDerivation`) has two introduction rules:
- `clash` : an anticommuting derivable pair is contradictory;
- `absurd` : a derivation of `-I` is contradictory.

`Derivation` and `BotDerivation` are mutually inductive because `botElim`
consumes a `BotDerivation`, while `clash`/`absurd` consume `Derivation`s.
-/

import StabilizerBW.PauliLogic.Syntax

namespace PauliLogic

/-- The negated identity `-I^⊗n`, the "falsum witness" Pauli word. -/
def pauliMinusI (n : ℕ) : Pauli n := (pauliI n).negate

mutual

/-- PL_n derivations. A value of type `Derivation Γ Q` is a proof of the
 sequent `Γ ⊢ Q`. The context `Γ` is an *index* (not a parameter) because
 the `cut` rule introduces a derivation over the extended context `P :: Γ`. -/
inductive Derivation {n : ℕ} : List (Pauli n) → Pauli n → Type
 /-- Axiom: any literal listed in `Γ` is derivable. -/
 | ax {Γ : List (Pauli n)} (k : Fin Γ.length) : Derivation Γ (Γ.get k)
 /-- Unit: `+I` is derivable. -/
 | unitI {Γ : List (Pauli n)} : Derivation Γ (pauliI n)
 /-- Multiplication: from `Γ ⊢ P` and `Γ ⊢ Q` with `P`, `Q` commuting,
 derive `Γ ⊢ P·Q`. -/
 | mul {Γ : List (Pauli n)} {P Q : Pauli n} (h : P.commutes Q = true)
 (dP : Derivation Γ P) (dQ : Derivation Γ Q) :
 Derivation Γ (Pauli.mul P Q h)
 /-- Cut: from `Γ ⊢ P` and `P :: Γ ⊢ Q`, derive `Γ ⊢ Q`. -/
 | cut {Γ : List (Pauli n)} {P Q : Pauli n}
 (dP : Derivation Γ P) (dQ : Derivation (P :: Γ) Q) :
 Derivation Γ Q
 /-- ⊥-elimination: from a contradictory theory, any literal is derivable. -/
 | botElim {Γ : List (Pauli n)} (Q : Pauli n) (d : BotDerivation Γ) :
 Derivation Γ Q

/-- Derivations of falsum (`⊥`): a theory is contradictory either via an
 anticommuting derivable pair (`clash`) or a derivation of `-I`
 (`absurd`). -/
inductive BotDerivation {n : ℕ} : List (Pauli n) → Type
 /-- Clash: an anticommuting derivable pair is contradictory. -/
 | clash {Γ : List (Pauli n)} {P Q : Pauli n} (h : P.commutes Q = false)
 (dP : Derivation Γ P) (dQ : Derivation Γ Q) : BotDerivation Γ
 /-- Absurd: a derivation of `-I` is contradictory. -/
 | absurd {Γ : List (Pauli n)} (d : Derivation Γ (pauliMinusI n)) :
 BotDerivation Γ

end

/-- Explosion as a combinator alias for the `botElim` rule. -/
def Derivation.exfalso {n : ℕ} {Γ : List (Pauli n)} (Q : Pauli n)
 (d : BotDerivation Γ) : Derivation Γ Q := Derivation.botElim Q d

end PauliLogic
