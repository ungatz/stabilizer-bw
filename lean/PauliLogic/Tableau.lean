/-
# PauliLogic/Tableau.lean

Tableaux (stabilizer presentations) and the Aaronson–Gottesman row-reduction
algorithm, plus the algebraic core of measurement-as-oracle-cut
(the development Proposition 17.16, `prop:av-measurement-cut`).

A `Tableau n` is a list of pairwise-commuting Pauli words. The central
correspondences:

- **`tableau_step_eq_mul`**: one Aaronson–Gottesman row multiplication of rows
 `i, j` IS exactly one `PL_n` `mul` step.
- **`Tableau.rowMul`**: performing that row multiplication preserves the
 pairwise-commuting invariant — the AG tableau operation is well defined.
- **measurement (oracle cut + repair)**: `repair_commutes_Q` is the heart of
 Proposition 17.16: an anticommuting generator, multiplied through the chosen
 pivot `g₁`, is *repaired* to commute with the measured literal `Q`; the fresh
 axiom `Q` (with the effect-chosen sign) then commutes with the whole repaired
 theory.

Reference: `Proofs/T5_Measurement.md`, and the Haskell `measure` function.
-/

import RequestProject.PauliLogic.Syntax

namespace PauliLogic

/-- Every Pauli word commutes with itself. -/
theorem Pauli.commutes_self {n : ℕ} (p : Pauli n) : p.commutes p = true := by
 unfold Pauli.commutes
 have h : (crossZX p p + crossZX p p) % 2 = 0 := by omega
 rw [h]; rfl

/-- `commutes` ignores the global sign. -/
@[simp] theorem Pauli.commutes_withSign {n : ℕ} (p q : Pauli n) (s : Bool) :
 ({ p with sign := s } : Pauli n).commutes q = p.commutes q := rfl

/-- A tableau: a stabilizer presentation by pairwise-commuting generators. -/
structure Tableau (n : ℕ) where
 generators : List (Pauli n)
 pairwise_commute : ∀ p ∈ generators, ∀ q ∈ generators, p.commutes q = true

namespace Tableau

/-- Conversion from a list of generators (carrying the commuting proof). -/
def fromGenerators {n : ℕ} (gens : List (Pauli n))
 (h : ∀ p ∈ gens, ∀ q ∈ gens, p.commutes q = true) : Tableau n := ⟨gens, h⟩

/-- The underlying generator list. -/
def toList {n : ℕ} (T : Tableau n) : List (Pauli n) := T.generators

/-- The result of one AG row multiplication of rows `i` and `j`: the literal
 placed in row `i`. -/
def rowMulEntry {n : ℕ} (T : Tableau n) (i j : Fin T.generators.length)
 (hij : (T.generators.get i).commutes (T.generators.get j) = true) : Pauli n :=
 Pauli.mul (T.generators.get i) (T.generators.get j) hij

/-- **One Aaronson–Gottesman row multiplication IS one `PL_n` `mul` step.** -/
theorem tableau_step_eq_mul {n : ℕ} (T : Tableau n) (i j : Fin T.generators.length)
 (hij : (T.generators.get i).commutes (T.generators.get j) = true) :
 T.rowMulEntry i j hij
 = Pauli.mul (T.generators.get i) (T.generators.get j) hij := rfl

/-
The AG row operation preserves the pairwise-commuting invariant.
-/
theorem rowMul_pairwise {n : ℕ} (T : Tableau n) (i j : Fin T.generators.length)
 (hij : (T.generators.get i).commutes (T.generators.get j) = true) :
 ∀ p ∈ T.generators.set i (Pauli.mul (T.generators.get i) (T.generators.get j) hij),
 ∀ q ∈ T.generators.set i (Pauli.mul (T.generators.get i) (T.generators.get j) hij),
 p.commutes q = true := by
 grind +suggestions

/-- **The AG row operation preserves the tableau invariant.** Replacing row `i`
 by `gᵢ · gⱼ` keeps the generators pairwise commuting (so the operation is a
 well-defined map on tableaux, witnessing that tableau reduction stays within
 the stabilizer presentation). -/
def rowMul {n : ℕ} (T : Tableau n) (i j : Fin T.generators.length)
 (hij : (T.generators.get i).commutes (T.generators.get j) = true) : Tableau n where
 generators :=
 T.generators.set i (Pauli.mul (T.generators.get i) (T.generators.get j) hij)
 pairwise_commute := rowMul_pairwise T i j hij

end Tableau

/-! ## Measurement as an oracle cut (Proposition 17.16) -/

/-
**Repair lemma — the heart of measurement-as-oracle-cut.** If a generator
 `g` anticommutes with the measured literal `Q`, multiplying it through the
 pivot `g₁` (which also anticommutes with `Q`) *repairs* it: the product
 commutes with `Q`. This is the "repair commutativity by row multiplications"
 clause of Proposition 17.16.
-/
theorem repair_commutes_Q {n : ℕ} (Q g1 g : Pauli n)
 (hg1Q : g1.commutes Q = false) (hgQ : g.commutes Q = false)
 (hgg1 : g.commutes g1 = true) :
 (Pauli.mul g g1 hgg1).commutes Q = true := by
 unfold Pauli.commutes at *;
 have h_split : (∑ j, ((g.zs j ^^ g1.zs j) && Q.xs j).toNat) % 2 = ((∑ j, (g.zs j && Q.xs j).toNat) + (∑ j, (g1.zs j && Q.xs j).toNat)) % 2 := by
 rw [ ← Finset.sum_add_distrib ] ; exact Nat.ModEq.sum ( fun i _ => by cases g.zs i <;> cases g1.zs i <;> cases Q.xs i <;> rfl ) ;
 have h_split' : (∑ j, (Q.zs j && (g.xs j ^^ g1.xs j)).toNat) % 2 = ((∑ j, (Q.zs j && g.xs j).toNat) + (∑ j, (Q.zs j && g1.xs j).toNat)) % 2 := by
 rw [ ← Finset.sum_add_distrib ] ; exact Nat.ModEq.sum ( fun i _ => by cases Q.zs i <;> cases g.xs i <;> cases g1.xs i <;> rfl ) ;
 unfold crossZX at *; simp_all +decide [ Pauli.mul ] ;
 unfold mulZs mulXs; omega;

/-- The fresh axiom `Q` (with the effect-chosen sign `r`) commutes with every
 repaired generator: a generator already commuting with `Q` is kept; one that
 anticommutes is repaired through `g₁` (`repair_commutes_Q`). In both cases
 the post-measurement literal `{Q with sign := r}` commutes with the result.
 This packages the post-measurement commutativity of Proposition 17.16. -/
theorem postMeasure_commutes {n : ℕ} (Q g1 g : Pauli n) (r : Bool)
 (hg1Q : g1.commutes Q = false) (hgg1 : g.commutes g1 = true) :
 (if g.commutes Q then g else Pauli.mul g g1 hgg1).commutes
 ({ Q with sign := r } : Pauli n) = true := by
 rw [Pauli.commutes_symm, Pauli.commutes_withSign]
 by_cases hgQ : g.commutes Q = true
 · simp only [hgQ, if_true]; rw [Pauli.commutes_symm]; exact hgQ
 · simp only [Bool.not_eq_true] at hgQ
 simp only [hgQ, Bool.false_eq_true, if_false]
 rw [Pauli.commutes_symm]
 exact repair_commutes_Q Q g1 g hg1Q hgQ hgg1

end PauliLogic