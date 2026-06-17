/-
# Universality (Selinger-2011 shape)

Selinger's completeness theorem (*Finite dimensional Hilbert spaces are
complete for dagger compact closed categories*, ENTCS 2011) says: an equation
between morphisms holds in the syntactic dagger compact closed category iff it
holds under interpretation in the semantic target.  For PL_n the analogous
statement is the soundness-plus-completeness package, lifted to the
categorical setting:

  a sequent is valid in `Stab_n` iff it is provable in `Cat_PL_n`
    (`universality`);
  a morphism `P ⟶ Q` exists in `Cat_PL_n` iff `P` and `Q` are mutually
    derivable (`hom_iff_mutual_derivable`);
  a morphism `P ⟶ Q` exists iff the two objects receive the same
    interpretation `[[P]] = [[Q]]` in `Stab_n` (`universality_categorical`).

Both directions use the already-mechanised `soundness` and `completeness_nonempty`
as black boxes.  Nothing is carried as a hypothesis; the universality is
unconditional.
-/

import StabilizerBW.PauliLogic.Categorical.Interpret
import StabilizerBW.PauliLogic.Completeness

open CategoryTheory

namespace PauliLogic
namespace PLnCategory

/-! ## Validity ↔ provability (the core universality) -/

/-- **Target 9 — universality (sequent level).**  A sequent is valid in the
stabilizer model iff it is provable in `PL_n`.  This is the categorical
universality: equality under interpretation in `Stab_n` ⇔ provability in
`Cat_PL_n`.  Both directions are the existing soundness/completeness theorems. -/
theorem universality {n : ℕ} {Γ : List (Pauli n)} {Q : Pauli n} :
    Valid Γ Q ↔ Nonempty (Derivation Γ Q) :=
  ⟨completeness_nonempty, fun ⟨d⟩ => soundness d⟩

/-! ## Membership and entailment helpers -/

theorem mem_V_singleton {n : ℕ} (R : Pauli n) (v : Vec n) :
    v ∈ V ([R] : List (Pauli n)) ↔ pauliAction R v = v := by
  simp [V]

theorem valid_iff_subset {n : ℕ} (P Q : Pauli n) :
    Valid ([P] : List (Pauli n)) Q ↔ V ([P] : List (Pauli n)) ⊆ V ([Q] : List (Pauli n)) := by
  unfold Valid
  constructor
  · intro h v hv
    rw [mem_V_singleton]
    exact h v hv
  · intro h v hv
    have := h hv
    rwa [mem_V_singleton] at this

theorem stabEquiv_iff_valid {n : ℕ} (P Q : Pauli n) :
    StabEquiv P Q ↔ (Valid ([P] : List (Pauli n)) Q ∧ Valid ([Q] : List (Pauli n)) P) := by
  rw [valid_iff_subset, valid_iff_subset, StabEquiv]
  constructor
  · intro h
    exact ⟨subset_of_eq h, subset_of_eq h.symm⟩
  · intro h
    exact Set.Subset.antisymm h.1 h.2

/-! ## Morphism-level Curry–Howard–Lambek bridge -/

/-- A morphism `P ⟶ Q` in `Cat_PL_n` exists iff `P` and `Q` are **mutually
derivable** in `PL_n`.  This is the Curry–Howard–Lambek bridge: hom-sets of the
categorical Lambek side are exactly (cut-equivalence classes of) derivations. -/
theorem hom_iff_mutual_derivable {n : ℕ} (P Q : PLObj n) :
    Nonempty (P ⟶ Q) ↔
      (Nonempty (Derivation ([P.word] : List (Pauli n)) Q.word) ∧
       Nonempty (Derivation ([Q.word] : List (Pauli n)) P.word)) := by
  constructor
  · rintro ⟨f⟩
    have h := (stabEquiv_iff_valid P.word Q.word).1 f.down
    exact ⟨completeness_nonempty h.1, completeness_nonempty h.2⟩
  · rintro ⟨⟨d₁⟩, ⟨d₂⟩⟩
    have h₁ : Valid ([P.word] : List (Pauli n)) Q.word := soundness d₁
    have h₂ : Valid ([Q.word] : List (Pauli n)) P.word := soundness d₂
    exact ⟨⟨(stabEquiv_iff_valid P.word Q.word).2 ⟨h₁, h₂⟩⟩⟩

/-- A morphism `P ⟶ Q` exists in `Cat_PL_n` iff the interpretation functor
identifies the two objects in `Stab_n`: `[[P]] = [[Q]]`. -/
theorem universality_categorical {n : ℕ} (P Q : PLObj n) :
    Nonempty (P ⟶ Q) ↔ (interpret_functor n).obj P = (interpret_functor n).obj Q := by
  rw [interpret_obj, interpret_obj]
  constructor
  · rintro ⟨f⟩
    exact congrArg Discrete.mk f.down
  · intro h
    exact ⟨⟨congrArg Discrete.as h⟩⟩

end PLnCategory
end PauliLogic
