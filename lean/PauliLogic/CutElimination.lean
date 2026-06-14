/-
# PauliLogic/CutElimination.lean

Cut elimination for `PL_n` (the development Theorem 17.15, `thm:av-cut-elimination`).

Every `Derivation` normalises to a **cut-free** derivation. Cut elimination
is realised by the `splice` procedure: a cut against a lemma `P` is removed by
substituting the (already normalised) proof of `P` for every reference to the
cut formula in the body. Because `splice` is a *separate* function, `normalize`
is structurally recursive (no well-founded measure needed): on `cut dP dQ` it
recurses into the strictly smaller `dP`, `dQ` and then splices.

This file mirrors the Haskell reference's `normalize`: the proof IS the
Aaronson–Gottesman tableau reduction algorithm, each `mul` node being one row
multiplication.

Reference: `Proofs/T4_CutElimination.md`.
-/

import RequestProject.PauliLogic.Rules

namespace PauliLogic

mutual

/-- Cut-free PL_n derivations: the `cut` rule is absent. All other rules of
 `PL_n` (`ax`, `unitI`, `mul`, `botElim`) remain. -/
inductive CutFree {n : ℕ} : List (Pauli n) → Pauli n → Type
 | ax {Γ : List (Pauli n)} (k : Fin Γ.length) : CutFree Γ (Γ.get k)
 | unitI {Γ : List (Pauli n)} : CutFree Γ (pauliI n)
 | mul {Γ : List (Pauli n)} {P Q : Pauli n} (h : P.commutes Q = true)
 (dP : CutFree Γ P) (dQ : CutFree Γ Q) : CutFree Γ (Pauli.mul P Q h)
 | botElim {Γ : List (Pauli n)} (Q : Pauli n) (d : BotCutFree Γ) : CutFree Γ Q

/-- Cut-free falsum derivations. -/
inductive BotCutFree {n : ℕ} : List (Pauli n) → Type
 | clash {Γ : List (Pauli n)} {P Q : Pauli n} (h : P.commutes Q = false)
 (dP : CutFree Γ P) (dQ : CutFree Γ Q) : BotCutFree Γ
 | absurd {Γ : List (Pauli n)} (d : CutFree Γ (pauliMinusI n)) : BotCutFree Γ

end

/- Embed a cut-free derivation back into the general derivations. -/
mutual
def CutFree.toDerivation {n : ℕ} : {Γ : List (Pauli n)} → {Q : Pauli n} →
 CutFree Γ Q → Derivation Γ Q
 | _, _, .ax k => .ax k
 | _, _, .unitI => .unitI
 | _, _, .mul h dP dQ => .mul h dP.toDerivation dQ.toDerivation
 | _, _, .botElim Q d => .botElim Q d.toBotDerivation
def BotCutFree.toBotDerivation {n : ℕ} : {Γ : List (Pauli n)} →
 BotCutFree Γ → BotDerivation Γ
 | _, .clash h dP dQ => .clash h dP.toDerivation dQ.toDerivation
 | _, .absurd d => .absurd d.toDerivation
end

/- **Splice (the cut-removal step).** Given a cut-free proof `cfP` of the
 cut formula `P` over `Γ`, and a cut-free proof of `Q` over the extended
 context `P :: Γ`, produce a cut-free proof of `Q` over `Γ` by substituting
 `cfP` for every reference to the head formula. -/
mutual
def splice {n : ℕ} {Γ : List (Pauli n)} {P : Pauli n} (cfP : CutFree Γ P) :
 {Q : Pauli n} → CutFree (P :: Γ) Q → CutFree Γ Q
 | _, .ax k =>
 match k with
 | ⟨0, _⟩ => cfP
 | ⟨j + 1, hj⟩ => CutFree.ax ⟨j, by simpa using hj⟩
 | _, .unitI => .unitI
 | _, .mul h dA dB => .mul h (splice cfP dA) (splice cfP dB)
 | _, .botElim Q d => .botElim Q (spliceBot cfP d)
def spliceBot {n : ℕ} {Γ : List (Pauli n)} {P : Pauli n} (cfP : CutFree Γ P) :
 BotCutFree (P :: Γ) → BotCutFree Γ
 | .clash h dA dB => .clash h (splice cfP dA) (splice cfP dB)
 | .absurd d => .absurd (splice cfP d)
end

/- **Cut elimination, computational core** (the development Theorem 17.15): every
 `Derivation` normalises to a cut-free derivation with the same conclusion. -/
mutual
def normalize {n : ℕ} : {Γ : List (Pauli n)} → {Q : Pauli n} →
 Derivation Γ Q → CutFree Γ Q
 | _, _, .ax k => .ax k
 | _, _, .unitI => .unitI
 | _, _, .mul h dP dQ => .mul h (normalize dP) (normalize dQ)
 | _, _, .cut dP dQ => splice (normalize dP) (normalize dQ)
 | _, _, .botElim Q d => .botElim Q (normalizeBot d)
def normalizeBot {n : ℕ} : {Γ : List (Pauli n)} →
 BotDerivation Γ → BotCutFree Γ
 | _, .clash h dP dQ => .clash h (normalize dP) (normalize dQ)
 | _, .absurd d => .absurd (normalize d)
end

/-- Existence form of cut elimination (the kernel-level statement of
 Theorem 17.15): every entailment provable in `PL_n` is provable
 cut-free. -/
theorem cutElimination {n : ℕ} {Γ : List (Pauli n)} {Q : Pauli n}
 (d : Derivation Γ Q) : Nonempty (CutFree Γ Q) :=
 ⟨normalize d⟩

/-! ## Subset-product certificate (the corollary)

A cut-free derivation that does not invoke `botElim` is a *subset product* of
the theory: its conclusion's symplectic `(x, z)` vector is the XOR of the
selected generators' vectors. This is exactly the Aaronson–Gottesman tableau
row content (the sign is the order-dependent phase tracked by `phaseZ`).
-/

/-- XOR of the x-bits of the generators of `Γ` selected by `idxs`. -/
def selX {n : ℕ} {Γ : List (Pauli n)} (idxs : List (Fin Γ.length)) : Fin n → Bool :=
 fun j => idxs.foldr (fun k acc => xor ((Γ.get k).xs j) acc) false

/-- XOR of the z-bits of the generators of `Γ` selected by `idxs`. -/
def selZ {n : ℕ} {Γ : List (Pauli n)} (idxs : List (Fin Γ.length)) : Fin n → Bool :=
 fun j => idxs.foldr (fun k acc => xor ((Γ.get k).zs j) acc) false

theorem selX_append {n : ℕ} {Γ : List (Pauli n)} (A B : List (Fin Γ.length)) :
 selX (A ++ B) = fun j => xor (selX A j) (selX B j) := by
 funext j;
 induction A <;> simp_all +decide [ selX ]

theorem selZ_append {n : ℕ} {Γ : List (Pauli n)} (A B : List (Fin Γ.length)) :
 selZ (A ++ B) = fun j => xor (selZ A j) (selZ B j) := by
 funext j; induction A <;> simp_all +decide [ selZ ] ;

/-- A subset-product certificate for `Γ ⊢ Q`: a list of generator indices
 whose XOR-product reproduces `Q`'s symplectic `(x, z)` vector. -/
def Certificate {n : ℕ} (Γ : List (Pauli n)) (Q : Pauli n) : Type :=
 { idxs : List (Fin Γ.length) // selX idxs = Q.xs ∧ selZ idxs = Q.zs }

/-- **Corollary (subset-product certificate).** Every cut-free derivation
 either yields a subset-product certificate (the multiset of generators
 multiplied) or exhibits the theory as contradictory. -/
def cutFree_to_certificate {n : ℕ} : {Γ : List (Pauli n)} → {Q : Pauli n} →
 CutFree Γ Q → Certificate Γ Q ⊕ BotCutFree Γ
 | _, _, .ax k =>
 Sum.inl ⟨[k], by
 constructor <;> funext j <;> simp [selX, selZ]⟩
 | _, _, .unitI =>
 Sum.inl ⟨[], by constructor <;> funext j <;> rfl⟩
 | _, _, .mul h dA dB =>
 match cutFree_to_certificate dA, cutFree_to_certificate dB with
 | Sum.inl ⟨idxsA, hA⟩, Sum.inl ⟨idxsB, hB⟩ =>
 Sum.inl ⟨idxsA ++ idxsB, by
 refine ⟨?_, ?_⟩
 · funext j
 rw [selX_append]
 simp only [Pauli.mul, mulXs]
 rw [show (selX idxsA) = _ from hA.1, show (selX idxsB) = _ from hB.1]
 · funext j
 rw [selZ_append]
 simp only [Pauli.mul, mulZs]
 rw [show (selZ idxsA) = _ from hA.2, show (selZ idxsB) = _ from hB.2]⟩
 | Sum.inr b, _ => Sum.inr b
 | _, Sum.inr b => Sum.inr b
 | _, _, .botElim _ d => Sum.inr d

end PauliLogic