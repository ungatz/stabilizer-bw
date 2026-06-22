import StabilizerBW.T1A.ZpowFacts
import StabilizerBW.Roots.MoebiusGradeClosedFormAllN

/-!
# T1A — leaf reconstruction and the Möbius factorisation for linear phases

`ofLeaves n f : BWVec n` is the depth-`n` Barnes–Wall tree whose leaf at the
Boolean point `b` is `f b` (the inverse of `leafB`).  We instantiate it at the
phase vector of a **linear phase polynomial** `P = c₀ + Σᵢ cᵢ xᵢ`, whose leaf at
the Boolean point with support `U` is `ζ₈^(c₀ + Σ_{i∈U} cᵢ)`.

The headline of this file is the **Möbius factorisation**
```
  m_U(D_P) = ζ₈^{c₀} · ∏_{i∈U} (ζ₈^{cᵢ} − 1),
```
which (combined with `ZpowFacts.factor_eq`) makes the `λ`-valuation of every
Möbius coefficient an explicit product of per-coefficient contributions.
-/

namespace T1A

open Roots Roots.MoebiusClosed Roots.MoebiusAllN Z8
open scoped Classical
open Finset

/-- Reconstruct a `BWVec n` from its leaf function (inverse of `leafB`). -/
def ofLeaves : (n : ℕ) → ((Fin n → Bool) → Z8) → BWVec n
  | 0, f => f Fin.elim0
  | n + 1, f =>
      (ofLeaves n (fun b => f (Fin.snoc b false)),
       ofLeaves n (fun b => f (Fin.snoc b true)))

/-
`ofLeaves` is a section of `leafB`.
-/
theorem leafB_ofLeaves : ∀ (n : ℕ) (f : (Fin n → Bool) → Z8) (b : Fin n → Bool),
    leafB n (ofLeaves n f) b = f b := by
  intro n;
  have h_ind : ∀ (n : ℕ) (f : (Fin n → Bool) → Z8) (b : Fin n → Bool), leafB n (ofLeaves n f) b = f b := by
    intro n
    induction' n with n ih;
    · exact fun f b => by rw [ show b = Fin.elim0 from Subsingleton.elim _ _ ] ; rfl;
    · intro f b; by_cases h : b ( Fin.last n ) <;> simp +decide [ *, leafB, ofLeaves ] ;
      · congr ; ext i ; cases i using Fin.lastCases <;> aesop;
      · congr with i ; induction i using Fin.lastCases <;> aesop
  generalize_proofs at *;
  exact h_ind n

/-! ## Linear phase polynomials -/

/-- A linear (degree `≤ 1`) phase polynomial on `m` qubits: a constant `c₀` and
linear coefficients `cᵢ`, all in `ℤ/8`. -/
abbrev LinPhase (m : ℕ) : Type := ZMod 8 × (Fin m → ZMod 8)

/-- The phase `P(b) = c₀ + Σ_{i : bᵢ} cᵢ` of a linear polynomial at a Boolean point. -/
def linEval {m : ℕ} (P : LinPhase m) (b : Fin m → Bool) : ZMod 8 :=
  P.1 + ∑ i, if b i then P.2 i else 0

/-- The leaf value `ζ₈^{P(b)}`. -/
def linLeaf {m : ℕ} (P : LinPhase m) (b : Fin m → Bool) : Z8 := zpow8 (linEval P b)

/-- The Barnes–Wall phase vector `D_P = (ζ₈^{P(b)})_b` of a linear phase polynomial. -/
def toBWVec {m : ℕ} (P : LinPhase m) : BWVec m := ofLeaves m (linLeaf P)

/-- `zpow8` turns a finite sum into a finite product. -/
theorem zpow8_sum {m : ℕ} (s : Finset (Fin m)) (f : Fin m → ZMod 8) :
    zpow8 (∑ i ∈ s, f i) = ∏ i ∈ s, zpow8 (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow8_add, ih]

/-- The leaf value of `D_P` at the Boolean point with support `U`. -/
theorem leafVal_toBWVec {m : ℕ} (P : LinPhase m) (U : Finset (Fin m)) :
    leafVal m (toBWVec P) U = zpow8 (P.1 + ∑ i ∈ U, P.2 i) := by
  unfold leafVal toBWVec
  rw [leafB_ofLeaves]
  unfold linLeaf linEval
  congr 2
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp

/-- The leaf value factorises multiplicatively over the support. -/
theorem leafVal_toBWVec_prod {m : ℕ} (P : LinPhase m) (U : Finset (Fin m)) :
    leafVal m (toBWVec P) U = zpow8 P.1 * ∏ i ∈ U, zpow8 (P.2 i) := by
  rw [leafVal_toBWVec, zpow8_add, zpow8_sum]

/-
**Möbius factorisation for linear phases.**
`m_U(D_P) = ζ₈^{c₀} · ∏_{i∈U} (ζ₈^{cᵢ} − 1)`.
-/
theorem mob_lin_eq {m : ℕ} (P : LinPhase m) (U : Finset (Fin m)) :
    mob (leafVal m (toBWVec P)) U
      = zpow8 P.1 * ∏ i ∈ U, (zpow8 (P.2 i) - 1) := by
  simp_all +decide [ mob ];
  rw [ Finset.prod_sub ];
  rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_bij ( fun V hV => U \ V ) _ _ _ _ <;> simp_all +decide [ Finset.card_sdiff ] ;
  · intro a₁ ha₁ a₂ ha₂ h; rw [ ← Finset.sdiff_sdiff_eq_self ha₁, h, Finset.sdiff_sdiff_eq_self ha₂ ] ;
  · exact fun b hb => ⟨ U \ b, by aesop_cat, by aesop_cat ⟩;
  · intro a ha; rw [ Finset.inter_eq_left.mpr ha ] ; rw [ leafVal_toBWVec_prod ] ; ring;

end T1A