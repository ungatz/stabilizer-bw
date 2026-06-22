import StabilizerBW.Grade.EnumeratorBound.CaseN4.ConcreteInstance
import StabilizerBW.Compilation.ContextGame

/-!
# MenuBandwidthN4 / CrossValidation — T5: matching the n=2 (CHSH) and n=3 (9-Pauli) cases

The only kernel-checked Bandwidth instances prior to this development are the n=2
CHSH facet (`MenuBridge.CHSH`) and the n=3 9-Pauli Clifford-menu facet
(`Compilation.ContextGame`).  This file cross-validates the n=4 development
against both.

## Main results

* `cross_chsh_N`, `cross_chsh_gap` — re-export of the n=2 CHSH constants
  `N = 8` and gap `(√2 − 1)/4`.
* `cliffordFacet3` — the n=3 all-ones 9-Pauli facet (`coeff = 1`, bound `3`),
  with `cliffordFacet3_S = 9`, `cliffordFacet3_N = 18`.
* `n3_gap` — the n=3 9-Pauli magic-state bandwidth gap is `(√3 − 1)/6`.
* `cross_n3_contextgame` — that gap equals `p_Q − p_S` of
  `Compilation.ContextGame` (`CliffordMenu.gap_pos`), the established n=3 value.
* `n4_matches_n3` — the n=4 magic-state gap (`concrete_gap_n4`) equals the n=3
  gap `(√3 − 1)/6`, confirming the closed-form scaling across the menu tower.
-/

open scoped BigOperators

namespace CliffordMenuN4

/-! ## n = 2 : the CHSH facet -/

/-- Cross-check: the CHSH game normalisation is `N = 8`. -/
theorem cross_chsh_N : MenuBridge.CHSH.chshFacet.N = 8 := MenuBridge.CHSH.chsh_N

/-- Cross-check: the CHSH Tsirelson gap is `(√2 − 1)/4`. -/
theorem cross_chsh_gap :
    MenuBridge.CHSH.chshFacet.quantumValue MenuBridge.CHSH.tsirelsonProfile
      - MenuBridge.CHSH.chshFacet.classicalValue = (Real.sqrt 2 - 1) / 4 :=
  MenuBridge.CHSH.chsh_gap_tsirelson

/-! ## n = 3 : the 9-Pauli Clifford-menu facet -/

/-- The n=3 all-ones 9-Pauli Clifford-menu facet: `coeff = 1`, bound `3`. -/
def cliffordFacet3 : MenuBridge.Facet 9 where
  coeff := fun _ => 1
  classicalBound := 3

/-- `S = ∑_k |α_k| = 9`. -/
theorem cliffordFacet3_S : cliffordFacet3.S = 9 := by
  unfold MenuBridge.Facet.S cliffordFacet3; simp

/-- `N = 2S = 18`. -/
theorem cliffordFacet3_N : cliffordFacet3.N = 18 := by
  unfold MenuBridge.Facet.N; rw [cliffordFacet3_S]; norm_num

/-- The n=3 magic profile `|H⟩^{⊗3}` lifted to the nine observables (all `1/√3`). -/
noncomputable def magicLift3 : Fin 9 → ℝ := fun _ => 1 / Real.sqrt 3

/-- The n=3 9-Pauli facet functional on `|H⟩^{⊗3}` is `9/√3 = 3√3`. -/
theorem cliffordFacet3_L_magic :
    cliffordFacet3.L magicLift3 = 3 * Real.sqrt 3 := by
  unfold MenuBridge.Facet.L magicLift3
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hco : ∀ k, cliffordFacet3.coeff k = 1 := fun _ => rfl
  simp only [hco, one_mul]
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  nlinarith [hsq]

/-- **T5: the n=3 9-Pauli magic-state bandwidth gap is `(√3 − 1)/6`.** -/
theorem n3_gap :
    cliffordFacet3.quantumValue magicLift3 - cliffordFacet3.classicalValue
      = (Real.sqrt 3 - 1) / 6 := by
  rw [MenuBridge.Facet.gap_eq]
  unfold MenuBridge.Facet.violation
  rw [cliffordFacet3_L_magic, cliffordFacet3_N]
  show (3 * Real.sqrt 3 - cliffordFacet3.classicalBound) / 18 = _
  unfold cliffordFacet3
  ring

/-- **T5: cross-validation against `Compilation.ContextGame`.**  The n=3 9-Pauli
gap equals `p_Q − p_S` of the established n=3 contextuality game. -/
theorem cross_n3_contextgame :
    cliffordFacet3.quantumValue magicLift3 - cliffordFacet3.classicalValue
      = CliffordMenu.p_Q - CliffordMenu.p_S := by
  rw [n3_gap]
  unfold CliffordMenu.p_Q CliffordMenu.p_S
  ring

/-! ## n = 4 matches n = 3 -/

/-- **T5: the n=4 magic-state gap equals the n=3 gap `(√3 − 1)/6`**, confirming the
closed-form bandwidth scaling across the menu tower. -/
theorem n4_matches_n3 :
    facetGap cliffordFacet4 magicLift4
      = cliffordFacet3.quantumValue magicLift3 - cliffordFacet3.classicalValue := by
  rw [concrete_gap_n4, n3_gap]

end CliffordMenuN4
