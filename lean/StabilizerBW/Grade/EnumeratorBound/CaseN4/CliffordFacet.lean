import StabilizerBW.MenuBridge
import StabilizerBW.Grade.EnumeratorBound.CaseN4.CliffordMenuN4

/-!
# MenuBandwidthN4 / CliffordFacet — T2: the all-ones facet at `n = 4`

We package the four-qubit all-ones Clifford-menu facet as a `MenuBridge.Facet 12`
(twelve single-qubit Pauli observables, coefficient `1` on each, classical bound
`4`) and connect it to the convex-geometry development of `CliffordMenuN4`.

## Main results

* `cliffordFacet4` — the `MenuBridge.Facet 12` with `coeff = 1`, `classicalBound = 4`.
* `cliffordFacet4_S` — `S = ∑_k |α_k| = 12`.
* `cliffordFacet4_N` — `N = 2S = 24`.
* `idx12` — the canonical equivalence `Idx4 ≃ Fin 12` packaging the twelve
  observables, with `cliffordFacet4_L_eq_facetValue` identifying the facet
  functional `L` with the menu functional `W` of `CliffordMenuN4`.
* `cliffordFacet4_violation_le_zero_of_stab` — every four-qubit stabilizer
  profile has nonpositive facet violation (the operational form of the proved
  bound `octahedron_facet_stab_bound4`).
-/

open scoped BigOperators

namespace CliffordMenuN4

/-- The canonical indexing equivalence `Idx4 = Fin 4 × Fin 3 ≃ Fin 12`. -/
def idx12 : Idx4 ≃ Fin 12 := finProdFinEquiv

/-- **T2: the all-ones facet at the 4-qubit Clifford menu.**  Coefficient `1` on
each of the twelve single-qubit Pauli observables, classical bound `C = 4`. -/
def cliffordFacet4 : MenuBridge.Facet 12 where
  coeff := fun _ => 1
  classicalBound := 4

/-- **T2: `S = ∑_k |α_k| = 12`.** -/
theorem cliffordFacet4_S : cliffordFacet4.S = 12 := by
  unfold MenuBridge.Facet.S cliffordFacet4
  simp

/-- **T2: `N = 2S = 24`.** -/
theorem cliffordFacet4_N : cliffordFacet4.N = 24 := by
  unfold MenuBridge.Facet.N
  rw [cliffordFacet4_S]; norm_num

/-- The half-width is positive, so the facet is nondegenerate. -/
theorem cliffordFacet4_S_pos : 0 < cliffordFacet4.S := by
  rw [cliffordFacet4_S]; norm_num

/-- **T2 (functional identification):** the facet functional `L` evaluated on the
profile lifted through `idx12` equals the menu functional `W = Σ_{q,a} ⟨P^a_q⟩`. -/
theorem cliffordFacet4_L_eq_facetValue (E : Idx4 → ℝ) :
    cliffordFacet4.L (fun k => E (idx12.symm k)) = facetValue coeffOne E := by
  unfold MenuBridge.Facet.L cliffordFacet4 facetValue coeffOne
  rw [← Equiv.sum_comp idx12 (fun k => (1 : ℝ) * E (idx12.symm k))]
  simp

/-- The facet violation of the lifted profile equals the menu violation
`W(E) − 4`. -/
theorem cliffordFacet4_violation_eq (E : Idx4 → ℝ) :
    cliffordFacet4.violation (fun k => E (idx12.symm k))
      = facetValue coeffOne E - menuC := by
  unfold MenuBridge.Facet.violation
  rw [cliffordFacet4_L_eq_facetValue]
  simp [cliffordFacet4, menuC]

/-- **T2 (operational stabilizer bound):** every four-qubit stabilizer profile has
nonpositive facet violation — the `Facet`-level form of
`octahedron_facet_stab_bound4`. -/
theorem cliffordFacet4_violation_le_zero_of_stab {E : Idx4 → ℝ}
    (he : InPolytope menuVertices E) :
    cliffordFacet4.violation (fun k => E (idx12.symm k)) ≤ 0 := by
  rw [cliffordFacet4_violation_eq]
  have := octahedron_facet_stab_bound4 he
  simp only [menuC] at this ⊢
  linarith

end CliffordMenuN4
