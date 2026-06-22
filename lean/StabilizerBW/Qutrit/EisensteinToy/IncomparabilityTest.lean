import StabilizerBW.Qutrit.EisensteinToy.TCountTest

/-!
# T7 — TEST 4: the cT vs CCZ incomparability

Layer 65's qubit witnesses (`GradeAuditIncomparable`) compare the Barnes–Wall grade against the
Jiang–Wang nullity on the **controlled-`T`** gate `cT` and the **doubly-controlled-`Z`** gate
`CCZ`, finding them order-incomparable.  Both diagnostic gates are non-Clifford and carry genuine
`T`-type phases.

At `d = 3` the analogous diagnostic gates are the controlled-`T₃` and the qutrit Toffoli, whose
non-Clifford phases are again `9`th roots of unity `ζ₉`.  By the structural obstruction of
`TCountTest.lean` (`no_isPrimitiveRoot_nine`), **these phases are not Eisenstein integers**, so
the diagnostic gates are *not representable* over the `ℤ[ω]` lattice — and the qubit
incomparability comparison has no faithful `ℤ[ω]` analogue.

We make this precise:

* `ninth_root_phase_not_representable` — a diagonal entry of order `9` (the controlled-`T₃`
  phase) cannot occur over `ℤ[ω]`: any `c` with `c⁹ = 1` already satisfies `c³ = 1`.

We then record the data that *is* available over `ℤ[ω]` — the grades of the representable
diagonal gates — exhibiting a second qutrit-specific deviation:

* `clifford_phase_has_nonzero_grade` — the Clifford phase `-1` (`diag(1, -1)`) has grade `1`,
  whereas the order-`3` phase `ω` (`diag(1, ω)`) has grade `0`.  In the qubit case *all* Clifford
  phases are grade-`0` automorphisms; over the Eisenstein lattice the Clifford phase `-1` is not.

**Conclusion: TEST 4 fails to reproduce.**  The incomparability comparison is vacuous over
`ℤ[ω]` (the diagnostic `T`-bearing gates are unrepresentable), and the representable phases reveal
that the Eisenstein lattice does not even keep the qutrit Clifford phases grade-`0`.

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace QutritEis
open Eis

/-- **The controlled-`T₃` phase is unrepresentable over `ℤ[ω]`.** Any diagonal entry `c` of order
dividing `9` already has order dividing `3`; in particular no genuine order-`9` (controlled-`T₃`)
phase exists among the Eisenstein integers. -/
theorem ninth_root_phase_not_representable (c : Eis) (h : c ^ 9 = 1) : c ^ 3 = 1 :=
  ninth_root_is_cube_root c h

/-- **The diagnostic gates carry no Eisenstein representation.** There is no Eisenstein integer
serving as a primitive `9`th-root controlled-`T₃` phase. -/
theorem diagnostic_gates_unrepresentable : ¬ ∃ z : Eis, IsPrimitiveRoot z 9 :=
  no_isPrimitiveRoot_nine

/-- **Second qutrit-specific deviation:** over the Eisenstein lattice the Clifford phase `-1` has
grade `1` while the order-`3` phase `ω` has grade `0`.  (In the qubit case both would be
grade `0`.) -/
theorem clifford_phase_has_nonzero_grade :
    gradeEMat diagOmega = 0 ∧ gradeEMat diagNegOne = 1 :=
  ⟨gradeEMat_diag_omega, gradeEMat_diag_negOne⟩

end QutritEis
