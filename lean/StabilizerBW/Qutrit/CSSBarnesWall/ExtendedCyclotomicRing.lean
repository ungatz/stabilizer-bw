import Mathlib
import StabilizerBW.Qutrit.EisensteinToy.TCountTest

/-!
# T5 — The extended Clifford-phase ring `ℤ[ζ₉]` and the Howard–Vala T-gate

Layer 90's TEST 3 found a genuine obstruction: the Howard–Vala qutrit T-gate
`T₃ = diag(1, ζ₉, ζ₉⁴)` has phases that are **primitive 9th roots of unity**,
and *there is no primitive 9th root of unity in the Eisenstein integers*
`ℤ[ω] = ℤ[ζ₃]` (`QutritEisensteinAnalogue.TCountTest.no_isPrimitiveRoot_nine`).
So `T₃` is *not* representable over the base cyclotomic ring `ℤ[ζ₃]`.

The PLAYBOOK §14 design pattern for prime-`d` cyclotomic-lattice analogues is to
pass to the **extended cyclotomic ring** `ℤ[ζ_{d²}]`.  For `d = 3` this is
`ℤ[ζ₉]`.  Here we set up

  `QutritCliffordPhaseRing := CyclotomicRing 9 ℤ ℚ`   (`= ℤ[ζ₉]`),

which carries a primitive 9th root of unity `ζ₉` by Mathlib's cyclotomic
machinery.  Over this ring the Howard–Vala T-gate phases `1, ζ₉, ζ₉⁴` are honest
elements (powers of `ζ₉`), so **`T₃` IS representable** — refining TEST 3:
the obstruction was specific to the *base* ring `ℤ[ζ₃]`; in the extended ring
`ℤ[ζ₉]` it disappears, exactly as the design pattern predicts.

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace QutritCSSBarnesWall

open Polynomial

/-- The extended cyclotomic ring `ℤ[ζ₉]` (the qutrit Clifford+T phase ring). -/
noncomputable abbrev QutritCliffordPhaseRing : Type := CyclotomicRing 9 ℤ ℚ

@[inherit_doc] notation "ℤζ₉" => QutritCliffordPhaseRing

/-- A primitive 9th root of unity in `ℤ[ζ₉]`. -/
noncomputable def zeta9 : ℤζ₉ := IsCyclotomicExtension.zeta 9 ℤ ℤζ₉

/-- `ζ₉` is a primitive 9th root of unity. -/
theorem zeta9_isPrimitiveRoot : IsPrimitiveRoot zeta9 9 :=
  IsCyclotomicExtension.zeta_spec 9 ℤ ℤζ₉

/-- The diagonal of the Howard–Vala qutrit T-gate `T₃ = diag(1, ζ₉, ζ₉⁴)`,
over `ℤ[ζ₉]`. -/
noncomputable def T3phase : Fin 3 → ℤζ₉
  | 0 => 1
  | 1 => zeta9
  | 2 => zeta9 ^ 4

/-- `ζ₉` has order exactly `9`: the T-gate is genuinely non-Clifford
(the Clifford phases have order dividing `3`). -/
theorem zeta9_orderOf : orderOf zeta9 = 9 := zeta9_isPrimitiveRoot.eq_orderOf.symm

/-- There **is** a primitive 9th root of unity in the extended ring `ℤ[ζ₉]`. -/
theorem exists_primitiveRoot_nine_extended : ∃ z : ℤζ₉, IsPrimitiveRoot z 9 :=
  ⟨zeta9, zeta9_isPrimitiveRoot⟩

/-- **TEST 3 refined (headline): the Howard–Vala T-gate IS representable over the
extended ring `ℤ[ζ₉]`.**

* In the extended ring there is a primitive 9th root of unity `z = ζ₉`, and the
  three T-gate phases `1, ζ₉, ζ₉⁴` are exactly `z⁰, z¹, z⁴` — so
  `T₃ = diag(1, ζ₉, ζ₉⁴)` is a well-defined diagonal operator over `ℤ[ζ₉]`.
* In the base Eisenstein ring `ℤ[ζ₃] = ℤ[ω]` there is **no** primitive 9th root
  of unity, so `T₃` is not representable there.

Thus the TEST 3 obstruction is specific to the base ring; passing to the
extended cyclotomic ring `ℤ[ζ₉]` removes it, as the prime-`d` design pattern
predicts. -/
theorem qutrit_T_gate_representable :
    (∃ z : ℤζ₉, IsPrimitiveRoot z 9 ∧
      T3phase 0 = 1 ∧ T3phase 1 = z ∧ T3phase 2 = z ^ 4) ∧
    ¬ (∃ z : QutritEis.Eis, IsPrimitiveRoot z 9) := by
  refine ⟨⟨zeta9, zeta9_isPrimitiveRoot, ?_, ?_, ?_⟩, QutritEis.no_isPrimitiveRoot_nine⟩
  · rfl
  · rfl
  · rfl

end QutritCSSBarnesWall
