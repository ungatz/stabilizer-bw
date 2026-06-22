import StabilizerBW.SqrtPi.Z8Ring

/-!
# Catalytic embedding and the level-raising grade-doubling engine

The conjectured catalytic-embedding grade preservation `Γ(g) = 2g` (CHKRS SI Def. S12 / Lemma S13,
specialised to `Φ₃ : Π₃ → Π₂`) is driven by the **level-raising identity**: the cyclotomic prime
at level `2` (`λ₂ = 1 - ζ₄ = 1 - i`) is an associate of the *square* of the level-3 prime
(`λ₃ = 1 - ζ₈`). Equivalently `(1 + i)` (an associate of `λ₂`) equals `λ₃²` up to a unit.

This is exactly the mechanism by which "one ramified step per square root" doubles the lattice grade:
a factor `λ₂` at level 2 corresponds to a factor `λ₃²` at level 3, so a grade-`g` operator
acquires grade `2g` under the cyclotomic doubling `ζ₈ ↦ ζ₄`.

Here we kernel-prove this core algebraic engine. The full categorical statement (the grade of
`⟦Φ₃(a)⟧` with respect to the level-2 Barnes–Wall lattice equals `2·g₃(a)`) additionally requires the
level-2 ring `ℤ[i]`, the level-2 lattice, and the explicit catalytic embedding `Φ₃`; it is the
remaining bridge documented in `Proofs/T3_CatalystGrade.md`.
-/

namespace Pi3
namespace Catalyst
open Z8

/-- **T3 (level-raising engine).** The square of the level-3 prime `λ₃ = 1 - ζ₈` is an associate of
`(1 + i)` (an associate of the level-2 prime `λ₂ = 1 - ζ₄`): `λ₃² = u · (1+i)` for a unit `u`.
This is the algebraic mechanism behind the conjectured grade-doubling `Γ(g) = 2g`. -/
theorem levelRaising : ∃ u : Z8, IsUnit u ∧ lam ^ 2 = u * onePlusI :=
  ⟨uu, IsUnit.of_mul_eq_one uuInv uu_unit, by rw [pow_two, lamsq_eq]⟩

/-- The level-2 prime `λ₂ = 1 - ζ₄ = 1 - i` is an associate of `1 + i`. -/
theorem levelTwo_prime_assoc : ∃ u : Z8, IsUnit u ∧ (1 - imag) = u * onePlusI :=
  ⟨⟨0, 0, -1, 0⟩, IsUnit.of_mul_eq_one (⟨0, 0, 1, 0⟩ : Z8) (by decide), by decide⟩

/-- Consequently `λ₂ ∣ x ↔ λ₃² ∣ x`: divisibility by the level-2 prime is divisibility by the
*square* of the level-3 prime — the grade-doubling on the level of divisibility. -/
theorem dvd_levelTwo_iff (x : Z8) : (1 - imag) ∣ x ↔ lam ^ 2 ∣ x := by
  have h1 : (1 - imag : Z8) = (⟨0, 0, -1, 0⟩ : Z8) * onePlusI := by decide
  have h2 : (onePlusI : Z8) = (⟨0, 0, 1, 0⟩ : Z8) * (1 - imag) := by decide
  rw [dvd_lamSq_iff, ← dvd_onePlusI_iff]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨(⟨0, 0, -1, 0⟩ : Z8) * t, by rw [h1]; ring⟩
  · rintro ⟨t, rfl⟩; exact ⟨(⟨0, 0, 1, 0⟩ : Z8) * t, by rw [h2]; ring⟩

end Catalyst
end Pi3
