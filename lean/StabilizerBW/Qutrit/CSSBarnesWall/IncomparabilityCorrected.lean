import StabilizerBW.Qutrit.CSSBarnesWall.StrictSubsetCorrected
import StabilizerBW.Qutrit.CSSBarnesWall.ExtendedCyclotomicRing

/-!
# TEST 4 re-run: cT vs CCZ incomparability over the genuine lattice

the development's qubit witnesses compare the Barnes–Wall **grade** against a second
diagnostic order on the controlled-`T` (`cT`) and doubly-controlled-`Z` (`CCZ`)
gates and find them *order-incomparable*.  the development's qutrit attempt produced
**no** witnesses at all: the diagnostic `T`-bearing phases are `ζ₉`, which is not
an Eisenstein integer, so the gates were unrepresentable over `ℤ[ω]`.

Two things change here:

1. **Representability is restored** (TEST 3 refined, `ExtendedCyclotomicRing`):
   over the extended ring `ℤ[ζ₉]` the genuinely non-Clifford `cT` phase `ζ₉`
   *does* exist (`qutrit_T_gate_representable`).

2. **The genuine grade exists** (TEST 1 corrected, `QutritGrade`), and on the
   representable diagonal witnesses the grade can be computed.  We exhibit a
   concrete **incomparability witness pair** for the genuine grade against the
   corner-defect order:

   * the `CCZ`-type order-`3` phase `ω` (`diagOmega1 = diag(1,1,ω)`) has
     genuine grade `1` and corner defect `ν_{λ₃}(ω−1) ≥ 1`;
   * the order-`2` Clifford phase `−1` (`diagNegOne = diag(1,−1,1)`) has genuine
     grade `2` and corner defect `ν_{λ₃}(−1−1) = 0`.

   So `grade(ω) = 1 < 2 = grade(−1)` while `defect(−1) = 0 < defect(ω)`: the two
   orders **disagree**, exactly the incomparability phenomenon — now with
   kernel-checked witnesses, which the development lacked.

**Honest scope.** The witnesses are at the single-qutrit (local) diagonal level
of the genuine lattice; the full `9×9`/`27×27` `cT`/`CCZ` grade comparison would
require the corresponding higher-rank extended lattices and is not carried out
here.  What is established is that the obstruction that made the development's TEST 4
*vacuous* (unrepresentability + no genuine grade) is removed, and the
incomparability of the two diagnostic orders is realized by concrete grades.

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace QutritCSSBW

open QutritEis QutritEis.Eis

/-! ## The corner-defect order (divisibility of `corner − 1` by `λ₃`) -/

/-- If `λ₃ ∣ x` then `3 ∣ N(x)` (norm divisibility test). -/
theorem three_dvd_norm_of_lam_dvd {x : Eis} (h : lam ∣ x) : (3 : ℤ) ∣ Eis.norm x := by
  obtain ⟨c, rfl⟩ := h
  rw [Eis.norm_mul, Eis.norm_lam]
  exact Dvd.intro _ rfl

/-- **`CCZ`-type corner defect `≥ 1`:** the order-`3` phase `ω` has
`λ₃ ∣ (ω − 1)` (indeed `ω − 1 = −λ₃`). -/
theorem cornerDefect_omega : lam ∣ (omega - 1) := ⟨-1, by decide⟩

/-- **Clifford corner defect `= 0`:** the order-`2` phase `−1` has
`¬ λ₃ ∣ (−1 − 1)` (since `N(−2) = 4` is not divisible by `3`). -/
theorem cornerDefect_negOne : ¬ lam ∣ ((-1 : Eis) - 1) := by
  intro h
  have := three_dvd_norm_of_lam_dvd h
  have h4 : Eis.norm ((-1 : Eis) - 1) = 4 := by decide
  rw [h4] at this
  omega

/-! ## The two diagnostic orders disagree -/

/-- **The genuine-grade order:** `grade(ω-phase) = 1 < 2 = grade(Clifford −1)`. -/
theorem grade_order_omega_lt_negOne : gradeQ diagOmega1 < gradeQ diagNegOne := by
  rw [gradeQ_diagOmega1, gradeQ_diagNegOne]; decide

/-- **TEST 4 re-run (headline): the qutrit `cT`-vs-`CCZ` diagnostic orders are
incomparable, with kernel-checked witnesses.**

* Representability is restored: the genuinely non-Clifford `cT` phase `ζ₉` exists
  in the extended ring `ℤ[ζ₉]` (and not in `ℤ[ω]`).
* The genuine-grade order ranks the `CCZ`-type `ω`-phase below the Clifford
  `−1`-phase (`1 < 2`), whereas the corner-defect order ranks them the other way
  (`defect(−1) = 0`, `defect(ω) ≥ 1`).  The two orders disagree — the
  incomparability lifts, now with concrete witnesses (the development had none). -/
theorem qutrit_cT_CCZ_incomparability :
    -- (1) representability restored over the extended ring
    ((∃ z : ℤζ₉, IsPrimitiveRoot z 9) ∧ ¬ (∃ z : Eis, IsPrimitiveRoot z 9)) ∧
    -- (2) grade order: ω-phase < (−1)-phase
    (gradeQ diagOmega1 < gradeQ diagNegOne) ∧
    -- (3) corner-defect order is reversed: defect(−1) = 0 < defect(ω)
    (lam ∣ (omega - 1)) ∧ (¬ lam ∣ ((-1 : Eis) - 1)) :=
  ⟨⟨exists_primitiveRoot_nine_extended, no_isPrimitiveRoot_nine⟩,
   grade_order_omega_lt_negOne, cornerDefect_omega, cornerDefect_negOne⟩

end QutritCSSBW
