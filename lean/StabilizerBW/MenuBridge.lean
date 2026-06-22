import Mathlib

/-!
# The Soundness ↔ Facet-Structure Bridge (Target H-B)

This file formalizes the structural bridge from the menu polytope's facet
geometry to the operational soundness of compiled contextuality tests, as
described in `02-menu-zero-set.tex`, Remark `rem:mzs-arora-bridge-scope`,
named target **H-B**.

## What is modelled

A *facet* of the menu polytope `F_Ω` is, for the purposes of the soundness
bridge, exactly a facet inequality
`∑_k α_k ⟨M_k⟩ ≤ C(Ω)`
together with the data needed to read off its operational content:

* `K` observables `M_k` (we only need their number, `K`);
* the real facet coefficients `α_k = coeff k`;
* the classical (LHV) bound `C = classicalBound`.

A quantum state `ρ` enters only through its profile of expectation values
`E : Fin K → ℝ`, `E k = Tr(M_k ρ)`.  The *facet violation* of `ρ` is
`V(E) = (∑_k α_k E_k) − C`.

The contextuality game `G_Ω^α` derived from the facet is, abstractly, the
affine rescaling of the facet functional into `[0,1]`:

* facet functional         `L(E) = ∑_k α_k E_k`;
* facet half-width          `S    = ∑_k |α_k|`  (the largest `|L|` can reach
                                                  over profiles with `|E_k| ≤ 1`);
* game normalisation        `N    = 2S`;
* acceptance probability    `accept(E) = (L(E) + S) / N`.

With this normalisation the game value of any profile with `|E_k| ≤ 1` lies in
`[0,1]`, the classical value is `(C + S)/N`, and the quantum value on `ρ_*` is
`(L(E_*) + S)/N = (C + V)/N`.

## Main results

* `MenuBridge.Facet.gap_eq` — **(classical side, (C))** the
  un-compiled gap equals `V/N` on the nose:
  `quantumValue E − classicalValue = violation E / N`.
* `MenuBridge.Facet.accept_le_classicalValue` — the classical value is a genuine
  upper bound: any profile obeying the facet inequality accepts with probability
  `≤ classicalValue`.
* `MenuBridge.Facet.accept_mem_unitInterval` — well-formedness: the game value is
  a probability.
* `MenuBridge.Facet.compiled_gap` — **(compiled side, (K))** under the
  named cryptographic soundness/completeness hypotheses (the Arora et al.
  guarantee), the *compiled* gap is bounded below by the linear function
  `f(V) = V/N` minus the cryptographic noise:
  `violation E / N − (negl_C + negl_Q) ≤ p_Q^c − p_C^c`.
* `MenuBridge.menu_bridge` — the worst-facet packaging matching
  `V_Ω(ρ) = max_α (∑_k α_k Tr(M_k ρ) − C^α)`: there is a witnessing facet whose
  un-compiled gap equals `V_Ω / N`.
* The `MenuBridge.CHSH` section instantiates the bridge on the `n = 2` CHSH facet
  (**CHSH cross-validation**): `N = 8`, and on the Tsirelson profile the gap
  is exactly `(√2 − 1)/4`, i.e. the explicit menu-independent constant is
  `c₁ = 1/N = 1/8` for this facet.

The cryptographic content of the Arora compilation (LWE-based soundness) is, by
design, *not* re-proved here: it enters `compiled_gap` as explicit hypotheses
(`hsound`, `hcomplete`), exactly the "operational-modulo-cryptography" ledger of
the chapter.  Everything else is unconditional.
-/

open scoped BigOperators

namespace MenuBridge

/-- A facet of a menu polytope `F_Ω`, abstracted to the data the soundness
bridge needs: the number `K` of observables `M_k`, the real facet coefficients
`α_k = coeff k`, and the classical (LHV) bound `C = classicalBound`. -/
structure Facet (K : ℕ) where
  /-- The facet coefficients `α_k`. -/
  coeff : Fin K → ℝ
  /-- The classical (LHV) bound `C^α(Ω)`. -/
  classicalBound : ℝ

variable {K : ℕ}

/-- The facet functional `L(E) = ∑_k α_k E_k`, evaluated on a profile of
expectation values `E k = Tr(M_k ρ)`. -/
def Facet.L (f : Facet K) (E : Fin K → ℝ) : ℝ := ∑ k, f.coeff k * E k

/-- The facet half-width `S = ∑_k |α_k|`: the largest `|L(E)|` can reach over
profiles with `|E_k| ≤ 1`. -/
def Facet.S (f : Facet K) : ℝ := ∑ k, |f.coeff k|

/-- The game normalisation `N = 2S`. -/
def Facet.N (f : Facet K) : ℝ := 2 * f.S

/-- The facet violation of a profile: `V(E) = L(E) − C`. -/
def Facet.violation (f : Facet K) (E : Fin K → ℝ) : ℝ := f.L E - f.classicalBound

/-- Acceptance probability of the contextuality game `G_Ω^α` on a profile:
the facet functional affinely rescaled into `[0,1]`. -/
noncomputable def Facet.accept (f : Facet K) (E : Fin K → ℝ) : ℝ :=
  (f.L E + f.S) / f.N

/-- Classical value of the game `c^α = C^α/N` (acceptance at the classical
bound). -/
noncomputable def Facet.classicalValue (f : Facet K) : ℝ :=
  (f.classicalBound + f.S) / f.N

/-- Quantum value of the game on the state with profile `E`. -/
noncomputable def Facet.quantumValue (f : Facet K) (E : Fin K → ℝ) : ℝ :=
  f.accept E

/-
The half-width is nonnegative.
-/
lemma Facet.S_nonneg (f : Facet K) : 0 ≤ f.S := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-
A nondegenerate facet (`S > 0`) has positive normalisation.
-/
lemma Facet.N_pos (f : Facet K) (hS : 0 < f.S) : 0 < f.N := by
  exact mul_pos zero_lt_two hS

/-
`|L(E)| ≤ S` whenever every expectation value is bounded by `1`.
-/
lemma Facet.abs_L_le_S (f : Facet K) (E : Fin K → ℝ) (hE : ∀ k, |E k| ≤ 1) :
    |f.L E| ≤ f.S := by
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i _ => by rw [ abs_mul ] ; exact mul_le_of_le_one_right ( abs_nonneg _ ) ( hE i ) )

/-
**Well-formedness.** On any physical profile (each `|E_k| ≤ 1`) the game
value is a genuine probability in `[0,1]`.
-/
lemma Facet.accept_mem_unitInterval (f : Facet K) (hS : 0 < f.S)
    (E : Fin K → ℝ) (hE : ∀ k, |E k| ≤ 1) :
    0 ≤ f.accept E ∧ f.accept E ≤ 1 := by
      unfold Facet.accept;
      rw [ div_le_one, le_div_iff₀ ];
      · constructor <;> nlinarith [ abs_le.mp ( f.abs_L_le_S E hE ), show f.N = 2 * f.S from rfl ];
      · exact f.N_pos hS;
      · exact f.N_pos hS

/-
**The classical side (C).** The un-compiled gap equals the facet
violation divided by the normalisation `N`, on the nose:
`quantumValue E − classicalValue = V(E)/N`. This is the unrolling of the menu
polytope's geometry into the contextuality-game language.
-/
theorem Facet.gap_eq (f : Facet K) (E : Fin K → ℝ) :
    f.quantumValue E - f.classicalValue = f.violation E / f.N := by
      convert div_sub_div_same _ _ f.N using 1;
      unfold Facet.violation; ring;

/-
The classical value is a genuine upper bound: any profile obeying the facet
inequality `L(E) ≤ C` accepts with probability at most `classicalValue`. This is
the operational form of "`c^α = C^α/N` is the classical value".
-/
theorem Facet.accept_le_classicalValue (f : Facet K) (hS : 0 < f.S)
    (E : Fin K → ℝ) (hcl : f.L E ≤ f.classicalBound) :
    f.accept E ≤ f.classicalValue := by
      convert div_le_div_of_nonneg_right ( add_le_add_right hcl f.S ) ( mul_nonneg zero_le_two hS.le ) using 1;
      · unfold Facet.accept Facet.N; ring;
      · unfold Facet.classicalValue Facet.N; ring;

/-
Quantum advantage: a profile that violates the facet (`V > 0`) strictly
beats the classical value.
-/
theorem Facet.classicalValue_lt_quantumValue (f : Facet K) (hS : 0 < f.S)
    (E : Fin K → ℝ) (hV : 0 < f.violation E) :
    f.classicalValue < f.quantumValue E := by
      linarith [ Facet.gap_eq f E, show 0 < f.violation E / f.N from div_pos hV ( by linarith [ Facet.N_pos f hS ] ) ]

/-
**The compiled side (K).** Under the named cryptographic guarantees of
the Arora et al. compilation —
* completeness: the honest quantum prover holding `ρ_*` is accepted with
  probability `p_Q^c ≥ quantumValue E − negl_Q`, and
* soundness: every computationally-bounded classical prover is accepted with
  probability `p_C^c ≤ classicalValue + negl_C`
— the *compiled* soundness gap is bounded below by the linear function
`f(V) = V/N` minus the cryptographic noise. The degradation is additive
(linear in `V`, not super-linear), which is the expected `rem:mzs-arora-bridge`
outcome rather than a falsification.
-/
theorem Facet.compiled_gap (f : Facet K) (E : Fin K → ℝ)
    (pQc pCc neglQ neglC : ℝ)
    (hcomplete : f.quantumValue E - neglQ ≤ pQc)
    (hsound : pCc ≤ f.classicalValue + neglC) :
    f.violation E / f.N - (neglC + neglQ) ≤ pQc - pCc := by
      linarith [ Facet.gap_eq f E ]

/-
The monotone bridge function `f(V) = V/N` is increasing in the violation.
-/
theorem Facet.gap_mono (f : Facet K) (hS : 0 < f.S) {E E' : Fin K → ℝ}
    (h : f.violation E ≤ f.violation E') :
    f.violation E / f.N ≤ f.violation E' / f.N := by
      gcongr;
      exact mul_nonneg zero_le_two hS.le

/-! ## Worst-facet packaging

The `V_Ω(ρ) = max_α (∑_k α_k Tr(M_k ρ) − C^α)` is the worst facet
violation over the menu's finite facet family.  We package the bridge through
the *witnessing* facet that attains the max. -/

variable {m : ℕ}

/-- The worst facet violation `V_Ω(E) = max_j V_{α_j}(E)` over a nonempty finite
facet family. -/
noncomputable def menuViolation [NeZero m] (fac : Fin m → Facet K)
    (E : Fin K → ℝ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := Fin m)) (fun j => (fac j).violation E)

/-
There is a witnessing facet attaining the worst violation.
-/
theorem exists_witness_facet [NeZero m] (fac : Fin m → Facet K) (E : Fin K → ℝ) :
    ∃ j, (fac j).violation E = menuViolation fac E := by
      convert Finset.exists_max_image Finset.univ ( fun j => ( fac j ).violation E ) ( Finset.univ_nonempty );
      constructor <;> intro h;
      · exact ⟨ Finset.mem_univ _, fun x' _ => h.symm ▸ Finset.le_sup' ( fun j => ( fac j ).violation E ) ( Finset.mem_univ _ ) ⟩;
      · exact le_antisymm ( Finset.le_sup' ( fun j => ( fac j ).violation E ) ( Finset.mem_univ _ ) ) ( Finset.sup'_le _ _ fun j hj => h.2 j hj )

/-
**The bridge, worst-facet form.** For every menu (finite facet family) and
every profile there is a witnessing facet whose un-compiled soundness gap equals
the worst facet violation divided by that facet's normalisation:
`quantumValue E − classicalValue = V_Ω(E) / N`.
-/
theorem menu_bridge [NeZero m] (fac : Fin m → Facet K) (E : Fin K → ℝ) :
    ∃ j, (fac j).quantumValue E - (fac j).classicalValue = menuViolation fac E / (fac j).N := by
  -- Apply the gap_eq theorem to the facet j obtained from exists_witness_facet.
  obtain ⟨j, hj⟩ := exists_witness_facet fac E;
  use j;
  rw [Facet.gap_eq (fac j) E, hj]

/-! ## CHSH cross-validation: the `n = 2` CHSH facet

At `n = 2` the menu is the product (Bell) menu and the bridge reduces to the
Bell test, with no cryptographic compilation needed.  The CHSH facet is
`T_ZZ + T_ZX + T_XZ − T_XX ≤ 2`, i.e. coefficients `(1,1,1,−1)` and classical
bound `2`.  We confirm `N = 8` and that on the Tsirelson profile
`(1/√2, 1/√2, 1/√2, −1/√2)` (CHSH value `2√2`) the gap is exactly `(√2−1)/4`,
so the explicit constant for this facet is `c₁ = 1/N = 1/8`. -/

namespace CHSH

/-- The `n = 2` CHSH facet: `T_ZZ + T_ZX + T_XZ − T_XX ≤ 2`. -/
def chshFacet : Facet 4 where
  coeff := ![1, 1, 1, -1]
  classicalBound := 2

/-- The Tsirelson-optimal correlation profile, CHSH value `2√2`. -/
noncomputable def tsirelsonProfile : Fin 4 → ℝ :=
  ![1 / Real.sqrt 2, 1 / Real.sqrt 2, 1 / Real.sqrt 2, -(1 / Real.sqrt 2)]

/-
The CHSH facet half-width is `S = 4`.
-/
theorem chsh_S : chshFacet.S = 4 := by
  unfold chshFacet;
  norm_num [ Facet.S, Fin.sum_univ_succ ]

/-
The CHSH game normalisation is `N = 8`.
-/
theorem chsh_N : chshFacet.N = 8 := by
  convert congr_arg ( fun x : ℝ => 2 * x ) ( chsh_S ) using 1;
  norm_num

/-
The CHSH functional on the Tsirelson profile is `2√2`.
-/
theorem chsh_L_tsirelson : chshFacet.L tsirelsonProfile = 2 * Real.sqrt 2 := by
  unfold chshFacet tsirelsonProfile;
  unfold Facet.L;
  norm_num [ Fin.sum_univ_succ ];
  grind

/-
The Tsirelson facet violation is `2√2 − 2`.
-/
theorem chsh_violation_tsirelson :
    chshFacet.violation tsirelsonProfile = 2 * Real.sqrt 2 - 2 := by
      convert congr_arg ( fun x => x - 2 ) ( chsh_L_tsirelson )

/-
**Explicit constant.** On the Tsirelson profile the un-compiled CHSH gap is
exactly `(√2 − 1)/4`, matching the Tsirelson bound with `c₁ = 1/N = 1/8`.
-/
theorem chsh_gap_tsirelson :
    chshFacet.quantumValue tsirelsonProfile - chshFacet.classicalValue
      = (Real.sqrt 2 - 1) / 4 := by
        rw [ Facet.gap_eq, chsh_violation_tsirelson, chsh_N ]; ring

end CHSH

end MenuBridge