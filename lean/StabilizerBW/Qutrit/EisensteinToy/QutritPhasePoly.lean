import StabilizerBW.Qutrit.EisensteinToy.EisensteinIntegers

/-!
# T2 — Qutrit phase polynomials and the down-set Möbius transform

The qubit arithmetic view encodes a diagonal operator by its phase function and analyses it via
the **down-set Möbius transform** (finite differences) of the phases.  We provide the qutrit
analogue:

* `QutritPhasePoly n` — phase functions `(Fin n → ZMod 3) → ZMod 9` at the Howard–Vala 9th-root
  level (qutrit Clifford+T phases are 9th roots of unity);
* the down-set "zeta" transform `zetaT` (subset partial sums) and the Möbius transform `mobT`
  over an arbitrary commutative ring, together with the **Möbius inversion** `mobT_zetaT`.

The Möbius/finite-difference *combinatorial backbone is characteristic-independent*: the
inversion `mobT_zetaT` holds over **any** commutative ring, in particular over `ZMod 9` (qutrit
phases) and over `ℤ[ω]` (Eisenstein coefficients).  This is the part of the qubit machinery that
**does** generalise to `d = 3`; what fails (the arithmetic *grade constant*, `2 ↦ 1` not
`2 ↦ 3`) is isolated in `StrictSubsetTest.lean`.

Everything is kernel-clean (no `sorry`/`axiom`/`native_decide`/`@[implemented_by]`).
-/

namespace QutritEis

open Finset

/-- A qutrit phase polynomial on `n` qutrits: a phase function valued in `ZMod 9`
(the Howard–Vala 9th-root level). -/
abbrev QutritPhasePoly (n : ℕ) : Type := (Fin n → ZMod 3) → ZMod 9

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The down-set "zeta" transform: `zetaT f U = ∑_{V ⊆ U} f V`. -/
def zetaT (f : Finset (Fin n) → R) (U : Finset (Fin n)) : R :=
  ∑ V ∈ U.powerset, f V

/-- The down-set Möbius transform: `mobT g U = ∑_{V ⊆ U} (-1)^{|U| - |V|} g V`. -/
def mobT (g : Finset (Fin n) → R) (U : Finset (Fin n)) : R :=
  ∑ V ∈ U.powerset, (-1) ^ (U.card - V.card) * g V

/-
**Möbius inversion (characteristic-independent backbone).** The Möbius transform inverts the
zeta transform: `mobT (zetaT f) = f`, over any commutative ring.
-/
set_option maxHeartbeats 1600000 in
theorem mobT_zetaT (f : Finset (Fin n) → R) (U : Finset (Fin n)) :
    mobT (zetaT f) U = f U := by
  unfold mobT zetaT;
  -- By interchanging the order of summation, we can rewrite the double sum.
  have h_interchange : ∑ V ∈ U.powerset, (-1 : R) ^ (U.card - V.card) * ∑ W ∈ V.powerset, f W = ∑ W ∈ U.powerset, f W * ∑ V ∈ Finset.Icc W U, (-1 : R) ^ (U.card - V.card) := by
    simp +decide only [Finset.mul_sum _ _ _, mul_comm];
    rw [ Finset.sum_sigma', Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x hx => ⟨ x.2, x.1 ⟩ ) _ _ _ _ <;> simp +decide;
    · exact fun a ha₁ ha₂ => ⟨ Finset.Subset.trans ha₂ ha₁, ha₂, ha₁ ⟩;
    · aesop;
    · lia;
  -- Consider the inner sum $\sum_{V \in \text{Icc}(W, U)} (-1)^{|U| - |V|}$.
  have h_inner : ∀ W ∈ U.powerset, W ≠ U → ∑ V ∈ Finset.Icc W U, (-1 : R) ^ (U.card - V.card) = 0 := by
    intro W hW hWU
    have h_inner_sum : ∑ V ∈ Finset.Icc W U, (-1 : R) ^ (U.card - V.card) = ∑ V ∈ Finset.powerset (U \ W), (-1 : R) ^ (Finset.card V) := by
      apply Finset.sum_bij (fun V _ => U \ V);
      · simp +contextual [ Finset.subset_iff ];
        exact fun a ha₁ ha₂ x hx₁ hx₂ hx₃ => hx₂ ( ha₁ hx₃ );
      · simp +contextual [ Finset.ext_iff ];
        grind;
      · intro b hb; use U \ b; simp_all +decide [ Finset.subset_iff ] ;
        exact fun x hx hx' => hb hx' |>.2 hx;
      · simp +contextual [ Finset.card_sdiff ];
        exact fun a ha₁ ha₂ => by rw [ Finset.inter_eq_left.mpr ha₂ ] ;
    rw [ h_inner_sum, Finset.sum_powerset ];
    simp +decide [ Finset.sum_powersetCard ];
    have := add_pow ( -1 : R ) 1 ( Finset.card ( U \ W ) ) ; simp_all +decide [ mul_comm, Finset.sum_range_succ ] ;
    rw [ ← this, zero_pow ( Finset.card_ne_zero_of_mem ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by contrapose! hWU; aesop ) ) ) ) ];
  rw [ h_interchange, Finset.sum_eq_single U ] <;> aesop

/-
The dual inversion: `zetaT (mobT g) = g`.
-/
set_option maxHeartbeats 1600000 in
theorem zetaT_mobT (g : Finset (Fin n) → R) (U : Finset (Fin n)) :
    zetaT (mobT g) U = g U := by
  -- Swap the order of summation in the double sum.
  have h_swap : ∑ V ∈ U.powerset, ∑ W ∈ V.powerset, (-1 : R) ^ (V.card - W.card) * g W = ∑ W ∈ U.powerset, ∑ V ∈ (U \ W).powerset, (-1 : R) ^ (W.card + V.card - W.card) * g W := by
    rw [ Finset.sum_sigma', Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x hx => ⟨ x.2, x.1 \ x.2 ⟩ ) _ _ _ _ <;> simp +decide;
    · grind;
    · simp +contextual [ Finset.ext_iff ];
      intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h₁ h₂; ext x; by_cases hx : x ∈ a₂.2 <;> aesop;
      grind +extAll;
    · rintro ⟨ a, b ⟩ ha hb; use a ∪ b, a; simp_all +decide [ Finset.subset_iff ] ;
      grind;
    · grind;
  convert h_swap using 1;
  rw [ Finset.sum_eq_single U ] <;> simp +contextual;
  intro b hb hbU
  have h_sum_zero : ∑ x ∈ (U \ b).powerset, (-1 : R) ^ x.card = 0 := by
    have h_sum_zero : ∑ x ∈ (U \ b).powerset, (-1 : R) ^ x.card = (1 - 1) ^ (U \ b).card := by
      rw [ sub_eq_neg_add, add_pow ] ; simp +decide [ Finset.sum_powerset ];
      exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ mul_comm ] ;
    simp_all +decide [ Finset.card_sdiff ];
    rw [ Finset.inter_eq_left.mpr hb, zero_pow ( Nat.sub_ne_zero_of_lt ( Finset.card_lt_card ( lt_of_le_of_ne hb hbU ) ) ) ];
  rw [ ← Finset.sum_mul, h_sum_zero, MulZeroClass.zero_mul ]

end QutritEis