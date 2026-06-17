/-
# Soundness of PL_n

Soundness of `PL_n` with respect to the model semantics: every derivable
Pauli word is valid in the stabilizer codespace of its theory.

## Semantics

We realise `ℂ^(2^n)` as functions `Vec n := (Fin n → Bool) → ℂ` on the
computational basis (a bitstring indexes a basis vector). A signed Pauli word
`P = (-1)^{sign} i^{#Y} ⊗_j X^{x_j} Z^{z_j}` acts by

 `(P · v)(c) = coeff P (c ⊕ x) · v (c ⊕ x)`,
 `coeff P b = (-1)^{sign} · iᶦ^{#Y} · (-1)^{⟨z, b⟩}`,

which is the standard Hermitian-Pauli matrix action written on basis
coefficients. The model space of a theory is

 `V Γ = { v | ∀ P ∈ Γ, P · v = v }`.

## Soundness

`Derivation Γ Q → ∀ v ∈ V Γ, Q · v = v` and
`BotDerivation Γ → ∀ v ∈ V Γ, v = 0`, by mutual induction on derivations.
The load-bearing facts are the *representation* lemmas
`pauliAction_mul` (commuting product = operator composition) and
`pauliAction_anticomm` (anticommuting operators anti-commute as maps).

Reference: `Proofs/T3_Soundness_Completeness.md`.
-/

import StabilizerBW.PauliLogic.Rules

open scoped BigOperators

namespace PauliLogic

/-- The state space `ℂ^(2^n)`, realised on the computational basis. -/
abbrev Vec (n : ℕ) := (Fin n → Bool) → ℂ

/-- Pointwise XOR of two bit vectors. -/
def xorv {n : ℕ} (a b : Fin n → Bool) : Fin n → Bool := fun j => xor (a j) (b j)

/-- `⟨z, b⟩ = Σ_j z_j b_j` over ℕ (an F₂ inner product, read mod 2 in signs). -/
def zdot {n : ℕ} (z b : Fin n → Bool) : ℕ := ∑ j, (z j && b j).toNat

/-- The basis coefficient of `P` at bitstring `b`. -/
noncomputable def coeff {n : ℕ} (P : Pauli n) (b : Fin n → Bool) : ℂ :=
 (-1) ^ (P.sign.toNat) * Complex.I ^ (numY P) * (-1) ^ (zdot P.zs b)

/-- The action of a signed Pauli word on `Vec n`. -/
noncomputable def pauliAction {n : ℕ} (P : Pauli n) (v : Vec n) : Vec n :=
 fun c => coeff P (xorv c P.xs) * v (xorv c P.xs)

/-- The model space `V Γ` of joint `+1`-eigenvectors of the theory. -/
def V {n : ℕ} (Γ : List (Pauli n)) : Set (Vec n) :=
 { v | ∀ P ∈ Γ, pauliAction P v = v }

/-! ## Basic `xorv` facts -/

@[simp] theorem xorv_false_right {n : ℕ} (c : Fin n → Bool) :
 xorv c (fun _ => false) = c := by funext j; simp [xorv]

theorem xorv_assoc {n : ℕ} (a b c : Fin n → Bool) :
 xorv (xorv a b) c = xorv a (xorv b c) := by funext j; simp [xorv, Bool.xor_assoc]

theorem xorv_comm {n : ℕ} (a b : Fin n → Bool) : xorv a b = xorv b a := by
 funext j; simp [xorv, Bool.xor_comm]

/-! ## Parity splitting of the `(-1)^{⟨z,b⟩}` factors -/

/-
`⟨z, a ⊕ b⟩` splits over XOR in the right argument (as a `(-1)`-power).
-/
theorem negpow_zdot_xorv_right {n : ℕ} (z a b : Fin n → Bool) :
 (-1 : ℂ) ^ (zdot z (xorv a b)) = (-1) ^ (zdot z a) * (-1) ^ (zdot z b) := by
 convert congr_arg ( fun x : ℕ => ( -1 : ℂ ) ^ x ) ( show ( zdot z ( xorv a b ) ) % 2 = ( zdot z a + zdot z b ) % 2 from ?_ ) using 1;
 · rw [ ← Nat.mod_add_div ( zdot z ( xorv a b ) ) 2, pow_add, pow_mul ] ; norm_num;
 · rw [ ← pow_add, ← Nat.mod_add_div ( zdot z a + zdot z b ) 2 ] ; norm_num [ pow_add, pow_mul ] ;
 · unfold xorv zdot;
 simp +decide only [← Finset.sum_add_distrib];
 exact Nat.ModEq.sum fun i _ => by cases z i <;> cases a i <;> cases b i <;> rfl;

/-
`⟨z ⊕ w, b⟩` splits over XOR in the left argument (as a `(-1)`-power).
-/
theorem negpow_zdot_xorv_left {n : ℕ} (z w b : Fin n → Bool) :
 (-1 : ℂ) ^ (zdot (xorv z w) b) = (-1) ^ (zdot z b) * (-1) ^ (zdot w b) := by
 convert negpow_zdot_xorv_right b z w using 1;
 · unfold zdot;
 grind;
 · congr! 2;
 · exact Finset.sum_congr rfl fun _ _ => by cases z ‹_› <;> cases b ‹_› <;> rfl;
 · exact Finset.sum_congr rfl fun _ _ => by cases w ‹_› <;> cases b ‹_› <;> rfl;

/-! ## The scalar identity at the heart of the representation property -/

/-
The phase bookkeeping for a commuting product: comparing the `i^{#Y}` and
 `(-1)^{⟨z,x⟩}` factors of `P·Q` with those of the operator composition.
-/
theorem coeff_scalar_mul {n : ℕ} (P Q : Pauli n) (h : P.commutes Q = true) :
 Complex.I ^ (numY P + numY Q) * (-1) ^ (crossZX P Q)
 = (if (phaseZ P Q) % 4 = 2 then (-1 : ℂ) else 1) * Complex.I ^ (numYmul P Q) := by
 -- Since `phaseZ P Q` is even, we can write it as `2 * k` for some integer `k`.
 obtain ⟨k, hk⟩ : ∃ k : ℤ, phaseZ P Q = 2 * k := by
 exact Int.dvd_of_emod_eq_zero ( phaseZ_even h );
 split_ifs <;> simp_all +decide [ mul_assoc ];
 · convert congr_arg ( fun x : ℂ => x * Complex.I ^ numYmul P Q ) ( show Complex.I ^ ( 2 * k ) = -1 from ?_ ) using 1;
 · convert congr_arg ( fun x : ℤ => Complex.I ^ x ) ( show ( numY P + numY Q : ℤ ) + 2 * crossZX P Q = 2 * k + numYmul P Q from ?_ ) using 1;
 · norm_cast ; norm_num [ pow_add, pow_mul ];
 · rw [ zpow_add₀ Complex.I_ne_zero ] ; norm_cast;
 · unfold phaseZ at hk; linarith;
 · ring;
 · rw [ zpow_mul, zpow_two ] ; norm_num;
 rcases Int.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num at *;
 norm_num [ zpow_add₀, zpow_mul' ];
 · -- Since `phaseZ P Q` is even, we can write it as `2 * k` for some integer `k`. Therefore, `(-1 : ℂ) ^ k = 1`.
 have h_even : (-1 : ℂ) ^ k = 1 := by
 rcases Int.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> norm_num [ zpow_add₀, zpow_mul ] at *;
 grind;
 have h_even : Complex.I ^ (numY P + numY Q) * (-1 : ℂ) ^ crossZX P Q = Complex.I ^ (phaseZ P Q + numYmul P Q) := by
 unfold phaseZ; ring;
 norm_cast ; norm_num [ pow_add, pow_mul', mul_assoc ];
 simp_all +decide [ zpow_add₀, zpow_mul ];
 norm_num [ zpow_two, ‹ ( -1 : ℂ ) ^ k = 1 › ]

/-! ## Action of distinguished words -/

@[simp] theorem pauliAction_I {n : ℕ} (v : Vec n) : pauliAction (pauliI n) v = v := by
 funext c; simp [pauliAction, coeff, pauliI, numY, zdot]

@[simp] theorem pauliAction_minusI {n : ℕ} (v : Vec n) :
 pauliAction (pauliMinusI n) v = -v := by
 funext c
 simp only [pauliAction, coeff, pauliMinusI, Pauli.negate, pauliI, numY, zdot,
 xorv_false_right]
 norm_num

/-! ## Representation lemmas -/

/-
For commuting `P, Q`, the action of the product is the composition of the
 actions: `P·Q` acts as `P ∘ Q`.
-/
theorem pauliAction_mul {n : ℕ} (P Q : Pauli n) (h : P.commutes Q = true) (v : Vec n) :
 pauliAction (Pauli.mul P Q h) v = pauliAction P (pauliAction Q v) := by
 have := @Pauli.mul_self;
 contrapose! this;
 refine' ⟨ 1, ⟨ Bool.true, fun _ => Bool.true, fun _ => Bool.true ⟩, _, _ ⟩ <;> simp +decide [ Pauli.mul ];
 simp +decide [ pauliI, mulXs, mulZs ];
 exact this ( by
 -- By definition of `pauliAction`, we can expand both sides.
 funext c; simp [pauliAction, coeff];
 rw [ show ( P.mul Q h ).sign.toNat = ( P.sign.toNat + Q.sign.toNat + ( if ( phaseZ P Q ) % 4 = 2 then 1 else 0 ) ) % 2 from ?_ ];
 · have h_coeff : Complex.I ^ (numY P + numY Q) * (-1) ^ (crossZX P Q) = (if (phaseZ P Q) % 4 = 2 then (-1 : ℂ) else 1) * Complex.I ^ (numYmul P Q) := by
 convert coeff_scalar_mul P Q h using 1;
 convert congr_arg ( fun x : ℂ => ( -1 : ℂ ) ^ P.sign.toNat * ( -1 : ℂ ) ^ Q.sign.toNat * x * ( -1 : ℂ ) ^ zdot ( xorv P.zs Q.zs ) ( xorv c ( xorv P.xs Q.xs ) ) * v ( xorv c ( xorv P.xs Q.xs ) ) ) h_coeff.symm using 1 <;> ring;
 · split_ifs <;> simp_all +decide [ Nat.even_iff, Nat.odd_iff ];
 · cases P.sign <;> cases Q.sign <;> simp_all +decide [ Nat.add_mod, Nat.mul_mod ]; all_goals congr;
 · cases P.sign <;> cases Q.sign <;> simp_all +decide [ Nat.add_mod ]; all_goals congr;
 · simp +decide [ crossZX, zdot, xorv ];
 simp +decide [ xorv, Finset.sum_add_distrib, pow_add, mul_assoc, mul_comm, mul_left_comm ];
 congr! 1;
 · exact congr_arg _ ( funext fun i => by simp +decide [ xorv, Bool.xor_assoc ] );
 · rw [ ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum ];
 rw [ ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib ] ; congr ; ext i ; by_cases hi : P.zs i <;> by_cases hj : Q.zs i <;> by_cases hk : P.xs i <;> by_cases hl : Q.xs i <;> by_cases hm : c i <;> simp +decide [ hi, hj, hk, hl, hm ] ;
 · unfold Pauli.mul;
 cases P.sign <;> cases Q.sign <;> simp +decide [ * ]; all_goals split_ifs <;> simp +decide [ * ] )

/-
For anticommuting `P, Q`, the actions anticommute.
-/
theorem pauliAction_anticomm {n : ℕ} (P Q : Pauli n) (h : P.commutes Q = false)
 (v : Vec n) :
 pauliAction P (pauliAction Q v) = - pauliAction Q (pauliAction P v) := by
 -- Since P and Q anticommute, we have that (crossZX P Q + crossZX Q P) % 2 = 1.
 have h_odd : (crossZX P Q + crossZX Q P) % 2 = 1 := by
 unfold Pauli.commutes at h; aesop;
 ext c;
 unfold pauliAction;
 -- Using the properties of `xorv` and `zdot`, we can simplify the expression.
 have h_simp : xorv (xorv c P.xs) Q.xs = xorv (xorv c Q.xs) P.xs := by
 exact funext fun i => by simp +decide [ xorv ] ; by_cases hi : c i <;> by_cases hj : P.xs i <;> by_cases hk : Q.xs i <;> simp +decide [ hi, hj, hk ] ;
 simp_all +decide [ coeff, negpow_zdot_xorv_right, negpow_zdot_xorv_left ];
 rw [ show zdot P.zs Q.xs = crossZX P Q from rfl, show zdot Q.zs P.xs = crossZX Q P from rfl ] ; ring;
 rw [ ← Nat.mod_add_div ( crossZX P Q ) 2, ← Nat.mod_add_div ( crossZX Q P ) 2 ] ; norm_num [ pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
 cases Nat.mod_two_eq_zero_or_one ( crossZX P Q ) <;> cases Nat.mod_two_eq_zero_or_one ( crossZX Q P ) <;> simp_all +decide [ Nat.add_mod ]

/-! ## Soundness -/

/-
**Soundness of PL_n** (Theorem 17.14, soundness direction): every
 derivable sequent is valid, and every contradictory theory has trivial
 model space.
-/
theorem soundness {n : ℕ} {Γ : List (Pauli n)} {Q : Pauli n}
 (d : Derivation Γ Q) : ∀ v ∈ V Γ, pauliAction Q v = v := by
 revert Q d;
 have h_ind : ∀ {Γ : List (Pauli n)} {Q : Pauli n} (d : Derivation Γ Q), ∀ v ∈ V Γ, pauliAction Q v = v := by
 intros Γ Q d; induction d using Derivation.rec;
 all_goals norm_num [ V ];
 exact fun v hv => hv _ ( List.get_mem _ _ );
 exact fun v hv => by rw [ pauliAction_mul _ _ ‹_› v, ‹∀ v ∈ V _, pauliAction _ v = v› v hv, ‹∀ v ∈ V _, pauliAction _ v = v› v hv ] ;
 exact fun v hv => ‹∀ v ∈ V _, pauliAction _ v = v› v ( by exact fun P hP => by cases hP <;> tauto );
 exact fun v hv => by rw [ ‹∀ v ∈ V _, v = 0› v hv, show pauliAction _ 0 = 0 from by ext; simp +decide [ pauliAction ] ] ;
 · grind +suggestions;
 · rename_i Γ' d' ih';
 intro v hv; specialize ih' v hv; simp_all +decide [ funext_iff ] ;
 exact fun x => by linear_combination' -ih' x / 2;
 exact fun { Q } d v hv => h_ind d v hv

/-
The falsum companion of soundness: a contradictory theory has only the
 zero vector in its model space.
-/
theorem soundnessBot {n : ℕ} {Γ : List (Pauli n)}
 (d : BotDerivation Γ) : ∀ v ∈ V Γ, v = 0 := by
 revert d;
 apply Classical.byContradiction
 intro h_nonzero;
 obtain ⟨d, hv, hv_ne_zero⟩ : ∃ d : BotDerivation Γ, ∃ v ∈ V Γ, v ≠ 0 := by
 exact by push_neg at h_nonzero; exact h_nonzero;
 obtain ⟨d, hv, hv_ne_zero⟩ : ∃ d : BotDerivation Γ, ∃ v ∈ V Γ, v ≠ 0 ∧ ∀ d' : BotDerivation Γ, ∀ v' ∈ V Γ, v' ≠ 0 → v' = v := by
 exact ⟨ d, hv, hv_ne_zero.1, hv_ne_zero.2, fun d' v' hv' hv'_ne_zero => by
 have := @soundness n Γ ( pauliMinusI n ) ; simp_all +decide [ V ] ;
 simp_all +decide [ funext_iff, Complex.ext_iff ];
 exact False.elim <| hv'_ne_zero.elim fun x hx => hx ( by linarith [ this ( Derivation.botElim _ d' ) v' hv' x ] ) ( by linarith [ this ( Derivation.botElim _ d' ) v' hv' x ] ) ⟩;
 have := hv_ne_zero.2.2 d ( 2 • hv ) ?_ ?_ <;> simp_all +decide [ two_smul ];
 · intro P hP; simp_all +decide [ V ] ;
 convert congr_arg₂ ( · + · ) ( hv_ne_zero.1 P hP ) ( hv_ne_zero.1 P hP ) using 1 ; ext ; simp +decide [ pauliAction ] ; ring;
 · grind

end PauliLogic