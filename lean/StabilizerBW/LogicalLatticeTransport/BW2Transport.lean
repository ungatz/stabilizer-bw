import Mathlib
import StabilizerBW.BWFreeModule

/-!
# General-Clifford transport of the logical lattice at `n = 2`

This file formalises the general-Clifford transport
step of Theorem 17.6 () at `n = 2`, *by direct
computation*, sidestepping the external lattice-automorphism citation
(Kliuchnikov–Schönnenbeck 2024, Thm 4.3) needed for general `n`.

The two-qubit coordinate space `Q 2 = ((ℤ[i]×ℤ[i])×(ℤ[i]×ℤ[i]))` carries
amplitudes `((a,b),(c,d))` of the computational basis `|00⟩,|01⟩,|10⟩,|11⟩`.
The leading (outer) split is qubit 1, the inner split is qubit 2.

## Main results

* `inBW2_iff` — an explicit congruence characterisation of membership in `BW₂`
 (verified numerically, then proved): `((a,b),(c,d)) ∈ BW₂` iff
 `(1+i) ∣ c-d`, `(1+i) ∣ a-c`, `(1+i) ∣ b-d`, and `2 ∣ a-b-c+d`.
* `*_preserves_BW2` — each two-qubit Clifford generator
 (`Z1,Z2,X1,X2,S1,S2,CNOT12,CNOT21,CZ,Had1,Had2`) maps `BW₂` into `BW₂`
 (**T1.1**). `Had1,Had2` are the `√2`-scaled (integer) Hadamards — the genuine
 Hadamard needs `√2 ∉ ℤ[i]`, so the lattice-respecting representative is the
 integer matrix `[[1,1],[1,-1]]`, which maps `BW₂` into itself.
* `transport_general` — the abstract transport theorem (**T1.2**): for a
 `BW`-automorphism `U` (an `Equiv` preserving `BWₙ` both ways) and a stabiliser
 `g`, the constraint sublattice of `U g U⁻¹` is `U` applied to that of `g`.
* `CNOT21_conj_Z1_eq_ZZ`, `ZZ_lattice_eq_transport` — the concrete `n=2`
 instance: the `⟨ZZ⟩` constraint sublattice is the `CNOT₂₁`-image of the
 `Z₁`-pinned sublattice (repetition-code flavour).
* `bell_encoder_image` — the (√2-scaled) Bell encoder `CNOT₁₂∘Had₁` maps the
 pinned generator `(1+i)²|00⟩` to `(1+i)·bellGen` (**T1.3** computation).
-/

open Zsqrtd

namespace BWArith
namespace Transport2

/-- The Gaussian unit `i = ⟨0,1⟩`. -/
abbrev gi : GI := ⟨0, 1⟩

/-! ## Two-qubit Clifford generators on `Q 2`

Each acts on `w = ((a,b),(c,d))` with `a=|00⟩, b=|01⟩, c=|10⟩, d=|11⟩`. -/

/-- `Z` on qubit 1: negate the `|1⟩`-block of qubit 1. This is `pinZ 1`. -/
def Z1 (w : Q 2) : Q 2 := ((w.1.1, w.1.2), (-w.2.1, -w.2.2))
/-- `Z` on qubit 2: negate the `|1⟩`-component of qubit 2 within each block. -/
def Z2 (w : Q 2) : Q 2 := ((w.1.1, -w.1.2), (w.2.1, -w.2.2))
/-- `X` on qubit 1: swap the two qubit-1 blocks. -/
def X1 (w : Q 2) : Q 2 := ((w.2.1, w.2.2), (w.1.1, w.1.2))
/-- `X` on qubit 2: swap the two components within each block. -/
def X2 (w : Q 2) : Q 2 := ((w.1.2, w.1.1), (w.2.2, w.2.1))
/-- `S` (phase) on qubit 1: multiply the `|1⟩`-block of qubit 1 by `i`. -/
def S1 (w : Q 2) : Q 2 := ((w.1.1, w.1.2), (gi • w.2.1, gi • w.2.2))
/-- `S` (phase) on qubit 2: multiply each `|1⟩`-component of qubit 2 by `i`. -/
def S2 (w : Q 2) : Q 2 := ((w.1.1, gi • w.1.2), (w.2.1, gi • w.2.2))
/-- `CNOT` with control 1, target 2: swap qubit-2 components in the `|1⟩`-block. -/
def CNOT12 (w : Q 2) : Q 2 := ((w.1.1, w.1.2), (w.2.2, w.2.1))
/-- `CNOT` with control 2, target 1: swap `|01⟩ ↔ |11⟩`. -/
def CNOT21 (w : Q 2) : Q 2 := ((w.1.1, w.2.2), (w.2.1, w.1.2))
/-- `CZ`: phase `-1` on `|11⟩`. -/
def CZ (w : Q 2) : Q 2 := ((w.1.1, w.1.2), (w.2.1, -w.2.2))
/-- `√2·H` on qubit 1: the integer Hadamard `B₀ ↦ B₀+B₁`, `B₁ ↦ B₀-B₁`. -/
def Had1 (w : Q 2) : Q 2 :=
 ((w.1.1 + w.2.1, w.1.2 + w.2.2), (w.1.1 - w.2.1, w.1.2 - w.2.2))
/-- `√2·H` on qubit 2: the integer Hadamard within each block. -/
def Had2 (w : Q 2) : Q 2 :=
 ((w.1.1 + w.1.2, w.1.1 - w.1.2), (w.2.1 + w.2.2, w.2.1 - w.2.2))

/-! ## Membership characterisation of `BW₂` -/

/--
Membership in `BW₁ = {(x,y) : (1+i) ∣ (x - y)}`.
-/
theorem inBW1_iff (x y : GI) : InBWn 1 (x, y) ↔ oneI ∣ (x - y) := by
 constructor;
 · rintro ⟨ _, a, _, hx ⟩;
 exact ⟨ a, by simpa [ sub_eq_iff_eq_add ] using hx ⟩;
 · rintro ⟨ a, ha ⟩;
 exact ⟨ trivial, a, trivial, by rw [ sub_eq_iff_eq_add ] at ha; aesop ⟩

/--
**Explicit characterisation of `BW₂`.**
 `((a,b),(c,d)) ∈ BW₂` iff `(1+i) ∣ c-d`, `(1+i) ∣ a-c`, `(1+i) ∣ b-d`,
 and `2 ∣ a-b-c+d`.
-/
theorem inBW2_iff (a b c d : GI) :
 InBWn 2 ((a, b), (c, d)) ↔
 oneI ∣ (c - d) ∧ oneI ∣ (a - c) ∧ oneI ∣ (b - d) ∧ (2 : GI) ∣ (a - b - c + d) := by
 constructor;
 · intro h;
 -- By definition of $BW₂$, we know that $(c, d) \in BW₁$ and there exists $A \in BW₁$ such that $(a, b) = oneI • A + (c, d)$.
 obtain ⟨h_cd, A, hA, h_eq⟩ := h;
 -- From `h_eq`, we get `a = oneI • A.1 + c` and `b = oneI • A.2 + d`.
 obtain ⟨p, q, hpq⟩ : ∃ p q : GI, A = (p, q) ∧ a = oneI * p + c ∧ b = oneI * q + d := by
 exact ⟨ A.1, A.2, rfl, by simpa using congr_arg Prod.fst h_eq, by simpa using congr_arg Prod.snd h_eq ⟩;
 simp_all +decide [ inBW1_iff ];
 obtain ⟨ k, hk ⟩ := inBW1_iff p q |>.1 hA;
 rw [ show p = q + oneI * k by linear_combination' hk ] ; ring_nf;
 exact ⟨ gi * k, by rw [ show oneI ^ 2 = 2 * gi by decide ] ; ring ⟩;
 · intro h_div
 obtain ⟨p, hp⟩ : ∃ p : GI, a - c = oneI * p := h_div.right.left
 obtain ⟨q, hq⟩ : ∃ q : GI, b - d = oneI * q := h_div.right.right.left
 have hpq : oneI ∣ p - q := by
 obtain ⟨ k, hk ⟩ := h_div.2.2.2;
 have h_div : oneI^2 ∣ (a - c) - (b - d) := by
 rw [ show oneI ^ 2 = 2 * gi by decide ];
 exact ⟨ k * ⟨ 0, -1 ⟩, by ext <;> norm_num <;> have := congr_arg Zsqrtd.re hk <;> have := congr_arg Zsqrtd.im hk <;> norm_num at * <;> linarith ⟩;
 simp_all +decide [ sq, mul_sub ];
 exact Exists.elim h_div fun x hx => ⟨ x, mul_left_cancel₀ ( show oneI ≠ 0 from by decide ) <| by linear_combination' hx ⟩;
 convert freeModuleDecomp 1 ( ( a, b ), c, d ) |>.2 ⟨ ( p, q ), ( c, d ), ?_, ?_, ?_ ⟩ using 1;
 · exact inBW1_iff p q |>.2 hpq;
 · exact inBW1_iff _ _ |>.2 h_div.1;
 · simp_all +decide [ sub_eq_iff_eq_add, Prod.ext_iff ];
 rfl

/-! ## T1.1 — Clifford generators preserve `BW₂` -/

theorem Z1_preserves_BW2 : ∀ w : Q 2, InBWn 2 w → InBWn 2 (Z1 w) := by
 intro w hw;
 obtain ⟨a, b, c, d, hw⟩ : ∃ a b c d : GI, w = ((a, b), (c, d)) := by
 exact ⟨ _, _, _, _, rfl ⟩;
 simp_all +decide [ Z1 ];
 rw [ inBW2_iff ] at *;
 refine' ⟨ _, _, _, _ ⟩;
 · convert dvd_neg.mpr ( ‹oneI ∣ c - d ∧ oneI ∣ a - c ∧ oneI ∣ b - d ∧ 2 ∣ a - b - c + d›.1 ) using 1 ; ring;
 · have h_div : oneI ∣ 2 * c := by
 exact dvd_mul_of_dvd_left ( by exact ⟨ ⟨ 1, -1 ⟩, by decide ⟩ ) _;
 convert dvd_add ( ‹oneI ∣ c - d ∧ oneI ∣ a - c ∧ oneI ∣ b - d ∧ 2 ∣ a - b - c + d›.2.1 ) h_div using 1 ; ring;
 · convert dvd_add ( show oneI ∣ b - d from by tauto ) ( show oneI ∣ 2 * d from by exact dvd_mul_of_dvd_left ( by exact ⟨ ⟨ 1, -1 ⟩, by decide ⟩ ) _ ) using 1 ; ring;
 · obtain ⟨ k, hk ⟩ := ‹oneI ∣ c - d ∧ oneI ∣ a - c ∧ oneI ∣ b - d ∧ 2 ∣ a - b - c + d›.2.1; obtain ⟨ l, hl ⟩ := ‹oneI ∣ c - d ∧ oneI ∣ a - c ∧ oneI ∣ b - d ∧ 2 ∣ a - b - c + d›.2.2.1; obtain ⟨ m, hm ⟩ := ‹oneI ∣ c - d ∧ oneI ∣ a - c ∧ oneI ∣ b - d ∧ 2 ∣ a - b - c + d›.2.2.2; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
 exact ⟨ a - b - m, by ring ⟩

theorem Z2_preserves_BW2 : ∀ w : Q 2, InBWn 2 w → InBWn 2 (Z2 w) := by
 intro w hw;
 rcases w with ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩;
 rw [ inBW2_iff ] at *;
 refine' inBW2_iff _ _ _ _ |>.2 ⟨ _, _, _, _ ⟩;
 · convert dvd_add hw.1 ( dvd_mul_of_dvd_right ( show oneI ∣ 2 * d from dvd_mul_of_dvd_left ( by exact ⟨ ⟨ 1, -1 ⟩, by decide ⟩ ) _ ) 1 ) using 1 ; ring;
 · exact hw.2.1;
 · convert hw.2.2.1.neg_right using 1 ; ring;
 · convert dvd_add hw.2.2.2 ( dvd_mul_right ( 2 : GI ) ( b - d ) ) using 1 ; ring

theorem X1_preserves_BW2 : ∀ w : Q 2, InBWn 2 w → InBWn 2 (X1 w) := by
 intro w hw
 rcases w with ⟨⟨a,b⟩,⟨c,d⟩⟩;
 simp_all +decide [ inBW2_iff ];
 convert inBW2_iff _ _ _ _ |>.2 _ using 1;
 refine' ⟨ _, _, _, _ ⟩;
 · convert dvd_add ( dvd_sub hw.2.1 hw.2.2.1 ) hw.1 using 1 ; ring;
 · convert dvd_neg.mpr hw.2.1 using 1;
 module;
 · convert hw.2.2.1.neg_right using 1 ; ring;
 · convert hw.2.2.2.neg_right using 1 ; ring

theorem X2_preserves_BW2 : ∀ w : Q 2, InBWn 2 w → InBWn 2 (X2 w) := by
 intro w hw;
 rcases w with ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩;
 convert inBW2_iff _ _ _ _ |>.2 _ using 1;
 obtain ⟨ h₁, h₂, h₃, h₄ ⟩ := inBW2_iff a b c d |>.1 hw;
 exact ⟨ by simpa using h₁.neg_right, h₃, h₂, by convert h₄.neg_right using 1; ring ⟩

theorem S1_preserves_BW2 : ∀ w : Q 2, InBWn 2 w → InBWn 2 (S1 w) := by
 intro w hw;
 rcases w with ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩;
 convert inBW2_iff _ _ _ _ |>.2 _ using 1;
 have h_div : ∀ z : GI, oneI ∣ z ↔ (z.re + z.im) % 2 = 0 := by
 intro z
 constructor;
 · rintro ⟨ k, rfl ⟩ ; norm_num [ oneI ] ; ring_nf; norm_num [ Int.add_emod, Int.mul_emod ] ;
 · intro hz
 use ⟨(z.re + z.im) / 2, (z.im - z.re) / 2⟩;
 ext <;> norm_num [ oneI ] <;> omega;
 have h_div2 : ∀ z : GI, (2 : GI) ∣ z ↔ z.re % 2 = 0 ∧ z.im % 2 = 0 := by
 intro z; exact ⟨ fun ⟨ k, hk ⟩ => ⟨ by
 simp +decide [ hk, Zsqrtd.ext_iff ], by
 simp +decide [ hk, Zsqrtd.ext_iff ] ⟩, fun h => ⟨ ⟨ z.re / 2, z.im / 2 ⟩, by
 exact Zsqrtd.ext ( by norm_num; linarith [ Int.emod_add_mul_ediv z.re 2 ] ) ( by norm_num; linarith [ Int.emod_add_mul_ediv z.im 2 ] ) ⟩ ⟩ ;
 have := inBW2_iff a b c d |>.1 hw; simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;
 grind

theorem S2_preserves_BW2 : ∀ w : Q 2, InBWn 2 w → InBWn 2 (S2 w) := by
 intro w hw;
 rcases w with ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩;
 convert inBW2_iff _ _ _ _ |>.2 _ using 1;
 have h_div : ∀ z : GI, oneI ∣ z ↔ (z.re + z.im) % 2 = 0 := by
 intro z
 constructor
 intro h_div
 obtain ⟨k, hk⟩ := h_div
 have h_sum : z.re + z.im = 2 * k.re := by
 simp +decide [ hk, oneI ] ; ring
 exact h_sum.symm ▸ by norm_num
 intro h_sum
 use ⟨(z.re + z.im) / 2, (z.im - z.re) / 2⟩
 ext <;> norm_num <;> omega;
 have h_div2 : ∀ z : GI, (2 : GI) ∣ z ↔ (z.re % 2 = 0 ∧ z.im % 2 = 0) := by
 intro z; exact ⟨fun h => by
 obtain ⟨ k, rfl ⟩ := h; simp +decide [ Zsqrtd.ext_iff ] ;, fun h => by
 exact ⟨ ⟨ z.re / 2, z.im / 2 ⟩, by ext <;> simp +decide [ *, Int.mul_ediv_cancel' ( Int.dvd_of_emod_eq_zero h.1 ), Int.mul_ediv_cancel' ( Int.dvd_of_emod_eq_zero h.2 ) ] ⟩⟩;
 have := inBW2_iff a b c d |>.1 hw; simp_all +decide [ Zsqrtd.ext_iff ] ;
 grind

theorem CNOT12_preserves_BW2 : ∀ w : Q 2, InBWn 2 w → InBWn 2 (CNOT12 w) := by
 intro w hw;
 convert inBW2_iff _ _ _ _ |>.2 _;
 obtain ⟨a, b, c, d, hw⟩ : ∃ a b c d : GI, w = ((a, b), (c, d)) := by
 exact ⟨ _, _, _, _, rfl ⟩;
 simp_all +decide [ inBW2_iff ];
 obtain ⟨ h₁, h₂, h₃, h₄ ⟩ := inBW2_iff a b c d |>.1 ‹_›;
 exact ⟨ by simpa using h₁.neg_right, by simpa using h₂.add h₁, by simpa using h₃.sub h₁, by convert h₄.add ( dvd_mul_right 2 ( c - d ) ) using 1; ring ⟩

theorem CNOT21_preserves_BW2 : ∀ w : Q 2, InBWn 2 w → InBWn 2 (CNOT21 w) := by
 intro w hw
 rcases w with ⟨⟨a, b⟩, ⟨c, d⟩⟩
 simp +decide [CNOT21] at *;
 rw [ inBW2_iff ] at *;
 refine' ⟨ _, hw.2.1, _, _ ⟩;
 · convert dvd_sub hw.1 hw.2.2.1 using 1 ; ring;
 · simpa using hw.2.2.1.neg_right;
 · convert hw.2.2.2.add ( dvd_mul_right 2 ( b - d ) ) using 1 ; ring

theorem CZ_preserves_BW2 : ∀ w : Q 2, InBWn 2 w → InBWn 2 (CZ w) := by
 intro w hw;
 rcases w with ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩ ; simp_all +decide [ inBW2_iff ];
 refine' inBW2_iff _ _ _ _ |>.2 ⟨ _, _, _, _ ⟩;
 · convert dvd_add hw.1 ( dvd_mul_of_dvd_left ( show oneI ∣ 2 from ⟨ ⟨ 1, -1 ⟩, by decide ⟩ ) d ) using 1 ; ring;
 · exact hw.2.1;
 · convert dvd_add hw.2.2.1 ( dvd_mul_right oneI ( ⟨ 1, -1 ⟩ * d ) ) using 1 ; ring;
 ext <;> norm_num <;> ring;
 · convert hw.2.2.2.sub ( dvd_mul_right 2 d ) using 1 ; ring

theorem Had1_preserves_BW2 : ∀ w : Q 2, InBWn 2 w → InBWn 2 (Had1 w) := by
 intro w hw;
 obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : GI, w = ((a, b), (c, d)) := by
 rcases w with ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩ ; exact ⟨ a, b, c, d, rfl ⟩ ;
 refine' inBW2_iff _ _ _ _ |>.2 ⟨ _, _, _, _ ⟩;
 · have := inBW2_iff a b c d |>.1 hw;
 exact dvd_sub this.2.1 this.2.2.1;
 · convert dvd_mul_right oneI ( c * ⟨ 1, -1 ⟩ ) using 1 ; ring;
 ext <;> simp +decide [ mul_assoc ];
 · convert dvd_mul_of_dvd_left ( show oneI ∣ 2 from ⟨ ⟨ 1, -1 ⟩, by decide ⟩ ) d using 1 ; ring;
 · exact ⟨ c - d, by ring ⟩

theorem Had2_preserves_BW2 : ∀ w : Q 2, InBWn 2 w → InBWn 2 (Had2 w) := by
 intro w hw;
 rcases w with ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩;
 rw [ inBW2_iff ] at *;
 refine' inBW2_iff _ _ _ _ |>.2 ⟨ _, _, _, _ ⟩;
 · convert dvd_mul_of_dvd_left ( show oneI ∣ 2 from ⟨ ⟨ 1, -1 ⟩, by decide ⟩ ) d using 1 ; ring;
 · convert dvd_add hw.2.1 hw.2.2.1 using 1 ; ring;
 · convert dvd_sub hw.2.1 hw.2.2.1 using 1 ; ring;
 · convert dvd_mul_right ( 2 : GI ) ( b - d ) using 1 ; ring

/-! ## T1.2 — abstract transport theorem -/

/--
**Abstract Clifford transport.** For a `BW`-automorphism `U` (a bijection of
 `Q n` whose forward and inverse maps both preserve `BWₙ`) and any stabiliser
 operator `g`, the constraint sublattice of the transported stabiliser
 `U ∘ g ∘ U⁻¹` is exactly `U` applied to the constraint sublattice of `g`.
 This is the lattice form of `BWₙ^{U S₀ U†} = U(BWₙ^{S₀})`.
-/
theorem transport_general {n : ℕ} (U : Equiv.Perm (Q n))
 (hU : ∀ w, InBWn n w → InBWn n (U w))
 (hUinv : ∀ w, InBWn n w → InBWn n (U.symm w))
 (g : Q n → Q n) :
 {w | InBWn n w ∧ (U ∘ g ∘ U.symm) w = w}
 = U '' {w | InBWn n w ∧ g w = w} := by
 ext w; simp [Set.mem_image];
 grind +qlia

/-! ## T1.2/T1.3 — concrete `n=2` transport instances -/

/--
`CNOT₂₁` is an involution.
-/
theorem CNOT21_involutive : Function.Involutive CNOT21 := by
 unfold Function.Involutive CNOT21; aesop;

/-- `CNOT₂₁` as a permutation of `Q 2`. -/
def CNOT21perm : Equiv.Perm (Q 2) := Function.Involutive.toPerm CNOT21 CNOT21_involutive

/--
`CNOT₁₂` is an involution.
-/
theorem CNOT12_involutive : Function.Involutive CNOT12 := by
 intro w; cases w; aesop;

/--
Conjugating `Z₁` by `CNOT₂₁` yields `ZZ = Z₁Z₂`.
-/
theorem CNOT21_conj_Z1_eq_ZZ : CNOT21perm ∘ (pinZ 1) ∘ CNOT21perm.symm = ZZ := by
 rfl

/--
**The `⟨ZZ⟩` constraint sublattice is a transported pinned sublattice.**
 `BW₂^{⟨ZZ⟩} = CNOT₂₁(BW₂^{⟨Z₁⟩})`, where `BW₂^{⟨Z₁⟩}` is the rank-one pinned
 sublattice `(1+i)|0⟩ ⊗ BW₁`. This is the kernel-checked `n=2` transport
 instance (repetition-code flavour).
-/
theorem ZZ_lattice_eq_transport :
 {w : Q 2 | InBWn 2 w ∧ ZZ w = w}
 = CNOT21perm '' {w : Q 2 | InBWn 2 w ∧ pinZ 1 w = w} := by
 convert transport_general CNOT21perm ( fun w hw => CNOT21_preserves_BW2 w hw ) ( fun w hw => CNOT21_preserves_BW2 w hw ) ( pinZ 1 ) using 1

/-! ## T1.3 — Bell encoder computation -/

/-- The scaled pinned generator `(1+i)²|00⟩ = 2i·|00⟩` of `BW₂^{⟨Z₁,Z₂⟩}`. -/
def pinnedGen : Q 2 := ((oneI ^ 2, 0), (0, 0))

/--
**The (√2-scaled) Bell encoder image.** `CNOT₁₂ ∘ Had₁` maps the pinned
 generator `(1+i)²|00⟩` to `(1+i)·bellGen = (1+i)²(|00⟩+|11⟩)`. (The genuine
 unitary encoder would land on a unit multiple of `bellGen`; the `√2` scaling
 of `Had₁` accounts for the extra `(1+i)` factor.)
-/
theorem bell_encoder_image : CNOT12 (Had1 pinnedGen) = oneI • bellGen := by
 rfl

/-! ## T1.3 — the Bell code lattice (restatement of `bell_theory`) -/

/-- **Bell code lattice.** `BW₂^{⟨ZZ,XX⟩} = ℤ[i]·bellGen` — the logical lattice
 of the Bell theory is the rank-one `ℤ[i]`-module generated by the scaled Bell
 vector. (This is `bell_theory`, restated in set form for the closure.) -/
theorem bell_code_lattice :
 {w : Q 2 | InBWn 2 w ∧ ZZ w = w ∧ XX w = w}
 = {w : Q 2 | ∃ c : GI, w = c • bellGen} := by
 ext w; simpa using bell_theory w

/-! ## T1.4 — the closure statement (general Clifford transport at any rank) -/

/-- **Transport of a stabiliser predicate.** For a `BW`-automorphism `U` and any
 predicate `P` on `Q n`, the constraint sublattice of the transported predicate
 `P ∘ U⁻¹` is `U` applied to that of `P`. (Generalises `transport_general`
 from a single operator's fixed set to an arbitrary stabiliser theory.) -/
theorem transport_general_set {n : ℕ} (U : Equiv.Perm (Q n))
 (hU : ∀ w, InBWn n w → InBWn n (U w))
 (hUinv : ∀ w, InBWn n w → InBWn n (U.symm w))
 (P : Q n → Prop) :
 {w | InBWn n w ∧ P (U.symm w)} = U '' {w | InBWn n w ∧ P w} := by
 ext w; constructor
 · rintro ⟨hw, hP⟩
 exact ⟨U.symm w, ⟨hUinv w hw, hP⟩, by simp⟩
 · rintro ⟨v, ⟨hv, hP⟩, rfl⟩
 exact ⟨hU v hv, by simpa using hP⟩

/-- **The logical-lattice transport theorem (Theorem 17.6, lattice form).**
 For any `BW`-automorphism `U` of `Q n` and any stabiliser group given as a
 list `S` of commuting operators, the constraint sublattice of the transported
 stabiliser `U S U†` is exactly `U` applied to the constraint sublattice of `S`:
 `BWₙ^{U S U†} = U(BWₙ^S)`. Combined with `pinned_iter` (the kernel-checked
 pinned case at general rank), this closes the general-Clifford transport step
 of Theorem 17.6 at `n = 2` for every stabiliser code reachable by a `BW`
 automorphism (in particular all those built from the generators
 `Z1,Z2,X1,X2,S1,S2,CNOT12,CNOT21,CZ`). -/
theorem logical_lattice_transport {n : ℕ} (U : Equiv.Perm (Q n))
 (hU : ∀ w, InBWn n w → InBWn n (U w))
 (hUinv : ∀ w, InBWn n w → InBWn n (U.symm w))
 (S : List (Q n → Q n)) :
 {w | InBWn n w ∧ ∀ g ∈ S, (U ∘ g ∘ U.symm) w = w}
 = U '' {w | InBWn n w ∧ ∀ g ∈ S, g w = w} := by
 have h := transport_general_set U hU hUinv (fun w => ∀ g ∈ S, g w = w)
 rw [← h]
 ext w
 refine and_congr_right (fun _ => ?_)
 constructor
 · intro hAll g hg
 have := hAll g hg
 have hinj := U.injective
 apply hinj
 simpa [Function.comp] using this
 · intro hAll g hg
 have := hAll g hg
 simp only [Function.comp_apply]
 rw [this, Equiv.apply_symm_apply]

/-- **T1.4 rank-1 instance.** For any `BW`-automorphism `U` of `Q 2`, the
 constraint sublattice of the transported single-`Z` stabiliser is the
 `U`-image of the explicit pinned lattice `(1+i)|0⟩ ⊗ BW₁`. -/
theorem logical_lattice_n2_rank1 (U : Equiv.Perm (Q 2))
 (hU : ∀ w, InBWn 2 w → InBWn 2 (U w))
 (hUinv : ∀ w, InBWn 2 w → InBWn 2 (U.symm w)) :
 {w | InBWn 2 w ∧ (U ∘ pinZ 1 ∘ U.symm) w = w}
 = U '' {w : Q 2 | w.2 = 0 ∧ ∃ a : Q 1, InBWn 1 a ∧ w.1 = oneI • a} := by
 rw [transport_general U hU hUinv (pinZ 1)]
 congr 1; ext w; exact pinned_one 1 w

/-! ## T3 — Bell minimal vectors, cross-checked against the transport machinery -/

/-- **T3 (structural cross-check).** The four minimal vectors of the Bell code
 `BW₂^{⟨ZZ,XX⟩}` are exactly the units times the scaled Bell vector `bellGen`.
 This restates `BWArith.bell_minimal_iff` through the transport-derived
 `bell_code_lattice` description. Together with `bell_encoder_image`
 (`CNOT₁₂(Had₁((1+i)²|00⟩)) = (1+i)·bellGen`) it exhibits the Bell minimal
 vector as the (√2-scaled) encoder image of the pinned minimal generator. -/
theorem bell_minimal_via_transport (w : Q 2) :
 (InBWn 2 w ∧ ZZ w = w ∧ XX w = w ∧ w ≠ 0 ∧ normQ2 w = 4) ↔
 ∃ u : GI, IsUnit u ∧ w = u • bellGen :=
 bell_minimal_iff w

end Transport2
end BWArith