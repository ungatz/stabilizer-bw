import Mathlib
import StabilizerBW.BWFreeModule
import StabilizerBW.LogicalLatticeTransport.BW2Transport

/-!
# General-Clifford transport of the logical lattice at `n = 3`

This file formalises **Target T2** of round R11: the general-Clifford transport
step of Theorem 17.6 at `n = 3`, by direct computation through a small generating
set of the three-qubit Clifford group.

`Q 3 = Q 2 × Q 2` splits off qubit 1 (outer) from qubits 2,3 (the inner `Q 2`).
Qubit-2/3 gates are *lifts* of the two-qubit generators of `BW2Transport.lean`
acting block-wise; qubit-1 gates act on the outer `Q 2 × Q 2` structure.

## Main results

* `lift23_preserves` — a block-wise (qubit 2/3) `ℤ[i]`-linear `BW₂`-automorphism
  lifts to a `BW₃`-automorphism.
* `pinZ_preserves`, `swapBlocks_preserves`, `hadOuter_preserves`,
  `sgateOuter_preserves` — the general outer-qubit structural preservation lemmas.
* `*_preserves_BW3` — each generator in `{H_i, S_i, Z_i (i=1,2,3), CNOT_{12},
  CNOT_{13}, CNOT_{23}}` maps `BW₃` into `BW₃` (**T2.1**).
* `CNOT12g_conj_Z2g_eq_Z1Z2g`, `repetition_code_transport` — the concrete `n=3`
  transport instance: the `⟨Z₁Z₂⟩` constraint sublattice is the `CNOT₁₂`-image of
  the `Z₂`-pinned sublattice (3-qubit repetition-code stabiliser).
* `logical_lattice_transport` (from `BW2Transport`, stated at general `n`) applies
  verbatim at `n = 3` to every stabiliser code reachable by these generators.
-/

open Zsqrtd

namespace BWArith
namespace Transport3

/-- The Gaussian unit `i`. -/
abbrev gi : GI := ⟨0, 1⟩

/-! ## `BWₙ` is an additive subgroup -/

/-
`BWₙ` is closed under addition.
-/
theorem InBWn_add (n : ℕ) (a b : Q n) (ha : InBWn n a) (hb : InBWn n b) :
    InBWn n (a + b) := by
  revert a b ha hb;
  induction' n with n ih;
  · aesop;
  · -- By definition of `InBWn`, we know that if `a` and `b` are in `BWn (n + 1)`, then their second components are in `BWn n`.
    intro a b ha hb
    obtain ⟨ha2, pa, hpa, ha1⟩ := ha
    obtain ⟨hb2, pb, hpb, hb1⟩ := hb;
    refine' ⟨ ih _ _ ha2 hb2, pa + pb, ih _ _ hpa hpb, _ ⟩;
    rw [ show ( a + b ).1 = a.1 + b.1 from rfl, show ( a + b ).2 = a.2 + b.2 from rfl, ha1, hb1 ] ; simp +decide [ add_smul, add_assoc, add_left_comm, add_comm ]

/-- `BWₙ` is closed under negation. -/
theorem InBWn_neg (n : ℕ) (a : Q n) (ha : InBWn n a) : InBWn n (-a) := by
  have := InBWn_smul n (-1) a ha; simpa using this

/-- `BWₙ` is closed under subtraction. -/
theorem InBWn_sub (n : ℕ) (a b : Q n) (ha : InBWn n a) (hb : InBWn n b) :
    InBWn n (a - b) := by
  rw [sub_eq_add_neg]; exact InBWn_add n a (-b) ha (InBWn_neg n b hb)

/-! ## Block-wise lift of qubit-2/3 generators -/

/-- Lift a `Q 2 → Q 2` map to `Q 3 = Q 2 × Q 2` by applying it to both
    qubit-1 blocks (this realises a gate on qubits 2,3). -/
def lift23 (G : Q 2 → Q 2) (w : Q 3) : Q 3 := (G w.1, G w.2)

/-
**A block-wise `ℤ[i]`-linear `BW₂`-automorphism lifts to a `BW₃`-automorphism.**
-/
theorem lift23_preserves (G : Q 2 → Q 2)
    (hlin : ∀ a b : Q 2, G (oneI • a + b) = oneI • G a + G b)
    (hpres : ∀ w, InBWn 2 w → InBWn 2 (G w)) :
    ∀ w : Q 3, InBWn 3 w → InBWn 3 (lift23 G w) := by
  intros w hw;
  obtain ⟨hb, a, ha, h1⟩ := ( BWArith.freeModuleDecomp 2 w ).mp hw;
  unfold lift23;
  rw [ BWArith.freeModuleDecomp ] ; aesop;

/-! ## General outer-qubit (qubit-1) structural lemmas -/

/-
**`Z` on qubit 1 preserves `BWₙ₊₁`** (negating the `|1⟩`-block).
-/
theorem pinZ_preserves (n : ℕ) :
    ∀ w : Q (n+1), InBWn (n+1) w → InBWn (n+1) (pinZ n w) := by
  intro w hw;
  obtain ⟨hw2, a0, ha0, h1⟩ := hw;
  refine' ⟨ _, _, _, _ ⟩;
  exact InBWn_neg n _ hw2;
  exact a0 + ( ⟨ 1, -1 ⟩ : GI ) • w.2;
  · exact InBWn_add n _ _ ha0 ( InBWn_smul n _ _ hw2 );
  · simp +decide [ pinZ, h1, smul_add, smul_smul ];
    rw [ show ( oneI * { re := 1, im := -1 } : GI ) = 2 by decide ] ; norm_num [ two_smul ] ; abel1

/-- Swap of the two leading-qubit blocks (this is `X` on qubit 1). -/
def swapBlocks (n : ℕ) (w : Q (n+1)) : Q (n+1) := (w.2, w.1)

/-
**`X` on qubit 1 preserves `BWₙ₊₁`.**
-/
theorem swapBlocks_preserves (n : ℕ) :
    ∀ w : Q (n+1), InBWn (n+1) w → InBWn (n+1) (swapBlocks n w) := by
  intro w hw; rw [freeModuleDecomp] at hw; obtain ⟨a, b, ha, hb, hw⟩ := hw; simp_all +decide [ swapBlocks ] ;
  refine' ⟨ _, _ ⟩;
  · exact InBWn_add n _ _ ( InBWn_smul n oneI a ha ) hb;
  · refine' ⟨ -a, _, _ ⟩ <;> simp_all +decide [ InBWn_neg ]

/-- The outer (qubit-1) integer Hadamard `(B₀,B₁) ↦ (B₀+B₁, B₀-B₁)`. -/
def hadOuter (n : ℕ) (w : Q (n+1)) : Q (n+1) := (w.1 + w.2, w.1 - w.2)

/-
**`√2·H` on qubit 1 preserves `BWₙ₊₁`.**
-/
theorem hadOuter_preserves (n : ℕ) :
    ∀ w : Q (n+1), InBWn (n+1) w → InBWn (n+1) (hadOuter n w) := by
  -- By definition of InBWn, we know that if w is in InBWn (n + 1), then its components are in InBWn n.
  intro w hw
  obtain ⟨a, b, ha, hb, hw_eq⟩ : ∃ a b : Q n, InBWn n a ∧ InBWn n b ∧ w = (oneI • a + b, b) := by
    exact (freeModuleDecomp n w).mp hw
  unfold hadOuter;
  simp_all +decide [ InBWn ];
  refine' ⟨ _, _ ⟩;
  · exact InBWn_smul n oneI a ha;
  · refine' ⟨ ( ⟨ 1, -1 ⟩ : GI ) • b, _, _ ⟩;
    · convert InBWn_smul n _ _ hb using 1;
    · rw [ show ( ⟨ 1, 1 ⟩ : GI ) • ( ⟨ 1, -1 ⟩ : GI ) • b = 2 • b by
            rw [ ← smul_assoc ] ; norm_num [ two_smul ];
            exact show ( 2 : GI ) • b = b + b from by rw [ two_smul ] ; ] ; abel_nf

/-- The outer (qubit-1) phase gate `(B₀,B₁) ↦ (B₀, i·B₁)`. -/
def sgateOuter (n : ℕ) (w : Q (n+1)) : Q (n+1) := (w.1, gi • w.2)

/-
**`S` on qubit 1 preserves `BWₙ₊₁`.**
-/
theorem sgateOuter_preserves (n : ℕ) :
    ∀ w : Q (n+1), InBWn (n+1) w → InBWn (n+1) (sgateOuter n w) := by
  intro w hw;
  obtain ⟨hw2, a0, ha0, h1⟩ := hw;
  refine' ⟨ _, _ ⟩;
  · exact InBWn_smul n gi w.2 hw2;
  · refine' ⟨ a0 + ( -gi ) • w.2, _, _ ⟩;
    · convert InBWn_add n a0 ( -gi • w.2 ) ha0 ( InBWn_smul n ( -gi ) w.2 hw2 ) using 1;
    · simp +decide [ h1, sgateOuter, oneI ];
      simp +decide [ add_assoc, add_left_comm, add_comm, smul_smul, show ( { re := 1, im := 1 } : GI ) * gi = -⟨ 1, -1 ⟩ by decide ];
      simp +decide [ ← add_assoc, ← smul_assoc, show ( { re := 1, im := 1 } : GI ) + { re := 1, im := -1 } = 2 by decide ];
      rw [ add_right_comm, ← add_smul ] ; congr ; norm_cast;
      erw [ show ( gi + { re := 1, im := Int.negSucc 0 } : GI ) = 1 by decide ] ; norm_num

/-! ## The three-qubit generating set on `Q 3` -/

/-- `Z` on qubit 1. -/
def Z1g : Q 3 → Q 3 := pinZ 2
/-- `Z` on qubit 2 (block-wise lift). -/
def Z2g : Q 3 → Q 3 := lift23 Transport2.Z1
/-- `Z` on qubit 3 (block-wise lift). -/
def Z3g : Q 3 → Q 3 := lift23 Transport2.Z2
/-- `√2·H` on qubit 1. -/
def Had1g : Q 3 → Q 3 := hadOuter 2
/-- `√2·H` on qubit 2 (block-wise lift). -/
def Had2g : Q 3 → Q 3 := lift23 Transport2.Had1
/-- `√2·H` on qubit 3 (block-wise lift). -/
def Had3g : Q 3 → Q 3 := lift23 Transport2.Had2
/-- `S` on qubit 1. -/
def S1g : Q 3 → Q 3 := sgateOuter 2
/-- `S` on qubit 2 (block-wise lift). -/
def S2g : Q 3 → Q 3 := lift23 Transport2.S1
/-- `S` on qubit 3 (block-wise lift). -/
def S3g : Q 3 → Q 3 := lift23 Transport2.S2
/-- `CNOT` control 2, target 3 (block-wise lift). -/
def CNOT23g : Q 3 → Q 3 := lift23 Transport2.CNOT12
/-- `CNOT` control 1, target 2: flip qubit 2 inside the qubit-1 `|1⟩`-block. -/
def CNOT12g (w : Q 3) : Q 3 := (w.1, Transport2.X1 w.2)
/-- `CNOT` control 1, target 3: flip qubit 3 inside the qubit-1 `|1⟩`-block. -/
def CNOT13g (w : Q 3) : Q 3 := (w.1, Transport2.X2 w.2)

/-! ## T2.1 — generators preserve `BW₃` -/

theorem Z1g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (Z1g w) := by
  convert pinZ_preserves 2 using 1

theorem Z2g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (Z2g w) := by
  convert lift23_preserves Transport2.Z1 _ Transport2.Z1_preserves_BW2 using 1;
  intro a b; rcases a with ⟨ ⟨ a1, a2 ⟩, ⟨ a3, a4 ⟩ ⟩ ; rcases b with ⟨ ⟨ b1, b2 ⟩, ⟨ b3, b4 ⟩ ⟩ ; simp +decide [ Transport2.Z1, Prod.smul_mk, smul_eq_mul, mul_add ] ;
  erw [ Prod.mk_add_mk, Prod.mk_add_mk ] ; ring;
  erw [ Prod.smul_mk, Prod.smul_mk ] ; norm_num ; ring;
  congr <;> ring;
  · erw [ Prod.smul_mk ] ; norm_num ; ring;
    exact neg_add _ _;
  · erw [ Prod.smul_mk ] ; norm_num ; ring;
    exact neg_add _ _

theorem Z3g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (Z3g w) := by
  convert lift23_preserves _ _ _ using 1;
  · unfold Transport2.Z2;
    simp [Q];
    exact fun _ _ _ _ => ⟨ add_comm _ _, add_comm _ _ ⟩;
  · exact fun w a => Transport2.Z2_preserves_BW2 w a

theorem Had1g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (Had1g w) := by
  convert hadOuter_preserves 2 using 1

theorem Had2g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (Had2g w) := by
  convert lift23_preserves Transport2.Had1 _ Transport2.Had1_preserves_BW2;
  simp +decide [ Transport2.Had1 ];
  simp +decide [ Prod.ext_iff, BWArith.Q ];
  grind

theorem Had3g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (Had3g w) := by
  intros w hw; exact lift23_preserves Transport2.Had2 (by
  simp +decide [ Transport2.Had2 ];
  simp +decide [ Q, Prod.ext_iff ];
  grind) (Transport2.Had2_preserves_BW2) w hw;

theorem S1g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (S1g w) := by
  exact sgateOuter_preserves 2

theorem S2g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (S2g w) := by
  intros w hw
  apply lift23_preserves Transport2.S1 (by
  unfold Transport2.S1;
  simp +decide [ Prod.ext_iff, BWArith.Q ];
  exact fun a b c d => ⟨ by ring, by ring ⟩) (by
  exact Transport2.S1_preserves_BW2) w hw

theorem S3g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (S3g w) := by
  convert Transport3.lift23_preserves _ _ _ using 2;
  · simp +decide [ Transport2.S2, Prod.ext_iff ];
    simp +decide [ Prod.ext_iff, BWArith.Q ];
    grind;
  · exact fun w a => Transport2.S2_preserves_BW2 w a

theorem CNOT23g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (CNOT23g w) := by
  intro w hw
  exact (by
  convert Transport3.lift23_preserves Transport2.CNOT12 _ _ w hw using 1;
  · aesop;
  · exact Transport2.CNOT12_preserves_BW2)

/-
For `v ∈ BW₂`, `v - X₂v ∈ (1+i)·BW₂` (used for `CNOT₁₂` preservation).
-/
theorem X1_diff_oneI (v : Q 2) (hv : InBWn 2 v) :
    ∃ δ : Q 2, InBWn 2 δ ∧ v - Transport2.X1 v = oneI • δ := by
      obtain ⟨c, d, e, f, hv⟩ : ∃ c d e f : GI, v = ((c, d), (e, f)) ∧ oneI ∣ (e - f) ∧ oneI ∣ (c - e) ∧ oneI ∣ (d - f) ∧ (2 : GI) ∣ (c - d - e + f) := by
        rcases v with ⟨ ⟨ c, d ⟩, ⟨ e, f ⟩ ⟩ ; use c, d, e, f; simp_all +decide [ Transport2.inBW2_iff ] ;
      obtain ⟨x, hx⟩ : ∃ x : GI, c - e = oneI * x := hv.2.2.1
      obtain ⟨y, hy⟩ : ∃ y : GI, d - f = oneI * y := hv.2.2.2.1
      use ((x, y), (-x, -y));
      constructor;
      · rw [ Transport2.inBW2_iff ];
        have h_div : oneI ∣ (x - y) := by
          have h_div : oneI ^ 2 ∣ oneI * (x - y) := by
            have h_div : oneI ^ 2 ∣ (c - d - e + f) := by
              obtain ⟨ k, hk ⟩ := hv.2.2.2.2; use k * ⟨ 0, -1 ⟩ ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
            convert h_div using 1 ; rw [ show c - d - e + f = oneI * ( x - y ) by linear_combination' hx - hy ];
          exact Exists.elim h_div fun k hk => ⟨ k, mul_left_cancel₀ ( show oneI ≠ 0 from by decide ) <| by linear_combination' hk ⟩;
        have h_div2 : oneI ∣ (2 : GI) := by
          exact ⟨ ⟨ 1, -1 ⟩, by decide ⟩;
        exact ⟨ by convert h_div.neg_right using 1; ring, by convert h_div2.mul_left x using 1; ring, by convert h_div2.mul_left y using 1; ring, by convert dvd_mul_right ( 2 : GI ) ( x - y ) using 1; ring ⟩;
      · simp_all +decide [ sub_eq_iff_eq_add, Transport2.X1 ];
        erw [ Prod.mk_add_mk, Prod.mk_add_mk ];
        erw [ Prod.mk_add_mk ] ; norm_num

/-
For `v ∈ BW₂`, `v - X₃v ∈ (1+i)·BW₂` (used for `CNOT₁₃` preservation).
-/
theorem X2_diff_oneI (v : Q 2) (hv : InBWn 2 v) :
    ∃ δ : Q 2, InBWn 2 δ ∧ v - Transport2.X2 v = oneI • δ := by
      obtain ⟨a, b, c, d, hv⟩ : ∃ a b c d : GI, v = ((a, b), (c, d)) ∧ oneI ∣ (c - d) ∧ oneI ∣ (a - c) ∧ oneI ∣ (b - d) ∧ (2 : GI) ∣ (a - b - c + d) := by
        rcases v with ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩ ; use a, b, c, d; simp_all +decide [ Transport2.inBW2_iff ] ;
      -- Define `δ` as `((x, -x),(y, -y))` where `x = (a - d)/oneI` and `y = (c - b)/oneI`.
      obtain ⟨x, hx⟩ : ∃ x : GI, a - b = oneI * x := by
        have h_div : oneI ∣ (a - c) - (b - d) := by
          exact dvd_sub hv.2.2.1 hv.2.2.2.1;
        exact ⟨ h_div.choose + hv.2.1.choose, by linear_combination' h_div.choose_spec + hv.2.1.choose_spec ⟩
      obtain ⟨y, hy⟩ : ∃ y : GI, c - d = oneI * y := by
        exact hv.2.1
      use ((x, -x), (y, -y));
      have h_div : oneI ∣ (x - y) := by
        obtain ⟨ k, hk ⟩ := hv.2.2.2.2;
        simp_all +decide [ mul_comm, mul_assoc, mul_left_comm ];
        rw [ show x - y = k * 2 / oneI from _ ];
        · rw [ show ( 2 : GI ) = oneI * ⟨ 1, -1 ⟩ by decide ];
          rw [ mul_left_comm, mul_div_cancel_left₀ ] <;> norm_num [ oneI ];
          · exact dvd_mul_of_dvd_right ( by exact ⟨ ⟨ 0, -1 ⟩, by decide ⟩ ) _;
          · decide +revert;
        · rw [ ← hk, show x * oneI - c + d = ( x - y ) * oneI by linear_combination' -hy ];
          exact Eq.symm ( mul_div_cancel_right₀ _ ( by decide ) );
      constructor;
      · rw [ Transport2.inBW2_iff ];
        simp_all +decide [ ← two_mul, dvd_mul_of_dvd_left ];
        exact ⟨ dvd_mul_of_dvd_left ( by exact ⟨ ⟨ 1, -1 ⟩, by decide ⟩ ) _, by simpa [ neg_add_eq_sub ] using h_div.neg_right, by exact ⟨ x - y, by ring ⟩ ⟩;
      · simp_all +decide [ sub_eq_iff_eq_add, Transport2.X2 ];
        erw [ Prod.mk_add_mk, Prod.mk_add_mk ] ; ring;
        erw [ Prod.mk_add_mk ] ; ring;
        simp +decide [ mul_add, add_assoc, add_left_comm, add_comm ]

theorem CNOT12g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (CNOT12g w) := by
  intro w hw
  obtain ⟨hb, a0, ha0, h1⟩ := freeModuleDecomp 2 w |>.1 hw;
  obtain ⟨δ, hδ, hdiff⟩ := X1_diff_oneI a0 h1.1;
  refine' freeModuleDecomp 2 _ |>.2 ⟨ hb + δ, Transport2.X1 a0, _, _, _ ⟩ <;> simp_all +decide [ add_assoc ];
  · exact InBWn_add 2 hb δ ha0 hδ
  · exact Transport2.X1_preserves_BW2 _ h1.1;
  · simp +decide [ ← hdiff, CNOT12g ]

theorem CNOT13g_preserves_BW3 : ∀ w : Q 3, InBWn 3 w → InBWn 3 (CNOT13g w) := by
  intros w hw
  obtain ⟨hb, a0, ha0, h1⟩ := (freeModuleDecomp 2 w).mp hw;
  obtain ⟨δ, hδ, hdiff⟩ := X2_diff_oneI a0 h1.1;
  refine' freeModuleDecomp 2 _ |>.2 ⟨ _, _, _, _ ⟩;
  exact hb + δ;
  exact Transport2.X2 a0;
  · exact InBWn_add 2 hb δ ha0 hδ
  · refine' ⟨ Transport2.X2_preserves_BW2 _ h1.1, _ ⟩;
    simp +decide [ CNOT13g, h1.2, hdiff.symm, smul_add, add_assoc ]

/-! ## T2 — concrete repetition-code transport at `n = 3` -/

/-
`CNOT₁₂` (qubit-1 control) is an involution.
-/
theorem CNOT12g_involutive : Function.Involutive CNOT12g := by
  intro w
  unfold CNOT12g
  simp [Transport2.X1]

/-- `CNOT₁₂` as a permutation of `Q 3`. -/
def CNOT12gperm : Equiv.Perm (Q 3) := Function.Involutive.toPerm CNOT12g CNOT12g_involutive

/-- The repetition-code stabiliser `Z₁Z₂` (`Z` on qubits 1 and 2). -/
def Z1Z2g : Q 3 → Q 3 := Z1g ∘ Z2g

/-
**Conjugating `Z₂` by `CNOT₁₂` yields `Z₁Z₂`** — the bit-flip/repetition code.
-/
theorem CNOT12g_conj_Z2g_eq_Z1Z2g :
    CNOT12gperm ∘ Z2g ∘ CNOT12gperm.symm = Z1Z2g := by
      unfold CNOT12gperm;
      funext w; rcases w with ⟨w1, ⟨⟨c,d⟩,⟨e,f⟩⟩⟩; simp [Function.comp, Equiv.symm_apply_eq];
      unfold CNOT12g Z2g Z1Z2g; simp +decide [ Transport2.CNOT12, Transport2.Z1 ] ;
      unfold lift23 Transport2.X1 Transport2.Z1 Z1g Z2g; simp +decide [ Transport2.X1, Transport2.Z1 ] ;
      unfold lift23 Transport2.Z1 pinZ; simp +decide [ Transport2.Z1 ] ;
      congr;
      · grind;
      · grind +splitIndPred

/-
**The 3-qubit repetition-code constraint sublattice is a transported pinned
    sublattice.**  `BW₃^{⟨Z₁Z₂⟩} = CNOT₁₂(BW₃^{⟨Z₂⟩})`.
-/
theorem repetition_code_transport :
    {w : Q 3 | InBWn 3 w ∧ Z1Z2g w = w}
      = CNOT12gperm '' {w : Q 3 | InBWn 3 w ∧ Z2g w = w} := by
  -- Apply the transport lemma with U = CNOT12gperm, g = Z2g, and the key conjugation identity.
  have h := Transport2.transport_general CNOT12gperm (fun w hw => CNOT12g_preserves_BW3 w hw) (fun w hw => CNOT12g_preserves_BW3 w hw) Z2g;
  rw [CNOT12g_conj_Z2g_eq_Z1Z2g] at h;
  exact h;

end Transport3
end BWArith