/-
# PauliLogic/Completeness.lean — Completeness of PL_n (R10, T1–T3)

The completeness half of Theorem 17.14 (`thm:av-pl-complete`): every VALID
stabilizer entailment `Γ ⊢ Q` has a derivation in `PL_n`.

The proof follows `proofs/PauliLogic_T3_Soundness_Completeness.md`, but uses a
streamlined trace identity that avoids dimension/kernel counting:

* `gen Γ a` is the signed subset product of the generators selected by
  `a : Fin Γ.length → Bool`.  The set `⟨Γ⟩` is `{ gen Γ a | a }`.
* `ptrace P` is the (basis) trace of the Pauli operator `pauliAction P`; it
  equals `2^n` if `P = +I`, `-2^n` if `P = -I`, and `0` otherwise.
* The averaged operator `stabSum Γ = Σ_a pauliAction (gen Γ a)` has
  `trace = 2^n · #{a : gen Γ a = +I} ≠ 0` (when `-I ∉ ⟨Γ⟩`), giving a nonzero
  stabilizer vector, and is fixed by `Q` when `Γ ⊢ Q` is valid.  Taking traces
  of `Q · stabSum = stabSum` yields `#{a : gen a = Q} = #{a : gen a = +I} +
  #{a : gen a = -Q} ≥ 1`, hence `Q ∈ ⟨Γ⟩`.
-/

import Mathlib
import StabilizerBW.PauliLogic.Soundness
import StabilizerBW.PauliLogic.CutElimination
import StabilizerBW.PauliLogic.Tableau

open scoped BigOperators
open Classical

set_option maxHeartbeats 1600000

namespace PauliLogic

/-! ## Validity -/

/-- The sequent `Γ ⊢ Q` is VALID: every joint `+1`-eigenvector of `Γ` is a
    `+1`-eigenvector of `Q`. -/
def Valid {n : ℕ} (Γ : List (Pauli n)) (Q : Pauli n) : Prop :=
  ∀ v ∈ V Γ, pauliAction Q v = v

/-! ## Total multiplication of Pauli words

`Pauli.mul` carries the commutation hypothesis, but its *body* never uses it.
`mulRaw` is the same operation without the hypothesis, which is convenient for
defining the generated group (where we do not always have the proof inline). -/

/-- Total product of two Pauli words (ignores commutation; equals `Pauli.mul`
    when the operands commute). -/
def mulRaw {n : ℕ} (p q : Pauli n) : Pauli n :=
  { sign := xor (xor p.sign q.sign) (decide (phaseZ p q % 4 = 2))
    xs := mulXs p q
    zs := mulZs p q }

@[simp] theorem mul_eq_mulRaw {n : ℕ} (p q : Pauli n) (h : p.commutes q = true) :
    Pauli.mul p q h = mulRaw p q := rfl

theorem mulRaw_self {n : ℕ} (p : Pauli n) : mulRaw p p = pauliI n := by
  rw [← mul_eq_mulRaw p p (Pauli.commutes_self p)]; exact Pauli.mul_self p _

theorem mulRaw_one {n : ℕ} (p : Pauli n) : mulRaw p (pauliI n) = p := by
  unfold mulRaw pauliI;
  unfold phaseZ; simp +decide [ mulXs, mulZs ] ;
  unfold numY numYmul crossZX mulXs mulZs; simp +decide ;

theorem one_mulRaw {n : ℕ} (p : Pauli n) : mulRaw (pauliI n) p = p := by
  unfold mulRaw; simp +decide [ mulXs, mulZs, pauliI ] ;
  unfold phaseZ; simp +decide [ numY, numYmul, crossZX ] ;
  unfold mulXs mulZs; simp +decide [ Finset.sum_ite ] ;

theorem mulRaw_comm {n : ℕ} (p q : Pauli n) (h : p.commutes q = true) :
    mulRaw p q = mulRaw q p := by
  rw [← mul_eq_mulRaw p q h, ← mul_eq_mulRaw q p (by rw [Pauli.commutes_symm]; exact h)]
  exact Pauli.mul_comm p q h _

theorem mulRaw_assoc {n : ℕ} (p q r : Pauli n)
    (hpq : p.commutes q = true) (hpr : p.commutes r = true) (hqr : q.commutes r = true) :
    mulRaw (mulRaw p q) r = mulRaw p (mulRaw q r) := by
  rw [← mul_eq_mulRaw p q hpq, ← mul_eq_mulRaw q r hqr]
  rw [← mul_eq_mulRaw _ r (commutes_mul_left hpq hpr hqr),
      ← mul_eq_mulRaw p _ (commutes_mul_right hqr hpq hpr)]
  exact Pauli.mul_assoc p q r hpq hpr hqr

/-- `commutes` ignores the sign; `mulRaw` only changes the sign relative to the
    XOR of bit-vectors, so it interacts with `commutes` exactly like
    `Pauli.mul`. -/
theorem mulRaw_commutes_left {n : ℕ} {p q r : Pauli n}
    (hpq : p.commutes q = true) (hpr : p.commutes r = true) (hqr : q.commutes r = true) :
    (mulRaw p q).commutes r = true := by
  rw [← mul_eq_mulRaw p q hpq]; exact commutes_mul_left hpq hpr hqr

theorem mulRaw_commutes_right {n : ℕ} {p q r : Pauli n}
    (hqr : q.commutes r = true) (hpq : p.commutes q = true) (hpr : p.commutes r = true) :
    p.commutes (mulRaw q r) = true := by
  rw [← mul_eq_mulRaw q r hqr]; exact commutes_mul_right hqr hpq hpr

/-! ## The generated stabilizer group `⟨Γ⟩` -/

/-- Signed subset product of the generators of `Γ` indexed by `L`, selected by
    `a`.  (Indices in `L` with `a i = false` are skipped.) -/
def genOn {n : ℕ} (Γ : List (Pauli n)) (L : List (Fin Γ.length))
    (a : Fin Γ.length → Bool) : Pauli n :=
  L.foldr (fun i acc => if a i then mulRaw (Γ.get i) acc else acc) (pauliI n)

/-- The signed subset product of `Γ` selected by `a : Fin Γ.length → Bool`. -/
def gen {n : ℕ} (Γ : List (Pauli n)) (a : Fin Γ.length → Bool) : Pauli n :=
  genOn Γ (List.finRange Γ.length) a

/-- A commuting context: all generators pairwise commute. -/
def Commuting {n : ℕ} (Γ : List (Pauli n)) : Prop :=
  ∀ i j : Fin Γ.length, (Γ.get i).commutes (Γ.get j) = true

/-! ### Commutation within `⟨Γ⟩` -/

theorem get_commutes_genOn {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ)
    (k : Fin Γ.length) (L : List (Fin Γ.length)) (a : Fin Γ.length → Bool) :
    (Γ.get k).commutes (genOn Γ L a) = true := by
  induction' L with i L ih generalizing k;
  · unfold genOn;
    simp +decide [ Pauli.commutes, crossZX, pauliI ];
  · by_cases hi : a i <;> simp_all +decide [ genOn ];
    apply mulRaw_commutes_right;
    · exact ih i;
    · exact hcomm k i;
    · exact ih k

theorem genOn_commutes_genOn {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ)
    (L M : List (Fin Γ.length)) (a b : Fin Γ.length → Bool) :
    (genOn Γ L a).commutes (genOn Γ M b) = true := by
  induction' L with i L ih generalizing M;
  · -- The identity element commutes with any element, so the commutation relation holds trivially.
    simp [genOn, Pauli.commutes];
    unfold crossZX; simp +decide [ pauliI ] ;
  · by_cases hi : a i <;> simp +decide [ *, genOn ];
    · apply mulRaw_commutes_left;
      · convert get_commutes_genOn hcomm i L a using 1;
      · convert get_commutes_genOn hcomm i M b using 1;
      · convert ih M using 1;
    · convert ih M using 1

theorem gen_commutes_gen {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ)
    (a b : Fin Γ.length → Bool) : (gen Γ a).commutes (gen Γ b) = true :=
  genOn_commutes_genOn hcomm _ _ a b

/-! ### Group laws of `⟨Γ⟩` -/

/-
Closure: the product of two subset products is the subset product of the
    XOR of the index sets.
-/
theorem genOn_closure {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ)
    (L : List (Fin Γ.length)) (a b : Fin Γ.length → Bool) :
    mulRaw (genOn Γ L a) (genOn Γ L b)
      = genOn Γ L (fun i => xor (a i) (b i)) := by
  induction' L with i L ih generalizing a b <;> simp_all +decide [ genOn ];
  · exact mulRaw_self _;
  · have h_comm : (Γ.get i).commutes (List.foldr (fun i acc => if a i = true then mulRaw Γ[↑i] acc else acc) (pauliI n) L) = true ∧ (Γ.get i).commutes (List.foldr (fun i acc => if b i = true then mulRaw Γ[↑i] acc else acc) (pauliI n) L) = true ∧ (List.foldr (fun i acc => if a i = true then mulRaw Γ[↑i] acc else acc) (pauliI n) L).commutes (List.foldr (fun i acc => if b i = true then mulRaw Γ[↑i] acc else acc) (pauliI n) L) = true := by
      exact ⟨ get_commutes_genOn hcomm i L a, get_commutes_genOn hcomm i L b, genOn_commutes_genOn hcomm L L a b ⟩;
    rw [ ← ih ];
    obtain ⟨hpA0, hpB0, hAB0⟩ := h_comm
    set p := Γ[↑i] with hp
    set gA := List.foldr (fun i acc => if a i = true then mulRaw Γ[↑i] acc else acc) (pauliI n) L
      with hgA
    set gB := List.foldr (fun i acc => if b i = true then mulRaw Γ[↑i] acc else acc) (pauliI n) L
      with hgB
    have hpA : p.commutes gA = true := hpA0
    have hpB : p.commutes gB = true := hpB0
    have hAB : gA.commutes gB = true := hAB0
    have hAp : gA.commutes p = true := by rw [Pauli.commutes_symm]; exact hpA
    have hpp : p.commutes p = true := Pauli.commutes_self p
    have hFT : mulRaw gA (mulRaw p gB) = mulRaw p (mulRaw gA gB) := by
      rw [← mulRaw_assoc gA p gB hAp hAB hpB, mulRaw_comm gA p hAp,
        mulRaw_assoc p gA gB hpA hpB hAB]
    rcases hai : a i with _ | _ <;> rcases hbi : b i with _ | _ <;>
      simp only [hai, hbi, reduceCtorEq, eq_self_iff_true, reduceIte]
    · exact hFT
    · exact mulRaw_assoc p gA gB hpA hpB hAB
    · show mulRaw (mulRaw p gA) (mulRaw p gB) = mulRaw gA gB
      have hpAB : p.commutes (mulRaw gA gB) = true := mulRaw_commutes_right hAB hpA hpB
      have hpgB : p.commutes (mulRaw p gB) = true := mulRaw_commutes_right hpB hpp hpB
      have hAgB : gA.commutes (mulRaw p gB) = true := mulRaw_commutes_right hpB hAp hAB
      rw [mulRaw_assoc p gA (mulRaw p gB) hpA hpgB hAgB, hFT,
        ← mulRaw_assoc p p (mulRaw gA gB) hpp hpAB hpAB, mulRaw_self p, one_mulRaw]

theorem gen_closure {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ)
    (a b : Fin Γ.length → Bool) :
    mulRaw (gen Γ a) (gen Γ b) = gen Γ (fun i => xor (a i) (b i)) :=
  genOn_closure hcomm _ a b

@[simp] theorem gen_zero {n : ℕ} (Γ : List (Pauli n)) :
    gen Γ (fun _ => false) = pauliI n := by
  unfold gen;
  induction' ( List.finRange Γ.length ) with i L ih <;> simp_all +decide [ genOn ]

/-
The single-generator selector reproduces `Γ.get k`.
-/
theorem gen_single {n : ℕ} {Γ : List (Pauli n)} (k : Fin Γ.length) :
    gen Γ (fun i => decide (i = k)) = Γ.get k := by
  -- We'll use induction on the length of the list.
  have h_ind : ∀ (L : List (Fin Γ.length)), List.Nodup L → ∀ (k : Fin Γ.length), k ∈ L → (L.foldr (fun i acc => if i = k then mulRaw (Γ.get i) acc else acc) (pauliI n)) = Γ.get k := by
    intros L hL k hk;
    induction' L with i L ih;
    · contradiction;
    · have h_foldr : ∀ (L : List (Fin Γ.length)), List.Nodup L → ∀ (k : Fin Γ.length), k ∉ L → (L.foldr (fun i acc => if i = k then mulRaw (Γ.get i) acc else acc) (pauliI n)) = pauliI n := by
        intros L hL k hk; induction' L with i L ih <;> simp_all +decide [ List.foldr ] ;
        aesop;
      grind +suggestions;
  convert h_ind ( List.finRange Γ.length ) ( List.nodup_finRange _ ) k ( List.mem_finRange _ ) using 1;
  unfold gen genOn; aesop;

/-! ## Pauli operators: linearity, sums, traces -/

theorem pauliAction_add {n : ℕ} (P : Pauli n) (u v : Vec n) :
    pauliAction P (u + v) = pauliAction P u + pauliAction P v := by
  funext c; simp [pauliAction]; ring

theorem pauliAction_sum {n : ℕ} {ι : Type*} (P : Pauli n) (s : Finset ι)
    (f : ι → Vec n) :
    pauliAction P (∑ i ∈ s, f i) = ∑ i ∈ s, pauliAction P (f i) := by
  induction' s using Finset.induction with i s hi ih;
  · unfold pauliAction; aesop;
  · simp +decide [ *, Finset.sum_insert hi, pauliAction_add ]

theorem pauliAction_smul {n : ℕ} (P : Pauli n) (z : ℂ) (v : Vec n) :
    pauliAction P (z • v) = z • pauliAction P v := by
  funext c; simp [pauliAction]; ring

/-
A stabilizer vector is fixed by every element of `⟨Γ⟩`.
-/
theorem genOn_fixes {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ)
    {v : Vec n} (hv : v ∈ V Γ) (L : List (Fin Γ.length)) (a : Fin Γ.length → Bool) :
    pauliAction (genOn Γ L a) v = v := by
  induction' L with i L ih generalizing a;
  · unfold genOn; aesop;
  · by_cases hi : a i <;> simp_all +decide [ genOn ];
    rw [ ← mul_eq_mulRaw ];
    rw [ pauliAction_mul, ih ];
    · exact hv _ ( List.get_mem _ _ );
    · convert get_commutes_genOn hcomm i L a using 1

theorem gen_fixes {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ)
    {v : Vec n} (hv : v ∈ V Γ) (a : Fin Γ.length → Bool) :
    pauliAction (gen Γ a) v = v :=
  genOn_fixes hcomm hv _ a

/-- The computational-basis indicator vector. -/
def basisVec {n : ℕ} (c : Fin n → Bool) : Vec n := fun d => if d = c then 1 else 0

/-- The (basis) trace of a linear operator on `Vec n`. -/
noncomputable def mtrace {n : ℕ} (f : Vec n → Vec n) : ℂ :=
  ∑ c : Fin n → Bool, f (basisVec c) c

theorem mtrace_zero {n : ℕ} : mtrace (fun _ : Vec n => (0 : Vec n)) = 0 := by
  simp [mtrace]

/-
Trace is additive over finite sums of operators.
-/
theorem mtrace_sum {n : ℕ} {ι : Type*} (s : Finset ι) (F : ι → (Vec n → Vec n)) :
    mtrace (fun v => ∑ i ∈ s, F i v) = ∑ i ∈ s, mtrace (F i) := by
  unfold mtrace; simp +decide [ Finset.sum_apply, Finset.mul_sum _ _ _ ] ;
  exact Finset.sum_comm

/-- The trace of a Pauli operator. -/
noncomputable def ptrace {n : ℕ} (P : Pauli n) : ℂ := mtrace (pauliAction P)

/-
Character sum: `Σ_c (-1)^{⟨z,c⟩}` is `2^n` if `z = 0`, else `0`.
-/
theorem sum_neg_one_zdot {n : ℕ} (z : Fin n → Bool) :
    (∑ c : Fin n → Bool, (-1 : ℂ) ^ (zdot z c))
      = if z = (fun _ => false) then (2 ^ n : ℂ) else 0 := by
  -- By definition of $zdot$, we can rewrite the sum as a product of sums.
  have h_prod : ∑ c : Fin n → Bool, (-1 : ℂ) ^ (zdot z c) = ∏ j : Fin n, (∑ b : Bool, (-1 : ℂ) ^ (if z j then b.toNat else 0)) := by
    rw [ Finset.prod_sum ];
    refine' Finset.sum_bij ( fun c _ => fun j _ => c j ) _ _ _ _ <;> simp +decide [ zdot ];
    · simp +decide [ funext_iff ];
    · exact fun b => ⟨ fun j => b j ( Finset.mem_univ j ), rfl ⟩;
    · intro a; rw [ ← Finset.prod_pow_eq_pow_sum ] ; congr; ext j; aesop;
  by_cases h : z = fun _ => false <;> simp_all +decide [ Finset.prod_eq_zero_iff ];
  exact Function.ne_iff.mp h |> Exists.imp fun x hx => by simpa using hx;

/-
The trace of a Pauli operator: `2^n` for `+I`, `-2^n` for `-I`, else `0`.
-/
theorem ptrace_eq {n : ℕ} (P : Pauli n) :
    ptrace P = (if P = pauliI n then (2 ^ n : ℂ)
                else if P = pauliMinusI n then -(2 ^ n : ℂ) else 0) := by
  split_ifs <;> simp_all +decide [ ptrace ];
  · unfold mtrace; simp +decide [ pauliAction_I ] ;
    simp +decide [ basisVec ];
  · unfold mtrace; simp +decide [ *, pauliAction_minusI ] ;
    unfold basisVec; simp +decide [ Finset.card_univ ] ;
  · -- By definition of trace, we can express it as a sum over basis vectors.
    have h_trace : mtrace (pauliAction P) = ∑ c : Fin n → Bool, (-1 : ℂ) ^ (P.sign.toNat) * Complex.I ^ (numY P) * (-1 : ℂ) ^ (zdot P.zs (xorv c P.xs)) * (if xorv c P.xs = c then 1 else 0) := by
      refine' Finset.sum_congr rfl fun c _ => _;
      unfold pauliAction;
      unfold coeff basisVec; aesop;
    by_cases h : P.xs = fun _ => false <;> simp_all +decide [ xorv ];
    · by_cases h' : P.zs = fun _ => false <;> simp_all +decide [ numY ];
      · cases P ; simp_all +decide [ pauliI, pauliMinusI ];
        exact False.elim <| ‹¬_› <| by congr;
      · rw [ ← Finset.mul_sum _ _ _, sum_neg_one_zdot ] ; aesop;
    · rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ funext_iff, xorv ];
      exact h.imp fun x hx => by simp +decide [ hx ] ;

/-! ## The averaged stabilizer operator -/

/-- The unnormalised projector `Σ_{g ∈ ⟨Γ⟩} g` (summed over selectors). -/
noncomputable def stabSum {n : ℕ} (Γ : List (Pauli n)) : Vec n → Vec n :=
  fun v => ∑ a : (Fin Γ.length → Bool), pauliAction (gen Γ a) v

theorem stabSum_invariant {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ)
    (a₀ : Fin Γ.length → Bool) (v : Vec n) :
    pauliAction (gen Γ a₀) (stabSum Γ v) = stabSum Γ v := by
  rw [ show stabSum Γ v = ∑ a : Fin Γ.length → Bool, pauliAction ( gen Γ a ) v from rfl, pauliAction_sum ];
  apply Finset.sum_bij (fun a _ => fun i => xor (a₀ i) (a i));
  · exact fun _ _ => Finset.mem_univ _;
  · simp +contextual [ funext_iff ];
  · exact fun b _ => ⟨ fun i => a₀ i ^^ b i, Finset.mem_univ _, by ext i; simp +decide ⟩;
  · intro a ha; rw [ ← pauliAction_mul ] ;
    rw [ mul_eq_mulRaw, gen_closure ];
    · assumption;
    · exact gen_commutes_gen hcomm a₀ a

theorem stabSum_mem {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ) (v : Vec n) :
    stabSum Γ v ∈ V Γ := by
  intro P hP
  obtain ⟨k, hk⟩ : ∃ k : Fin Γ.length, Γ.get k = P := List.mem_iff_get.mp hP
  simpa only [ ← hk, gen_single ] using stabSum_invariant hcomm ( fun i => decide ( i = k ) ) v

theorem mtrace_stabSum {n : ℕ} {Γ : List (Pauli n)} :
    mtrace (stabSum Γ) = ∑ a : (Fin Γ.length → Bool), ptrace (gen Γ a) := by
  convert mtrace_sum ( Finset.univ : Finset ( Fin Γ.length → Bool ) ) ( fun a => pauliAction ( gen Γ a ) ) using 1

/-! ## Counting subset products -/

/-
`mulRaw Q g = +I` iff `g = Q` (for commuting `Q`, `g`; `Q` is Hermitian).
-/
theorem mulRaw_eq_I_iff {n : ℕ} {Q g : Pauli n} (h : Q.commutes g = true) :
    mulRaw Q g = pauliI n ↔ g = Q := by
  constructor <;> intro h' <;> have :=mulRaw_assoc Q Q g <;> simp_all +decide [ mulRaw_commutes_left, mulRaw_commutes_right ];
  · simp_all +decide [ mulRaw_self, mulRaw_one ];
    rw [ ← this ( Pauli.commutes_self Q ), one_mulRaw ];
  · exact mulRaw_self Q

theorem mulRaw_eq_negI_iff {n : ℕ} {Q g : Pauli n} (h : Q.commutes g = true) :
    mulRaw Q g = pauliMinusI n ↔ g = Q.negate := by
  constructor;
  · -- By definition of mulRaw, we know that mulRaw Q (g.negate) = (mulRaw Q g).negate.
    have h_mul_neg : mulRaw Q (g.negate) = (mulRaw Q g).negate := by
      unfold mulRaw
      simp +decide [ Pauli.negate, mulXs, mulZs, phaseZ ];
      unfold numY numYmul crossZX mulXs mulZs; aesop;
    intro h_eq
    have h_eq_neg : mulRaw Q g.negate = pauliI n := by
      aesop;
    have := mulRaw_eq_I_iff ( show Q.commutes g.negate = true from ?_ );
    · exact this.mp h_eq_neg ▸ by unfold Pauli.negate; aesop;
    · unfold Pauli.commutes at *; aesop;
  · rintro rfl;
    unfold mulRaw pauliMinusI;
    unfold Pauli.negate; simp +decide [ mulXs, mulZs, phaseZ ] ;
    unfold numY numYmul crossZX mulXs mulZs pauliI; simp +decide [ Finset.sum_add_distrib, two_mul ] ;
    grind

theorem pauliI_ne_pauliMinusI {n : ℕ} : pauliI n ≠ pauliMinusI n := by
  intro h
  have : (pauliI n).sign = (pauliMinusI n).sign := by rw [h]
  simp [pauliI, pauliMinusI, Pauli.negate] at this

/-
`Σ_a ptrace (gen a) = 2^n · #{a : gen a = +I}` when `-I ∉ ⟨Γ⟩`.
-/
theorem sum_ptrace_gen {n : ℕ} {Γ : List (Pauli n)}
    (hnegI : ∀ a, gen Γ a ≠ pauliMinusI n) :
    (∑ a : (Fin Γ.length → Bool), ptrace (gen Γ a))
      = (2 ^ n : ℂ) * ((Finset.univ.filter (fun a => gen Γ a = pauliI n)).card : ℂ) := by
  convert Finset.sum_congr rfl fun a _ => ?_ using 1;
  rotate_left;
  exact fun a => if gen Γ a = pauliI n then ( 2 ^ n : ℂ ) else 0;
  · rw [ ptrace_eq ] ; aesop;
  · simp +decide [ Finset.sum_ite, mul_comm ]

/-
`Σ_a ptrace (mulRaw Q (gen a)) = 2^n · (#{a : gen a = Q} − #{a : gen a = -Q})`.
-/
theorem sum_ptrace_Qgen {n : ℕ} {Γ : List (Pauli n)} {Q : Pauli n}
    (hcommQ : ∀ a, Q.commutes (gen Γ a) = true) :
    (∑ a : (Fin Γ.length → Bool), ptrace (mulRaw Q (gen Γ a)))
      = (2 ^ n : ℂ) * ((Finset.univ.filter (fun a => gen Γ a = Q)).card : ℂ)
        - (2 ^ n : ℂ) * ((Finset.univ.filter (fun a => gen Γ a = Q.negate)).card : ℂ) := by
  have h_sum : ∀ a : Fin Γ.length → Bool, ptrace (mulRaw Q (gen Γ a)) = if gen Γ a = Q then (2^n : ℂ) else if gen Γ a = Q.negate then -(2^n : ℂ) else 0 := by
    intro a;
    split_ifs <;> simp_all +decide [ ptrace_eq, mulRaw_eq_I_iff, mulRaw_eq_negI_iff ];
    · exact fun h => False.elim <| h <| mulRaw_self Q;
    · rw [ if_neg, if_pos ];
      · convert mulRaw_eq_negI_iff _ |>.2 rfl using 1;
        grind;
      · rw [ mulRaw_eq_I_iff ] ; aesop;
        grind;
  rw [ Finset.sum_congr rfl fun a _ => h_sum a, Finset.sum_ite, Finset.sum_ite ] ; norm_num ; ring_nf;
  simp +decide [ Finset.filter_filter ];
  congr 1 with a ; simp +contextual [ Pauli.ext_iff ];
  cases Q ; simp +decide [ Pauli.negate ]

/-! ## Existence of a nonzero stabilizer state -/

/-
If `Γ` is commuting and `-I ∉ ⟨Γ⟩`, the code space is nonzero.
-/
theorem exists_nonzero_codeVector {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ)
    (hnegI : ∀ a, gen Γ a ≠ pauliMinusI n) :
    ∃ v ∈ V Γ, v ≠ 0 := by
  have h_mtrace_stabSum : mtrace (stabSum Γ) ≠ 0 := by
    rw [ mtrace_stabSum, sum_ptrace_gen hnegI ];
    exact mul_ne_zero ( pow_ne_zero _ two_ne_zero ) ( Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr ⟨ fun _ => false, by simp +decide [ gen_zero ] ⟩ );
  contrapose! h_mtrace_stabSum;
  exact mtrace_zero ▸ congr_arg _ ( funext fun v => h_mtrace_stabSum _ ( stabSum_mem hcomm v ) )

/-
A valid `Q` commutes with every element of `⟨Γ⟩` (else the code space is
    zero).
-/
theorem valid_commutes_gen {n : ℕ} {Γ : List (Pauli n)} {Q : Pauli n}
    (hvalid : Valid Γ Q) (hcomm : Commuting Γ)
    (hne : ∃ v ∈ V Γ, v ≠ 0) (a : Fin Γ.length → Bool) :
    Q.commutes (gen Γ a) = true := by
  obtain ⟨ v, hv, hv0 ⟩ := hne;
  by_contra h_contra
  have h_anticomm : pauliAction Q (pauliAction (gen Γ a) v) = - pauliAction (gen Γ a) (pauliAction Q v) := by
    apply pauliAction_anticomm Q (gen Γ a) (by
    grind) v
  have h_comm : pauliAction Q v = v ∧ pauliAction (gen Γ a) v = v := by
    exact ⟨ hvalid v hv, gen_fixes hcomm hv a ⟩
  generalize_proofs at *;
  grind

/-! ## The trace identity -/

/-
Taking traces of `Q · stabSum = stabSum`.
-/
theorem stab_trace_eq {n : ℕ} {Γ : List (Pauli n)} {Q : Pauli n}
    (hvalid : Valid Γ Q) (hcomm : Commuting Γ)
    (hcommQ : ∀ a, Q.commutes (gen Γ a) = true) :
    (∑ a : (Fin Γ.length → Bool), ptrace (mulRaw Q (gen Γ a)))
      = ∑ a : (Fin Γ.length → Bool), ptrace (gen Γ a) := by
  have h_eq : ∀ v : Vec n, ∑ a : (Fin Γ.length → Bool), pauliAction (mulRaw Q (gen Γ a)) v = pauliAction Q (∑ a : (Fin Γ.length → Bool), pauliAction (gen Γ a) v) := by
    intro v
    have h_sum : ∑ a : (Fin Γ.length → Bool), pauliAction (mulRaw Q (gen Γ a)) v = ∑ a : (Fin Γ.length → Bool), pauliAction Q (pauliAction (gen Γ a) v) := by
      exact Finset.sum_congr rfl fun a ha => pauliAction_mul Q (gen Γ a) (hcommQ a) v ▸ by aesop;
    rw [ h_sum, pauliAction_sum ];
  -- Apply the equality of operators to the basis vectors.
  have h_eq_basis : ∀ c : Fin n → Bool, (∑ a : (Fin Γ.length → Bool), pauliAction (mulRaw Q (gen Γ a)) (basisVec c)) = (∑ a : (Fin Γ.length → Bool), pauliAction (gen Γ a) (basisVec c)) := by
    intro c
    have h_eq_basis : pauliAction Q (∑ a : (Fin Γ.length → Bool), pauliAction (gen Γ a) (basisVec c)) = ∑ a : (Fin Γ.length → Bool), pauliAction (gen Γ a) (basisVec c) := by
      apply hvalid;
      convert stabSum_mem hcomm ( basisVec c ) using 1;
    rw [ h_eq, h_eq_basis ];
  convert Finset.sum_congr rfl fun c _ => congr_fun ( h_eq_basis c ) c using 1;
  any_goals exact Finset.univ;
  · simp +decide [ ptrace, mtrace ];
    exact Finset.sum_comm;
  · convert mtrace_stabSum.symm using 1

/-
**The trace identity .**  If `Γ ⊢ Q` is valid, `Γ` is
    commuting, and `-I ∉ ⟨Γ⟩`, then `Q` is a signed subset product of `Γ`.
-/
theorem trace_identity {n : ℕ} {Γ : List (Pauli n)} {Q : Pauli n}
    (hvalid : Valid Γ Q) (hcomm : Commuting Γ)
    (hnegI : ∀ a, gen Γ a ≠ pauliMinusI n) :
    ∃ a, gen Γ a = Q := by
  obtain ⟨a, ha⟩ : ∃ a : Fin Γ.length → Bool, gen Γ a = Q ∨ gen Γ a = Q.negate := by
    by_contra h_contra;
    convert PauliLogic.stab_trace_eq hvalid hcomm _ using 1;
    · rw [ PauliLogic.sum_ptrace_Qgen, PauliLogic.sum_ptrace_gen ];
      · simp_all +decide [ Finset.ext_iff ];
        exact ⟨ fun _ => false, PauliLogic.gen_zero Γ ⟩;
      · assumption;
      · obtain ⟨ v, hv, hv' ⟩ := PauliLogic.exists_nonzero_codeVector hcomm hnegI; exact fun a => PauliLogic.valid_commutes_gen hvalid hcomm ⟨ v, hv, hv' ⟩ a;
    · obtain ⟨ v, hv, hv' ⟩ := PauliLogic.exists_nonzero_codeVector hcomm hnegI; exact fun a => PauliLogic.valid_commutes_gen hvalid hcomm ⟨ v, hv, hv' ⟩ a;
  have h_contradiction : ∀ v ∈ V Γ, pauliAction (Q.negate) v = -v := by
    intros v hv
    have h_contradiction : pauliAction (Q.negate) v = -pauliAction Q v := by
      unfold pauliAction; simp +decide [ Pauli.negate ] ;
      ext c; simp +decide [ coeff ] ;
      cases Q.sign <;> simp +decide [ * ]; all_goals exact Or.inl rfl;
    rw [ h_contradiction, hvalid v hv ];
  grind +suggestions

/-! ## Building the derivation -/

/-
Every subset product of `Γ` is derivable (T2/T3 building block).
-/
theorem genOn_derivation_nonempty {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ)
    (L : List (Fin Γ.length)) (a : Fin Γ.length → Bool) :
    Nonempty (Derivation Γ (genOn Γ L a)) := by
  induction' L with i L' ih generalizing a <;> simp_all +decide [ genOn ];
  · exact ⟨ Derivation.unitI ⟩;
  · split_ifs;
    · exact ⟨ Derivation.mul ( get_commutes_genOn hcomm i L' a ) ( Derivation.ax i ) ( ih a |> Classical.choice ) ⟩;
    · exact ih a

theorem gen_derivation_nonempty {n : ℕ} {Γ : List (Pauli n)} (hcomm : Commuting Γ)
    (a : Fin Γ.length → Bool) : Nonempty (Derivation Γ (gen Γ a)) :=
  genOn_derivation_nonempty hcomm _ a

/-! ## The `V(Γ) = 0` case -/

/-- **T2.**  If the code space of `Γ` is trivial (`V Γ = {0}`), then the
    theory is contradictory: `Γ ⊢ ⊥` is derivable.  Either `Γ` contains an
    anticommuting pair (`clash`), or `Γ` is commuting and `-I ∈ ⟨Γ⟩` (`mul`
    then `absurd`); the remaining possibility (`Γ` commuting, `-I ∉ ⟨Γ⟩`) is
    excluded since it would yield a nonzero stabilizer vector. -/
theorem bottom_from_zero_space {n : ℕ} {Γ : List (Pauli n)}
    (hzero : ∀ v ∈ V Γ, v = 0) : Nonempty (BotDerivation Γ) := by
  by_cases hcomm : Commuting Γ
  · by_cases hnegI : ∃ a, gen Γ a = pauliMinusI n
    · -- `-I ∈ ⟨Γ⟩`: derive `Γ ⊢ -I`, then `(absurd)`.
      obtain ⟨a, ha⟩ := hnegI
      obtain ⟨d⟩ := gen_derivation_nonempty hcomm a
      rw [ha] at d
      exact ⟨BotDerivation.absurd d⟩
    · -- Commuting and `-I ∉ ⟨Γ⟩` would give a nonzero stabilizer vector.
      push_neg at hnegI
      obtain ⟨v, hv, hv0⟩ := exists_nonzero_codeVector hcomm hnegI
      exact absurd (hzero v hv) hv0
  · -- Non-commuting: an anticommuting pair gives `⊥` by `(clash)`.
    unfold Commuting at hcomm
    push_neg at hcomm
    obtain ⟨i, j, hij⟩ := hcomm
    have hf : (Γ.get i).commutes (Γ.get j) = false := by
      cases h : (Γ.get i).commutes (Γ.get j) with
      | false => rfl
      | true => exact absurd h hij
    exact ⟨BotDerivation.clash hf (Derivation.ax i) (Derivation.ax j)⟩

/-! ## Completeness -/

/-- **Completeness of PL_n** , `Nonempty` form. -/
theorem completeness_nonempty {n : ℕ} {Γ : List (Pauli n)} {Q : Pauli n}
    (hvalid : Valid Γ Q) : Nonempty (Derivation Γ Q) := by
  by_cases hcomm : Commuting Γ
  · by_cases hnegI : ∃ a, gen Γ a = pauliMinusI n
    · -- `-I ∈ ⟨Γ⟩`: derive `⊥` by `(absurd)`, then `(botElim)`.
      obtain ⟨a, ha⟩ := hnegI
      obtain ⟨d⟩ := gen_derivation_nonempty hcomm a
      rw [ha] at d
      exact ⟨Derivation.botElim Q (BotDerivation.absurd d)⟩
    · -- `-I ∉ ⟨Γ⟩`: the trace identity gives `Q ∈ ⟨Γ⟩`.
      push_neg at hnegI
      obtain ⟨a, ha⟩ := trace_identity hvalid hcomm hnegI
      obtain ⟨d⟩ := gen_derivation_nonempty hcomm a
      rw [ha] at d
      exact ⟨d⟩
  · -- Non-commuting: an anticommuting pair gives `⊥` by `(clash)`.
    unfold Commuting at hcomm
    push_neg at hcomm
    obtain ⟨i, j, hij⟩ := hcomm
    have hf : (Γ.get i).commutes (Γ.get j) = false := by
      cases h : (Γ.get i).commutes (Γ.get j) with
      | false => rfl
      | true => exact absurd h hij
    exact ⟨Derivation.botElim Q (BotDerivation.clash hf (Derivation.ax i) (Derivation.ax j))⟩

/-- **Completeness of PL_n** : every valid sequent has a derivation. -/
noncomputable def completeness {n : ℕ} {Γ : List (Pauli n)} {Q : Pauli n}
    (hvalid : Valid Γ Q) : Derivation Γ Q :=
  (completeness_nonempty hvalid).some

end PauliLogic