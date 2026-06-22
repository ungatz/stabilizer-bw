import StabilizerBW.SqrtPi.Level2.Grade2

/-!
# The level-2 Barnes–Wall lattices and the generator reduction for `gradeWrt₂`

This file builds the level-2 (Gaussian-integer) Barnes–Wall lattices, the exact analogues of
`Pi3.L3` (single qubit) and `Pi3.BW4` (two qubits) but over `ℤ[i]` instead of `ℤ[ζ₈]`:

* `L2`  — the single-qubit lattice `{(a,b) ∈ ℤ[i]² : (1+i) ∣ a + b}`;
* `BW2L` — the two-qubit lattice via the squaring construction, with the four explicit
  `ℤ[i]`-module generators and the spanning lemma `BW2L_subset_span`.

The key deliverable is `pushesIn2_of_gens`: to verify that `λ₂^k · M` pushes the whole lattice
`BW2L` into itself it suffices to check the four generators — turning every level-2 grade
computation into a finite `decide`.
-/

set_option maxRecDepth 4000
set_option maxHeartbeats 400000

namespace Pi3
open Zi

/-! ### Divisibility by `1 + i` over `ℤ[i]` -/

/-- `(1+i) = i · λ₂`, so `(1+i)` is an associate of `λ₂`. -/
lemma zi_onePlusI_eq : (onePlusI : Zi) = imag * lam2 := by decide

/-- `(1+i) ∣ y ↔ a + b even`. -/
lemma zi_dvd_onePlusI_iff (y : Zi) : onePlusI ∣ y ↔ ziDivLam y := by
  rw [← dvd_lam2_iff]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨imag * t, by rw [zi_onePlusI_eq]; ring⟩
  · rintro ⟨t, rfl⟩
    refine ⟨(⟨0, 0⟩ - imag) * t, ?_⟩
    have : (onePlusI : Zi) * ((⟨0, 0⟩ - imag) * t) = lam2 * t := by
      have h : (onePlusI : Zi) * (⟨0, 0⟩ - imag) = lam2 := by decide
      rw [← mul_assoc, h]
    rw [this]

/-- `(1+i)² = 2i`, so `(1+i)² ∣ y ↔ 2 ∣ y ↔ both coordinates even`. -/
lemma zi_dvd_onePlusISq_iff (y : Zi) : onePlusI ^ 2 ∣ y ↔ ziDiv2 y := by
  have hsq : (onePlusI : Zi) ^ 2 = (⟨0, 2⟩ : Zi) := by decide
  rw [hsq]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨?_, ?_⟩ <;> simp only [mul_a, mul_b] <;> omega
  · intro h
    unfold ziDiv2 at h
    refine ⟨⟨y.b / 2, -(y.a / 2)⟩, ?_⟩
    ext <;> simp only [mul_a, mul_b] <;> omega

/-! ### The single-qubit level-2 lattice `L₂` -/

/-- Membership in the single-qubit level-2 lattice `L₂`: `(1+i) ∣ v 0 + v 1`. -/
def inL2 (v : Fin 2 → Zi) : Prop := onePlusI ∣ (v 0 + v 1)

/-- The level-2 single-qubit Barnes–Wall lattice `L₂ = {(a,b) ∈ ℤ[i]² : (1+i) ∣ a+b}`. -/
def L2 : Submodule Zi (Fin 2 → Zi) where
  carrier := {v | inL2 v}
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, inL2, Pi.add_apply] at *
    have : u 0 + v 0 + (u 1 + v 1) = (u 0 + u 1) + (v 0 + v 1) := by ring
    rw [this]; exact dvd_add hu hv
  zero_mem' := by simp [inL2]
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq, inL2, Pi.smul_apply, smul_eq_mul] at *
    have : c * v 0 + c * v 1 = c * (v 0 + v 1) := by ring
    rw [this]; exact Dvd.dvd.mul_left hv c

@[simp] lemma mem_L2 (v : Fin 2 → Zi) : v ∈ L2 ↔ onePlusI ∣ (v 0 + v 1) := Iff.rfl

/-! ### The two-qubit level-2 lattice `BW2L` (squaring construction) -/

/-- Membership in the two-qubit level-2 Barnes–Wall lattice `BW2L` (dimension 4). -/
def inBW2L (x : Fin 4 → Zi) : Prop :=
  onePlusI ∣ (x 0 + x 1) ∧ onePlusI ∣ (x 2 - x 0) ∧
    onePlusI ^ 2 ∣ ((x 2 - x 0) + (x 3 - x 1))

/-- The two-qubit level-2 Barnes–Wall lattice `BW2L` as a `ℤ[i]`-submodule of `Fin 4 → ℤ[i]`. -/
def BW2L : Submodule Zi (Fin 4 → Zi) where
  carrier := {x | inBW2L x}
  add_mem' := by
    intro u v hu hv
    obtain ⟨h1, h2, h3⟩ := hu
    obtain ⟨k1, k2, k3⟩ := hv
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Pi.add_apply] at *
    · have e : u 0 + v 0 + (u 1 + v 1) = (u 0 + u 1) + (v 0 + v 1) := by ring
      rw [e]; exact dvd_add h1 k1
    · have e : u 2 + v 2 - (u 0 + v 0) = (u 2 - u 0) + (v 2 - v 0) := by ring
      rw [e]; exact dvd_add h2 k2
    · have e : u 2 + v 2 - (u 0 + v 0) + (u 3 + v 3 - (u 1 + v 1))
          = ((u 2 - u 0) + (u 3 - u 1)) + ((v 2 - v 0) + (v 3 - v 1)) := by ring
      rw [e]; exact dvd_add h3 k3
  zero_mem' := by refine ⟨?_, ?_, ?_⟩ <;> simp
  smul_mem' := by
    intro c x hx
    obtain ⟨h1, h2, h3⟩ := hx
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Pi.smul_apply, smul_eq_mul] at *
    · have e : c * x 0 + c * x 1 = c * (x 0 + x 1) := by ring
      rw [e]; exact h1.mul_left c
    · have e : c * x 2 - c * x 0 = c * (x 2 - x 0) := by ring
      rw [e]; exact h2.mul_left c
    · have e : c * x 2 - c * x 0 + (c * x 3 - c * x 1) = c * ((x 2 - x 0) + (x 3 - x 1)) := by ring
      rw [e]; exact h3.mul_left c

lemma mem_BW2L (x : Fin 4 → Zi) : x ∈ BW2L ↔ inBW2L x := Iff.rfl

/-- Decidable characterisation of `BW2L` membership in terms of coordinate parities. -/
def inBW2LD (x : Fin 4 → Zi) : Prop :=
  ziDivLam (x 0 + x 1) ∧ ziDivLam (x 2 - x 0) ∧ ziDiv2 ((x 2 - x 0) + (x 3 - x 1))

instance (x : Fin 4 → Zi) : Decidable (inBW2LD x) := by unfold inBW2LD; infer_instance

lemma mem_BW2L_iff (x : Fin 4 → Zi) : x ∈ BW2L ↔ inBW2LD x := by
  rw [mem_BW2L, inBW2L, inBW2LD, zi_dvd_onePlusI_iff, zi_dvd_onePlusI_iff, zi_dvd_onePlusISq_iff]

/-- The four `ℤ[i]`-module generators of `BW2L`. -/
def bw2gen1 : Fin 4 → Zi := ![1, -1, 1, -1]
def bw2gen2 : Fin 4 → Zi := ![0, onePlusI, 0, onePlusI]
def bw2gen3 : Fin 4 → Zi := ![0, 0, onePlusI, -onePlusI]
def bw2gen4 : Fin 4 → Zi := ![0, 0, 0, onePlusI ^ 2]

/-- The generating set of `BW2L`. -/
def bw2gens : Set (Fin 4 → Zi) := {bw2gen1, bw2gen2, bw2gen3, bw2gen4}

lemma bw2gen1_mem : bw2gen1 ∈ BW2L := by rw [mem_BW2L_iff]; decide
lemma bw2gen2_mem : bw2gen2 ∈ BW2L := by rw [mem_BW2L_iff]; decide
lemma bw2gen3_mem : bw2gen3 ∈ BW2L := by rw [mem_BW2L_iff]; decide
lemma bw2gen4_mem : bw2gen4 ∈ BW2L := by rw [mem_BW2L_iff]; decide

/-
Every `BW2L` vector is a `ℤ[i]`-combination of the four generators.
-/
lemma BW2L_subset_span : (BW2L : Set (Fin 4 → Zi)) ⊆ Submodule.span Zi bw2gens := by
  intro x hx
  obtain ⟨α, β, γ, δ, hx_eq⟩ :
      ∃ α β γ δ : Zi, x = α • bw2gen1 + β • bw2gen2 + γ • bw2gen3 + δ • bw2gen4 := by
    simp_all +decide [ funext_iff, Fin.forall_fin_succ ];
    obtain ⟨β, hβ⟩ : ∃ β : Zi, x 0 + x 1 = onePlusI * β := by
      exact mem_BW2L x |>.1 hx |>.1
    obtain ⟨γ, hγ⟩ : ∃ γ : Zi, x 2 - x 0 = onePlusI * γ := by
      exact mem_BW2L x |>.1 hx |>.2.1
    obtain ⟨δ, hδ⟩ : ∃ δ : Zi, (x 2 - x 0) + (x 3 - x 1) = onePlusI ^ 2 * δ := by
      exact mem_BW2L x |>.1 hx |>.2.2;
    refine' ⟨ x 0, β, γ, δ, _, _, _, _ ⟩ <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · simp +decide [ bw2gen1, bw2gen2, bw2gen3, bw2gen4 ];
    · convert congr_arg ( · - x 0 ) hβ using 1 ; ring!;
      erw [ show bw2gen1 1 = -1 from rfl, show bw2gen2 1 = onePlusI from rfl, show bw2gen3 1 = 0 from rfl, show bw2gen4 1 = 0 from rfl ] ; ring!;
    · simp +decide [ bw2gen1, bw2gen2, bw2gen3, bw2gen4 ] ; ring;
    · simp_all +decide [ mul_assoc, pow_two ];
      simp_all +decide [ bw2gen1, bw2gen2, bw2gen3, bw2gen4 ];
      grind
  rw [hx_eq]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))

/-! ### The generator reduction for `pushesIn2` -/

/-- The submodule of `ℤ[i]`-vectors that `λ₂^k · M` pushes into `BW2L`. -/
def pushSub (M : Matrix (Fin 4) (Fin 4) Q8) (k : ℕ) : Submodule Zi (Fin 4 → Zi) where
  carrier := {v | ∃ w ∈ BW2L, lam2Q ^ k • M.mulVec (coeViVec v) = coeViVec w}
  zero_mem' := by
    refine ⟨0, BW2L.zero_mem, ?_⟩
    rw [coeViVec_zero, Matrix.mulVec_zero, smul_zero]
  add_mem' := by
    rintro u v ⟨wu, hwu, hu⟩ ⟨wv, hwv, hv⟩
    refine ⟨wu + wv, BW2L.add_mem hwu hwv, ?_⟩
    rw [coeViVec_add u v, coeViVec_add wu wv, ← hu, ← hv, Matrix.mulVec_add, smul_add]
  smul_mem' := by
    rintro c v ⟨w, hw, hv⟩
    refine ⟨c • w, BW2L.smul_mem c hw, ?_⟩
    rw [coeViVec_smul c v, coeViVec_smul c w, ← hv, Matrix.mulVec_smul, smul_comm]

/-- **Generator reduction.** To check `λ₂^k · M` pushes `BW2L` into itself it suffices to
check the four generators. -/
lemma pushesIn2_of_gens (M : Matrix (Fin 4) (Fin 4) Q8) (k : ℕ)
    (h1 : bw2gen1 ∈ pushSub M k) (h2 : bw2gen2 ∈ pushSub M k)
    (h3 : bw2gen3 ∈ pushSub M k) (h4 : bw2gen4 ∈ pushSub M k) :
    pushesIn2 BW2L M k := by
  have hspan : Submodule.span Zi bw2gens ≤ pushSub M k := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with h | h | h | h <;> subst h <;> assumption
  intro v hv
  exact hspan (BW2L_subset_span hv)

/-! ### Integral matrices: a fully decidable grade computation -/

/-- `coeViVec` is injective (since `Zi.toQ8` is). -/
lemma coeViVec_injective {n : ℕ} {u v : Fin n → Zi} (h : coeViVec u = coeViVec v) : u = v := by
  funext i
  have := congrFun h i
  simp only [coeViVec] at this
  exact Zi.toZ8_injective (Q8.ofZ8_injective this)

/-- Coercion commutes with `mulVec` for an integral (mapped) matrix. -/
lemma coeViVec_mulVec_map (N : Matrix (Fin 4) (Fin 4) Zi) (v : Fin 4 → Zi) :
    (N.map Zi.toQ8).mulVec (coeViVec v) = coeViVec (N.mulVec v) := by
  funext i
  simp only [Matrix.mulVec, Matrix.map_apply, coeViVec, dotProduct]
  rw [← Zi.toQ8Hom_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [← Zi.toQ8Hom_apply, ← Zi.toQ8Hom_apply, map_mul]

/-- `λ₂^k` scaling commutes with the integral coercion. -/
lemma lam2Q_pow_smul (k : ℕ) (u : Fin 4 → Zi) :
    lam2Q ^ k • coeViVec u = coeViVec (Zi.lam2 ^ k • u) := by
  have h : lam2Q ^ k = Zi.toQ8 (Zi.lam2 ^ k) := by
    rw [lam2Q, ← Zi.toQ8Hom_apply, ← map_pow]; rfl
  rw [h]; exact (coeViVec_smul _ u).symm

/-- **Integral upper bound.** For an integral matrix `N`, if `λ₂^k · N` maps each of the four
generators into `BW2L`, then `λ₂^k · (N over ℚ[ζ₈])` pushes all of `BW2L` into itself. -/
lemma pushesIn2_integral_of_mapsGen (N : Matrix (Fin 4) (Fin 4) Zi) (k : ℕ)
    (h1 : Zi.lam2 ^ k • N.mulVec bw2gen1 ∈ BW2L)
    (h2 : Zi.lam2 ^ k • N.mulVec bw2gen2 ∈ BW2L)
    (h3 : Zi.lam2 ^ k • N.mulVec bw2gen3 ∈ BW2L)
    (h4 : Zi.lam2 ^ k • N.mulVec bw2gen4 ∈ BW2L) :
    pushesIn2 BW2L (N.map Zi.toQ8) k := by
  apply pushesIn2_of_gens
  · exact ⟨_, h1, by rw [coeViVec_mulVec_map, lam2Q_pow_smul]⟩
  · exact ⟨_, h2, by rw [coeViVec_mulVec_map, lam2Q_pow_smul]⟩
  · exact ⟨_, h3, by rw [coeViVec_mulVec_map, lam2Q_pow_smul]⟩
  · exact ⟨_, h4, by rw [coeViVec_mulVec_map, lam2Q_pow_smul]⟩

/-- **Integral lower bound (witness `bw2gen1`).** If `λ₂^k · N` sends `bw2gen1` outside `BW2L`,
then `λ₂^k · (N over ℚ[ζ₈])` does not push `BW2L` into itself. -/
lemma not_pushesIn2_integral_gen1 (N : Matrix (Fin 4) (Fin 4) Zi) (k : ℕ)
    (h : Zi.lam2 ^ k • N.mulVec bw2gen1 ∉ BW2L) :
    ¬ pushesIn2 BW2L (N.map Zi.toQ8) k := by
  intro hp
  obtain ⟨w, hw, hwEq⟩ := hp bw2gen1 bw2gen1_mem
  rw [coeViVec_mulVec_map, lam2Q_pow_smul] at hwEq
  exact h (coeViVec_injective hwEq ▸ hw)

end Pi3