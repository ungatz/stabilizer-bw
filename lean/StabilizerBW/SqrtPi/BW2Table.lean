import StabilizerBW.SqrtPi.Lattice

/-!
# The two-qubit Barnes–Wall lattice `BW₂` and the grade table

The level-3 two-qubit Barnes–Wall lattice is built by the squaring (`(u | u+v)`) construction
from the single-qubit lattice `L₃`:
`BW₂ = { (a, a+b) : a ∈ L₃, b ∈ (1+i)·L₃ } ⊆ (Fin 4 → ℤ[ζ₈])`.

For a vector `x = (x₀,x₁,x₂,x₃)`, membership unfolds to three divisibility conditions
* `(1+i) ∣ x₀ + x₁`,
* `(1+i) ∣ x₂ - x₀`,
* `(1+i)² ∣ (x₂ - x₀) + (x₃ - x₁)`.

We compute the lattice grade of the diagonal table entries and reproduce the user-side
`grade2_*` values `CZ ↦ 0`, `T⊗I ↦ 1`, `I⊗T ↦ 1`, `T⊗T ↦ 2`, `CS ↦ 2`, `cT ↦ 3`.
-/

set_option maxRecDepth 4000

namespace Pi3
open Z8

/-- `2 ∣ y` iff every coordinate of `y` is even. -/
def div2 (y : Z8) : Prop := y.a % 2 = 0 ∧ y.b % 2 = 0 ∧ y.c % 2 = 0 ∧ y.d % 2 = 0

instance (y : Z8) : Decidable (div2 y) := by unfold div2; infer_instance

/-- `(1+i)² ∣ y ↔ 2 ∣ y ↔ all coordinates even`. -/
lemma dvd_onePlusISq_iff (y : Z8) : onePlusI ^ 2 ∣ y ↔ div2 y := by
  have hsq : onePlusI ^ 2 = (⟨0, 0, 2, 0⟩ : Z8) := by decide
  rw [hsq]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Z8.mul_a, Z8.mul_b, Z8.mul_c, Z8.mul_d] <;> omega
  · intro h
    unfold div2 at h
    refine ⟨⟨y.c / 2, y.d / 2, -(y.a / 2), -(y.b / 2)⟩, ?_⟩
    ext <;> simp only [Z8.mul_a, Z8.mul_b, Z8.mul_c, Z8.mul_d] <;> omega

/-- Membership in the two-qubit Barnes–Wall lattice `BW₂` (dimension 4). -/
def inBW4 (x : Fin 4 → Z8) : Prop :=
  onePlusI ∣ (x 0 + x 1) ∧ onePlusI ∣ (x 2 - x 0) ∧
    onePlusI ^ 2 ∣ ((x 2 - x 0) + (x 3 - x 1))

/-- The two-qubit Barnes–Wall lattice `BW₂` as a `ℤ[ζ₈]`-submodule of `Fin 4 → ℤ[ζ₈]`. -/
def BW4 : Submodule Z8 (Fin 4 → Z8) where
  carrier := {x | inBW4 x}
  add_mem' := by
    intro u v hu hv
    obtain ⟨h1, h2, h3⟩ := hu
    obtain ⟨k1, k2, k3⟩ := hv
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Pi.add_apply] at *
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
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Pi.smul_apply, smul_eq_mul] at *
    · have e : c * x 0 + c * x 1 = c * (x 0 + x 1) := by ring
      rw [e]; exact h1.mul_left c
    · have e : c * x 2 - c * x 0 = c * (x 2 - x 0) := by ring
      rw [e]; exact h2.mul_left c
    · have e : c * x 2 - c * x 0 + (c * x 3 - c * x 1) = c * ((x 2 - x 0) + (x 3 - x 1)) := by ring
      rw [e]; exact h3.mul_left c

lemma mem_BW4 (x : Fin 4 → Z8) : x ∈ BW4 ↔ inBW4 x := Iff.rfl

/-- Decidable characterisation of `BW₂` membership in terms of coordinate parities. -/
def inBW4D (x : Fin 4 → Z8) : Prop :=
  divLam2 (x 0 + x 1) ∧ divLam2 (x 2 - x 0) ∧ div2 ((x 2 - x 0) + (x 3 - x 1))

instance (x : Fin 4 → Z8) : Decidable (inBW4D x) := by unfold inBW4D; infer_instance

lemma mem_BW4_iff (x : Fin 4 → Z8) : x ∈ BW4 ↔ inBW4D x := by
  rw [mem_BW4, inBW4, inBW4D, dvd_onePlusI_iff, dvd_onePlusI_iff, dvd_onePlusISq_iff]

/-- The grade of a diagonal two-qubit gate `diag d` with respect to `BW₂`. -/
noncomputable def gradeBW4 (d : Fin 4 → Z8) : ℕ :=
  sInf { k : ℕ | ∀ v ∈ BW4, (fun i => lam ^ k * (d i * v i)) ∈ BW4 }

/-- Helper: pin down `gradeBW4` from an upper-bound witness and a minimality witness. -/
lemma gradeBW4_eq (d : Fin 4 → Z8) (val : ℕ)
    (hup : ∀ w ∈ BW4, (fun i => lam ^ val * (d i * w i)) ∈ BW4)
    (hlow : ∀ k, k < val → ¬ (∀ w ∈ BW4, (fun i => lam ^ k * (d i * w i)) ∈ BW4)) :
    gradeBW4 d = val := by
  unfold gradeBW4
  refine le_antisymm (Nat.sInf_le hup) (le_csInf ⟨val, hup⟩ ?_)
  intro k hk
  by_contra hlt
  exact hlow k (by omega) hk

/-- `CZ = diag(1,1,1,-1)`. -/
def dCZ : Fin 4 → Z8 := ![1, 1, 1, -1]
/-- `T ⊗ I = diag(1,1,ζ,ζ)`. -/
def dTI : Fin 4 → Z8 := ![1, 1, zeta, zeta]
/-- `I ⊗ T = diag(1,ζ,1,ζ)`. -/
def dIT : Fin 4 → Z8 := ![1, zeta, 1, zeta]
/-- `T ⊗ T = diag(1,ζ,ζ,i)`. -/
def dTT : Fin 4 → Z8 := ![1, zeta, zeta, imag]
/-- `CS = diag(1,1,1,i)`. -/
def dCS : Fin 4 → Z8 := ![1, 1, 1, imag]
/-- controlled-`T` `= diag(1,1,1,ζ)`. -/
def dcT : Fin 4 → Z8 := ![1, 1, 1, zeta]

/-- The four `ℤ[ζ₈]`-module generators of `BW₂`. -/
def bw4gen1 : Fin 4 → Z8 := ![1, -1, 1, -1]
def bw4gen2 : Fin 4 → Z8 := ![0, onePlusI, 0, onePlusI]
def bw4gen3 : Fin 4 → Z8 := ![0, 0, onePlusI, -onePlusI]
def bw4gen4 : Fin 4 → Z8 := ![0, 0, 0, onePlusI ^ 2]

/-- The generating set of `BW₂`. -/
def bw4gens : Set (Fin 4 → Z8) := {bw4gen1, bw4gen2, bw4gen3, bw4gen4}

lemma bw4gen1_mem : bw4gen1 ∈ BW4 := by rw [mem_BW4_iff]; decide
lemma bw4gen2_mem : bw4gen2 ∈ BW4 := by rw [mem_BW4_iff]; decide
lemma bw4gen3_mem : bw4gen3 ∈ BW4 := by rw [mem_BW4_iff]; decide
lemma bw4gen4_mem : bw4gen4 ∈ BW4 := by rw [mem_BW4_iff]; decide

/-
Every `BW₂` vector is a `ℤ[ζ₈]`-combination of the four generators.
-/
lemma BW4_subset_span : (BW4 : Set (Fin 4 → Z8)) ⊆ Submodule.span Z8 bw4gens := by
  -- Take any $x \in BW4$ and show it is in the span of the generators.
  intro x hx
  obtain ⟨α, β, γ, δ, hx_eq⟩ : ∃ α β γ δ : Z8, x = α • bw4gen1 + β • bw4gen2 + γ • bw4gen3 + δ • bw4gen4 := by
    have h_decomp : ∃ α β γ δ : Z8, x 0 = α ∧ x 1 = -α + β * onePlusI ∧ x 2 = α + γ * onePlusI ∧ x 3 = -α + β * onePlusI - γ * onePlusI + δ * onePlusI ^ 2 := by
      simp +zetaDelta at *;
      have h_div : onePlusI ∣ (x 0 + x 1) ∧ onePlusI ∣ (x 2 - x 0) ∧ onePlusI ^ 2 ∣ ((x 2 - x 0) + (x 3 - x 1)) := by
        exact mem_BW4 x |>.1 hx;
      obtain ⟨ β, hβ ⟩ := h_div.1
      obtain ⟨ γ, hγ ⟩ := h_div.2.1
      obtain ⟨ δ, hδ ⟩ := h_div.2.2
      use β, by
        grind, γ, by
        grind +splitImp, δ, by
        grind +ring;
    obtain ⟨ α, β, γ, δ, h₀, h₁, h₂, h₃ ⟩ := h_decomp; use α, β, γ, δ; ext i; fin_cases i <;> simp +decide [ *, bw4gen1, bw4gen2, bw4gen3, bw4gen4 ] ; ring;
    · fin_cases i <;> simp +decide [ *, bw4gen1, bw4gen2, bw4gen3, bw4gen4 ] ; ring!;
    · fin_cases i <;> simp +decide [ *, bw4gen1, bw4gen2, bw4gen3, bw4gen4 ] ; ring!;
    · fin_cases i <;> simp +decide [ *, bw4gen1, bw4gen2, bw4gen3, bw4gen4 ];
      ring;
  exact hx_eq.symm ▸ Submodule.add_mem _ ( Submodule.add_mem _ ( Submodule.add_mem _ ( Submodule.smul_mem _ _ ( Submodule.subset_span ( by simp +decide [ bw4gens ] ) ) ) ( Submodule.smul_mem _ _ ( Submodule.subset_span ( by simp +decide [ bw4gens ] ) ) ) ) ( Submodule.smul_mem _ _ ( Submodule.subset_span ( by simp +decide [ bw4gens ] ) ) ) ) ( Submodule.smul_mem _ _ ( Submodule.subset_span ( by simp +decide [ bw4gens ] ) ) )

/-- Decidable generator-pushforward predicate: `λ^k·diag(d)` maps every generator into `BW₂`. -/
def mapsGen (d : Fin 4 → Z8) (k : ℕ) : Prop :=
  inBW4D (fun i => lam ^ k * (d i * bw4gen1 i)) ∧ inBW4D (fun i => lam ^ k * (d i * bw4gen2 i)) ∧
    inBW4D (fun i => lam ^ k * (d i * bw4gen3 i)) ∧ inBW4D (fun i => lam ^ k * (d i * bw4gen4 i))

instance (d : Fin 4 → Z8) (k : ℕ) : Decidable (mapsGen d k) := by unfold mapsGen; infer_instance

/-
If `λ^k·diag(d)` maps each generator into `BW₂`, it maps all of `BW₂` into `BW₂`.
-/
lemma mapsBW4_of_mapsGen (d : Fin 4 → Z8) (k : ℕ) (h : mapsGen d k) :
    ∀ w ∈ BW4, (fun i => lam ^ k * (d i * w i)) ∈ BW4 := by
  intro w hw
  have h_span : w ∈ Submodule.span Z8 bw4gens := by
    convert BW4_subset_span hw;
  refine' Submodule.span_induction _ _ _ _ h_span;
  · unfold bw4gens; simp +decide ;
    exact ⟨ by simpa only [ mem_BW4_iff ] using h.1, by simpa only [ mem_BW4_iff ] using h.2.1, by simpa only [ mem_BW4_iff ] using h.2.2.1, by simpa only [ mem_BW4_iff ] using h.2.2.2 ⟩;
  · simp +decide [ mem_BW4_iff ];
  · intro x y hx hy hx' hy'; convert BW4.add_mem hx' hy' using 1; ext i; simp +decide [ mul_add ] ; ring;
    · simp +decide [ mul_add ];
    · simp +decide [ mul_add, mul_left_comm ];
    · simp +decide [ mul_add ];
  · intro a x hx hx'; convert Submodule.smul_mem _ a hx' using 1; ext i; simp +decide [ mul_left_comm ] ;
    · simp +decide [ mul_assoc, mul_left_comm, mul_comm ];
    · simp +decide [ mul_assoc, mul_left_comm, mul_comm ];
    · simp +decide [ mul_assoc, mul_left_comm, mul_comm ]

/-- `grade(CZ) = 0`. -/
theorem grade2_CZ : gradeBW4 dCZ = 0 := by
  apply gradeBW4_eq
  · exact mapsBW4_of_mapsGen dCZ 0 (by decide)
  · intro k hk; omega
/-- `grade(T⊗I) = 1`. -/
theorem grade2_TI : gradeBW4 dTI = 1 := by
  apply gradeBW4_eq
  · exact mapsBW4_of_mapsGen dTI 1 (by decide)
  · intro k hk hall
    interval_cases k
    · exact absurd (hall bw4gen2 bw4gen2_mem) (by rw [mem_BW4_iff]; decide)
/-- `grade(I⊗T) = 1`. -/
theorem grade2_IT : gradeBW4 dIT = 1 := by
  apply gradeBW4_eq
  · exact mapsBW4_of_mapsGen dIT 1 (by decide)
  · intro k hk hall
    interval_cases k
    · exact absurd (hall bw4gen1 bw4gen1_mem) (by rw [mem_BW4_iff]; decide)
/-- `grade(T⊗T) = 2`. -/
theorem grade2_TT : gradeBW4 dTT = 2 := by
  apply gradeBW4_eq
  · exact mapsBW4_of_mapsGen dTT 2 (by decide)
  · intro k hk hall
    interval_cases k
    · exact absurd (hall bw4gen1 bw4gen1_mem) (by rw [mem_BW4_iff]; decide)
    · exact absurd (hall bw4gen1 bw4gen1_mem) (by rw [mem_BW4_iff]; decide)
/-- `grade(CS) = 2`. -/
theorem grade2_CS : gradeBW4 dCS = 2 := by
  apply gradeBW4_eq
  · exact mapsBW4_of_mapsGen dCS 2 (by decide)
  · intro k hk hall
    interval_cases k
    · exact absurd (hall bw4gen1 bw4gen1_mem) (by rw [mem_BW4_iff]; decide)
    · exact absurd (hall bw4gen1 bw4gen1_mem) (by rw [mem_BW4_iff]; decide)
/-- `grade(controlled-T) = 3`. -/
theorem grade2_cT : gradeBW4 dcT = 3 := by
  apply gradeBW4_eq
  · exact mapsBW4_of_mapsGen dcT 3 (by decide)
  · intro k hk hall
    interval_cases k
    · exact absurd (hall bw4gen1 bw4gen1_mem) (by rw [mem_BW4_iff]; decide)
    · exact absurd (hall bw4gen1 bw4gen1_mem) (by rw [mem_BW4_iff]; decide)
    · exact absurd (hall bw4gen1 bw4gen1_mem) (by rw [mem_BW4_iff]; decide)

/-- **T5 (Headline).** The grade-`1` stratum at `n = 2`: the `BW₂` diagonal table.
The `Π₃` syntax has terms whose lattice grade matches the two-qubit Barnes–Wall lattice's
most refined diagonal grades exactly:
`g(CZ)=0`, `g(T⊗I)=1`, `g(I⊗T)=1`, `g(T⊗T)=2`, `g(CS)=2`, `g(controlled-T)=3`. -/
theorem Headline_T5 :
    gradeBW4 dCZ = 0 ∧ gradeBW4 dTI = 1 ∧ gradeBW4 dIT = 1 ∧
      gradeBW4 dTT = 2 ∧ gradeBW4 dCS = 2 ∧ gradeBW4 dcT = 3 :=
  ⟨grade2_CZ, grade2_TI, grade2_IT, grade2_TT, grade2_CS, grade2_cT⟩

end Pi3