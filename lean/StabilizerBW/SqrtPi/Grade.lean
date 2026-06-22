import StabilizerBW.SqrtPi.Q8
import StabilizerBW.SqrtPi.Lattice

/-!
# The lattice grade of a (possibly fractional) operator

For an operator `M : Matrix (Fin n) (Fin n) ℚ[ζ₈]` and a `ℤ[ζ₈]`-lattice
`L ⊆ (Fin n → ℤ[ζ₈])`, the **grade** is `min { k : λ^k · M · L ⊆ L }`, i.e. the least
number of factors of the prime `λ = 1 - ζ₈` needed to push `M` back into the lattice.

We define it as an `ℕ∞`-valued infimum (`⊤` when no `k` works), and prove the two
structural facts the syntax needs:

* `gradeWrt_id`  : the identity has grade `0`;
* `gradeWrt_mul` : grade is subadditive, `g(M·N) ≤ g(M) + g(N)`.
-/

set_option maxRecDepth 4000

namespace Pi3
open Z8

/-- The coercion of an integral vector into `ℚ[ζ₈]ⁿ`. -/
def coeVec {n : ℕ} (v : Fin n → Z8) : Fin n → Q8 := fun i => Q8.ofZ8 (v i)

@[simp] lemma coeVec_apply {n : ℕ} (v : Fin n → Z8) (i : Fin n) :
    coeVec v i = Q8.ofZ8 (v i) := rfl

/-- `M` pushes `L` into `L` after scaling by `λ^k`: for every lattice point `v`,
`λ^k · M · v` is again (the coercion of) a lattice point. -/
def pushesIn {n : ℕ} (L : Submodule Z8 (Fin n → Z8))
    (M : Matrix (Fin n) (Fin n) Q8) (k : ℕ) : Prop :=
  ∀ v ∈ L, ∃ w ∈ L, (Q8.ofZ8 lam) ^ k • M.mulVec (coeVec v) = coeVec w

/-- The lattice grade of `M` with respect to the lattice `L`, in `ℕ∞`
(`⊤` if no scaling pushes `M` into `L`). -/
noncomputable def gradeWrt {n : ℕ} (L : Submodule Z8 (Fin n → Z8))
    (M : Matrix (Fin n) (Fin n) Q8) : ℕ∞ :=
  sInf ((Nat.cast : ℕ → ℕ∞) '' {k | pushesIn L M k})

lemma gradeWrt_le_of_pushesIn {n : ℕ} {L : Submodule Z8 (Fin n → Z8)}
    {M : Matrix (Fin n) (Fin n) Q8} {k : ℕ} (h : pushesIn L M k) :
    gradeWrt L M ≤ (k : ℕ∞) :=
  sInf_le ⟨k, h, rfl⟩

/-- Pin down `gradeWrt` from an upper-bound witness and a minimality witness. -/
lemma gradeWrt_eq {n : ℕ} (L : Submodule Z8 (Fin n → Z8))
    (M : Matrix (Fin n) (Fin n) Q8) (val : ℕ)
    (hup : pushesIn L M val)
    (hlow : ∀ k, k < val → ¬ pushesIn L M k) :
    gradeWrt L M = (val : ℕ∞) := by
  apply le_antisymm (gradeWrt_le_of_pushesIn hup)
  rw [gradeWrt]
  apply le_csInf ⟨(val : ℕ∞), Set.mem_image_of_mem _ hup⟩
  rintro x ⟨k, hk, rfl⟩
  by_contra hlt
  push_neg at hlt
  have : k < val := by exact_mod_cast hlt
  exact hlow k this hk

/-- The identity operator has grade `0`. -/
lemma gradeWrt_id {n : ℕ} (L : Submodule Z8 (Fin n → Z8)) :
    gradeWrt L (1 : Matrix (Fin n) (Fin n) Q8) = 0 := by
  have h0 : pushesIn L (1 : Matrix (Fin n) (Fin n) Q8) 0 := by
    intro v hv
    exact ⟨v, hv, by simp⟩
  have : gradeWrt L (1 : Matrix (Fin n) (Fin n) Q8) ≤ 0 := by
    simpa using gradeWrt_le_of_pushesIn h0
  exact le_antisymm this (by positivity)

/-- Composition of pushforwards: `M·N` is pushed in after `kM + kN` factors. -/
lemma pushesIn_mul {n : ℕ} {L : Submodule Z8 (Fin n → Z8)}
    {M N : Matrix (Fin n) (Fin n) Q8} {kM kN : ℕ}
    (hM : pushesIn L M kM) (hN : pushesIn L N kN) :
    pushesIn L (M * N) (kM + kN) := by
  intro v hv
  obtain ⟨w, hw, hwEq⟩ := hN v hv
  obtain ⟨w', hw', hw'Eq⟩ := hM w hw
  refine ⟨w', hw', ?_⟩
  have hmul : (M * N).mulVec (coeVec v) = M.mulVec (N.mulVec (coeVec v)) := by
    rw [Matrix.mulVec_mulVec]
  rw [hmul, pow_add, mul_smul]
  have : (Q8.ofZ8 lam) ^ kN • M.mulVec (N.mulVec (coeVec v))
       = M.mulVec ((Q8.ofZ8 lam) ^ kN • N.mulVec (coeVec v)) := by
    rw [Matrix.mulVec_smul]
  rw [this, hwEq, hw'Eq]

/-
The grade is subadditive under composition.
-/
lemma gradeWrt_mul {n : ℕ} (L : Submodule Z8 (Fin n → Z8))
    (M N : Matrix (Fin n) (Fin n) Q8) :
    gradeWrt L (M * N) ≤ gradeWrt L M + gradeWrt L N := by
  by_contra h;
  obtain ⟨kM, hkM⟩ : ∃ kM, pushesIn L M kM ∧ gradeWrt L M = kM := by
    unfold gradeWrt at *;
    by_cases hM : ∃ k, pushesIn L M k;
    · have := Nat.sInf_mem ( show { k : ℕ | pushesIn L M k }.Nonempty from hM );
      exact ⟨ _, this, le_antisymm ( csInf_le ⟨ 0, Set.forall_mem_image.2 fun k hk => Nat.cast_nonneg _ ⟩ ⟨ _, this, rfl ⟩ ) ( le_csInf ⟨ _, ⟨ _, this, rfl ⟩ ⟩ <| Set.forall_mem_image.2 fun k hk => Nat.cast_le.2 <| Nat.sInf_le hk ) ⟩;
    · simp_all +decide [ Set.image ]
  obtain ⟨kN, hkN⟩ : ∃ kN, pushesIn L N kN ∧ gradeWrt L N = kN := by
    have h_nonempty : {k | pushesIn L N k}.Nonempty := by
      contrapose! h; simp_all +decide [ gradeWrt ] ;
    have := Nat.sInf_mem h_nonempty;
    exact ⟨ _, this, le_antisymm ( gradeWrt_le_of_pushesIn this ) ( by exact le_csInf ( Set.Nonempty.image _ h_nonempty ) <| Set.forall_mem_image.2 fun k hk => Nat.cast_le.2 <| Nat.sInf_le hk ) ⟩;
  exact h ( by rw [ hkM.2, hkN.2 ] ; exact_mod_cast gradeWrt_le_of_pushesIn ( pushesIn_mul hkM.1 hkN.1 ) )

end Pi3