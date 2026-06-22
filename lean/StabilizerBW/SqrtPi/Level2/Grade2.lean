import StabilizerBW.SqrtPi.Level2.Zi

/-!
# The level-2 lattice grade `gradeWrt₂`

For an operator `M : Matrix (Fin n) (Fin n) ℚ[ζ₈]` and a `ℤ[i]`-lattice
`L ⊆ (Fin n → ℤ[i])`, the **level-2 grade** is `min { k : λ₂^k · M · L ⊆ L }`, i.e. the least
number of factors of the level-2 prime `λ₂ = 1 - i` needed to push `M` back into the lattice.

This is the exact level-2 analogue of `Pi3.gradeWrt` from `Grade.lean`, with the level-3 prime
`λ` replaced by the level-2 prime `λ₂` and the integral lattice taken over `ℤ[i]` (embedded into
the level-3 denotation field `ℚ[ζ₈]` via `Zi.toQ8`).
-/

set_option maxRecDepth 4000

namespace Pi3
open Zi

/-- The coercion of a `ℤ[i]`-vector into `ℚ[ζ₈]ⁿ` via `ℤ[i] ↪ ℚ[ζ₈]`. -/
def coeViVec {n : ℕ} (v : Fin n → Zi) : Fin n → Q8 := fun i => Zi.toQ8 (v i)

@[simp] lemma coeViVec_apply {n : ℕ} (v : Fin n → Zi) (i : Fin n) :
    coeViVec v i = Zi.toQ8 (v i) := rfl

@[simp] lemma coeViVec_zero {n : ℕ} : coeViVec (0 : Fin n → Zi) = 0 := by
  funext i; simp only [coeViVec, Pi.zero_apply, ← Zi.toQ8Hom_apply, map_zero]

lemma coeViVec_add {n : ℕ} (u v : Fin n → Zi) :
    coeViVec (u + v) = coeViVec u + coeViVec v := by
  funext i
  simp only [coeViVec, Pi.add_apply, ← Zi.toQ8Hom_apply, map_add]

lemma coeViVec_smul {n : ℕ} (c : Zi) (v : Fin n → Zi) :
    coeViVec (c • v) = Zi.toQ8 c • coeViVec v := by
  funext i
  simp only [coeViVec, Pi.smul_apply, smul_eq_mul, ← Zi.toQ8Hom_apply, map_mul]

/-- The image of the level-2 prime `λ₂` in `ℚ[ζ₈]`. -/
def lam2Q : Q8 := Zi.toQ8 Zi.lam2

/-- `M` pushes `L` into `L` after scaling by `λ₂^k`: for every lattice point `v`,
`λ₂^k · M · v` is again (the coercion of) a lattice point. -/
def pushesIn2 {n : ℕ} (L : Submodule Zi (Fin n → Zi))
    (M : Matrix (Fin n) (Fin n) Q8) (k : ℕ) : Prop :=
  ∀ v ∈ L, ∃ w ∈ L, lam2Q ^ k • M.mulVec (coeViVec v) = coeViVec w

/-- The level-2 lattice grade of `M` with respect to the `ℤ[i]`-lattice `L`, in `ℕ∞`. -/
noncomputable def gradeWrt2 {n : ℕ} (L : Submodule Zi (Fin n → Zi))
    (M : Matrix (Fin n) (Fin n) Q8) : ℕ∞ :=
  sInf ((Nat.cast : ℕ → ℕ∞) '' {k | pushesIn2 L M k})

lemma gradeWrt2_le_of_pushesIn {n : ℕ} {L : Submodule Zi (Fin n → Zi)}
    {M : Matrix (Fin n) (Fin n) Q8} {k : ℕ} (h : pushesIn2 L M k) :
    gradeWrt2 L M ≤ (k : ℕ∞) :=
  sInf_le ⟨k, h, rfl⟩

/-- `pushesIn2` is monotone in `k`: more factors of `λ₂` never hurt. -/
lemma pushesIn2_succ {n : ℕ} {L : Submodule Zi (Fin n → Zi)}
    {M : Matrix (Fin n) (Fin n) Q8} {k : ℕ} (h : pushesIn2 L M k) :
    pushesIn2 L M (k + 1) := by
  intro v hv
  obtain ⟨w, hw, hwEq⟩ := h v hv
  refine ⟨lam2 • w, L.smul_mem _ hw, ?_⟩
  have : coeViVec (lam2 • w) = lam2Q • coeViVec w := by
    funext i
    simp only [coeViVec, lam2Q, Pi.smul_apply, smul_eq_mul]
    rw [← Zi.toQ8Hom_apply, ← Zi.toQ8Hom_apply, ← Zi.toQ8Hom_apply, map_mul]
  rw [this, ← hwEq, pow_succ]
  rw [mul_comm (lam2Q ^ k) lam2Q, mul_smul]

/-- Helper: pin down `gradeWrt2` from an upper-bound witness and a minimality witness. -/
lemma gradeWrt2_eq {n : ℕ} (L : Submodule Zi (Fin n → Zi))
    (M : Matrix (Fin n) (Fin n) Q8) (val : ℕ)
    (hup : pushesIn2 L M val)
    (hlow : ∀ k, k < val → ¬ pushesIn2 L M k) :
    gradeWrt2 L M = (val : ℕ∞) := by
  apply le_antisymm (gradeWrt2_le_of_pushesIn hup)
  rw [gradeWrt2]
  apply le_csInf ⟨(val : ℕ∞), Set.mem_image_of_mem _ hup⟩
  rintro x ⟨k, hk, rfl⟩
  by_contra hlt
  push_neg at hlt
  have : k < val := by exact_mod_cast hlt
  exact hlow k this hk

end Pi3
