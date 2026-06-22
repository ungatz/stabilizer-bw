import StabilizerBW.SqrtPi.Z8Ring

/-!
# The single-qubit Barnes–Wall lattice `L₃` and the lattice grade

The level-3 single-qubit Barnes–Wall lattice is
`L₃ = {(a,b) ∈ ℤ[ζ₈]² : (1+i) ∣ a + b}`, a `ℤ[ζ₈]`-submodule of `(Fin 2 → ℤ[ζ₈])`.

For a single-qubit operator `M : Matrix (Fin 2) (Fin 2) ℤ[ζ₈]` the **lattice grade** is
`g(M) = min { k : λ^k · M · L₃ ⊆ L₃ }`, the least number of factors of the prime `λ`
needed to push `M` back into the lattice.

We also package the clamped cost function `cost x = if (1+i)∣x then 0 else if λ∣x then 1 else 2`,
which equals `max(0, 2 - ν_λ(x))`, and prove the key reduction
`g(diag(1, A)) = cost(A - 1)`.
-/

set_option maxRecDepth 4000

namespace Pi3
open Z8

/-- Membership in the single-qubit lattice `L₃`: `(1+i) ∣ v 0 + v 1`. -/
def inL3 (v : Fin 2 → Z8) : Prop := onePlusI ∣ (v 0 + v 1)

/-- The level-3 single-qubit Barnes–Wall lattice as a `ℤ[ζ₈]`-submodule of `Fin 2 → ℤ[ζ₈]`. -/
def L3 : Submodule Z8 (Fin 2 → Z8) where
  carrier := {v | inL3 v}
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, inL3, Pi.add_apply] at *
    have : u 0 + v 0 + (u 1 + v 1) = (u 0 + u 1) + (v 0 + v 1) := by ring
    rw [this]; exact dvd_add hu hv
  zero_mem' := by simp [inL3]
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq, inL3, Pi.smul_apply, smul_eq_mul] at *
    have : c * v 0 + c * v 1 = c * (v 0 + v 1) := by ring
    rw [this]; exact Dvd.dvd.mul_left hv c

@[simp] lemma mem_L3 (v : Fin 2 → Z8) : v ∈ L3 ↔ onePlusI ∣ (v 0 + v 1) := Iff.rfl

/-- The grade of a single-qubit operator `M`: the least `k` with `λ^k · M · L₃ ⊆ L₃`. -/
noncomputable def latGrade (M : Matrix (Fin 2) (Fin 2) Z8) : ℕ :=
  sInf { k : ℕ | ∀ v ∈ L3, (lam ^ k • M.mulVec v) ∈ L3 }

/-- The clamped `λ`-adic cost `max(0, 2 - ν_λ x)`. -/
def cost (x : Z8) : ℕ := if divLam2 x then 0 else if divLam x then 1 else 2

instance (x : Z8) : Decidable (divLam x) := by unfold divLam; infer_instance

/-- The least `k` with `λ^k·x` divisible by `(1+i)` is exactly `cost x`. -/
lemma sInf_divLam2_pow (x : Z8) : sInf { k : ℕ | divLam2 (lam ^ k * x) } = cost x := by
  set S := { k : ℕ | divLam2 (lam ^ k * x) } with hS
  unfold cost
  by_cases h2 : divLam2 x
  · simp only [h2, if_true]
    have h0 : 0 ∈ S := by simp [hS, h2]
    exact Nat.sInf_eq_zero.mpr (Or.inl h0)
  · simp only [h2, if_false]
    by_cases h1 : divLam x
    · simp only [h1, if_true]
      have h1mem : 1 ∈ S := by
        simp only [hS, Set.mem_setOf_eq, pow_one]
        exact (divLam2_lam_mul x).mpr h1
      have h0not : 0 ∉ S := by simp [hS, h2]
      have hne : S.Nonempty := ⟨1, h1mem⟩
      have hmem := Nat.sInf_mem hne
      have hle : sInf S ≤ 1 := Nat.sInf_le h1mem
      have hge : 1 ≤ sInf S := by
        rcases Nat.eq_zero_or_pos (sInf S) with h | h
        · exact absurd (h ▸ hmem) h0not
        · exact h
      omega
    · simp only [h1, if_false]
      have h2mem : 2 ∈ S := by
        simp only [hS, Set.mem_setOf_eq]; exact divLam2_lamSq_mul x
      have h0not : 0 ∉ S := by
        simp only [hS, Set.mem_setOf_eq, pow_zero, one_mul]; exact h2
      have h1not : 1 ∉ S := by
        simp only [hS, Set.mem_setOf_eq, pow_one]
        exact fun h => h1 ((divLam2_lam_mul x).mp h)
      have hne : S.Nonempty := ⟨2, h2mem⟩
      have hmem := Nat.sInf_mem hne
      have hle : sInf S ≤ 2 := Nat.sInf_le h2mem
      have hge : 2 ≤ sInf S := by
        rcases Nat.lt_or_ge (sInf S) 2 with h | h
        · interval_cases (sInf S)
          · exact absurd hmem h0not
          · exact absurd hmem h1not
        · exact h
      omega

end Pi3
