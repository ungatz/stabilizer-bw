import StabilizerBW.SqrtPi.Catalyst.Phi3

/-!
# T3**(a) — The tensor-swap `σ^⊗`, its grade, and conjugation invariance

The CHKRS SI Definition S12 catalytic embedding realises the `⊕`-rule
`Φ₃(a ⊕ b) = σ^⊗ ∘ (Φ₃ a ⊞ Φ₃ b) ∘ (σ^⊗)†`, where `σ^⊗` is the symmetric-monoidal tensor-swap
reorganising `2 ⊗ (m + n) ≅ (2 ⊗ m) + (2 ⊗ n)`.  At the verification object (single qubit
`= 2`, with `m = n = 1`) this is the coordinate transposition `(1 2)` of `Fin 4`, realised as the
honest `Π₂` morphism `σ^⊗ = (id₁ ⊞ σ_⊕) ⊞ id₁`.

This file discharges the prior round's blocker §6 (the `σ^⊗` conjugation had been *dropped* from
`Φ₃` for kernel tractability, with invariance only checked numerically) by kernel-proving:

* `Pi3.gradeWrt2_conj_eq` — **the general invariance**: conjugation by *any* grade-`0` lattice
  automorphism preserves the level-2 grade (this is the mathematical content of T3**(a)(iii));
* `Pi3.grade2_swap_eq_zero` — `σ^⊗` is grade `0` (it permutes lattice coordinates);
* `Pi3.grade2_swap_conj_invariant` — `grade₂(σ^⊗ ∘ M ∘ σ^⊗) = grade₂ M` for every `M`;
* `Pi3.Headline_T3_with_swap` — re-proving the `Φ₃(T)` grade **with** the `σ^⊗` conjugation in
  place: `grade₂(σ^⊗ ∘ Φ₃(T) ∘ σ^⊗) = grade₂(Φ₃ T) = grade₃(T) = 1`, confirming the value is
  unchanged by the (now kernel-justified) tensor-swap.
-/

set_option maxRecDepth 4000

namespace Pi3
open Pi3.Zi

/-! ### The general grade-conjugation invariance -/

/-- Left-multiplication by a grade-`0` lattice map preserves `pushesIn2`. -/
lemma pushesIn2_mul_left {n : ℕ} {L : Submodule Zi (Fin n → Zi)}
    {A N : Matrix (Fin n) (Fin n) Q8} {k : ℕ}
    (hA : pushesIn2 L A 0) (hN : pushesIn2 L N k) :
    pushesIn2 L (A * N) k := by
  intro v hv
  obtain ⟨w, hw, hwEq⟩ := hN v hv
  obtain ⟨w', hw', hw'Eq⟩ := hA w hw
  refine ⟨w', hw', ?_⟩
  rw [pow_zero, one_smul] at hw'Eq
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, hwEq, hw'Eq]

/-- Right-multiplication by a grade-`0` lattice map preserves `pushesIn2`. -/
lemma pushesIn2_mul_right {n : ℕ} {L : Submodule Zi (Fin n → Zi)}
    {A N : Matrix (Fin n) (Fin n) Q8} {k : ℕ}
    (hA : pushesIn2 L A 0) (hN : pushesIn2 L N k) :
    pushesIn2 L (N * A) k := by
  intro v hv
  obtain ⟨u, hu, huEq⟩ := hA v hv
  rw [pow_zero, one_smul] at huEq
  obtain ⟨w, hw, hwEq⟩ := hN u hu
  refine ⟨w, hw, ?_⟩
  rw [← Matrix.mulVec_mulVec, huEq, hwEq]

/-- The conjugating-set equality underlying the invariance. -/
lemma pushesIn2_conj_iff {n : ℕ} {L : Submodule Zi (Fin n → Zi)}
    {M P Pinv : Matrix (Fin n) (Fin n) Q8} {k : ℕ}
    (hP : pushesIn2 L P 0) (hPinv : pushesIn2 L Pinv 0)
    (hPP' : Pinv * P = 1) :
    pushesIn2 L (P * M * Pinv) k ↔ pushesIn2 L M k := by
  constructor
  · intro h
    have h2 : pushesIn2 L (Pinv * (P * M * Pinv) * P) k :=
      pushesIn2_mul_right hP (pushesIn2_mul_left hPinv h)
    have heq : Pinv * (P * M * Pinv) * P = M := by
      rw [show Pinv * (P * M * Pinv) * P = (Pinv * P) * M * (Pinv * P) by noncomm_ring, hPP',
        one_mul, mul_one]
    rwa [heq] at h2
  · intro h
    exact pushesIn2_mul_right hPinv (pushesIn2_mul_left hP h)

/-- **General conjugation invariance.** Conjugating an operator by a grade-`0` lattice
automorphism `P` (with two-sided grade-`0` inverse `Pinv`) preserves the level-2 lattice grade. -/
theorem gradeWrt2_conj_eq {n : ℕ} (L : Submodule Zi (Fin n → Zi))
    (M P Pinv : Matrix (Fin n) (Fin n) Q8)
    (hP : pushesIn2 L P 0) (hPinv : pushesIn2 L Pinv 0)
    (hPP' : Pinv * P = 1) :
    gradeWrt2 L (P * M * Pinv) = gradeWrt2 L M := by
  have hset : {k | pushesIn2 L (P * M * Pinv) k} = {k | pushesIn2 L M k} := by
    ext k; exact pushesIn2_conj_iff hP hPinv hPP'
  rw [gradeWrt2, gradeWrt2, hset]

/-! ### The concrete tensor-swap `σ^⊗ = (id₁ ⊞ σ_⊕) ⊞ id₁` -/

/-- The tensor-swap `σ^⊗ : Π₂(4,4)`, the coordinate transposition `(1 2)`. -/
def swapT : Pi2 4 4 := (Pi2.idn 1 ⊞₂ Pi2.swp) ⊞₂ Pi2.idn 1

/-- The integral (`ℤ[i]`) form of `⟦σ^⊗⟧₂`: the permutation matrix of the transposition `(1 2)`. -/
def NswapT : Matrix (Fin 4) (Fin 4) Zi :=
  Matrix.of ![![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 1]]

lemma denote_swapT_map : Pi2.denote swapT = NswapT.map Zi.toQ8 := by
  funext i j; fin_cases i <;> fin_cases j <;> decide +kernel

/-- `σ^⊗` is a grade-`0` lattice map: `pushesIn2 BW2L ⟦σ^⊗⟧₂ 0`. -/
lemma swap_pushesIn0 : pushesIn2 BW2L (Pi2.denote swapT) 0 := by
  rw [denote_swapT_map]
  exact pushesIn2_integral_of_mapsGen NswapT 0
    ((mem_BW2L_iff _).mpr (by decide)) ((mem_BW2L_iff _).mpr (by decide))
    ((mem_BW2L_iff _).mpr (by decide)) ((mem_BW2L_iff _).mpr (by decide))

/-- **Pi3.grade2_swap_eq_zero.** The tensor-swap `σ^⊗` has level-2 grade `0` (it permutes lattice
coordinates and hence preserves the Barnes–Wall lattice). -/
theorem grade2_swap_eq_zero : Pi2.grade2 swapT = 0 := by
  rw [Pi2.grade2]
  have h := gradeWrt2_eq BW2L (Pi2.denote swapT) 0 swap_pushesIn0 (by intro k hk; omega)
  simpa using h

/-- `σ^⊗` is its own inverse at the matrix level (`(1 2)` is an involution). -/
lemma swapT_mul_self : Pi2.denote swapT * Pi2.denote swapT = 1 := by
  funext i j; fin_cases i <;> fin_cases j <;> decide +kernel

/-- **Pi3.grade2_swap_conj_invariant.** Conjugation by the tensor-swap `σ^⊗` preserves the
level-2 grade: `grade₂(σ^⊗ ∘ M ∘ σ^⊗) = grade₂ M` for every `M : Π₂(4,4)`.  (Here `σ^⊗† = σ^⊗`
since the swap is an involution.) -/
theorem grade2_swap_conj_invariant (M : Pi2 4 4) :
    Pi2.grade2 (swapT ⊚₂ M ⊚₂ swapT) = Pi2.grade2 M := by
  have hden : Pi2.denote (swapT ⊚₂ M ⊚₂ swapT)
      = Pi2.denote swapT * Pi2.denote M * Pi2.denote swapT := by
    show Pi2.denote (M ⊚₂ swapT) * Pi2.denote swapT
        = Pi2.denote swapT * Pi2.denote M * Pi2.denote swapT
    rw [Pi2.denote_circ]
  rw [Pi2.grade2, Pi2.grade2, hden]
  exact gradeWrt2_conj_eq BW2L (Pi2.denote M) (Pi2.denote swapT) (Pi2.denote swapT)
    swap_pushesIn0 swap_pushesIn0 swapT_mul_self

/-! ### `Φ₃(T)` with the `σ^⊗` conjugation -/

/-- `Φ₃(T)` realised **with** the CHKRS-S12 tensor-swap conjugation in place. -/
def phiT_swap : Pi2 4 4 := swapT ⊚₂ Pi2.phiT ⊚₂ swapT

/-- The `σ^⊗`-conjugated `Φ₃(T)` has the same level-2 grade as the bare `Φ₃(T)`, namely `1`. -/
theorem grade2_phiT_swap : Pi2.grade2 phiT_swap = 1 := by
  rw [phiT_swap, grade2_swap_conj_invariant, grade2_phiT]

/-- The bare `Φ₃(T)` grade, re-exported for the headline. -/
lemma grade2_phiT_eq_one : Pi2.grade2 Pi2.phiT = 1 := grade2_phiT

/-- **Pi3.Headline_T3_with_swap.** With the (now kernel-justified) tensor-swap `σ^⊗` conjugation
restored to the catalytic embedding, the grade of `Φ₃(T)` is unchanged:
`grade₂(σ^⊗ ∘ Φ₃(T) ∘ σ^⊗) = grade₂(Φ₃ T) = grade₃(T) = 1`.  Together with `grade2_swap_eq_zero`
and `grade2_swap_conj_invariant`, this discharges blocker §6: the `σ^⊗` is a grade-`0` lattice
automorphism whose conjugation provably leaves every level-2 grade invariant, so the corrected
rule `Γ(g) = g` holds with or without it. -/
theorem Headline_T3_with_swap :
    Pi2.grade2 phiT_swap = Pi2.grade2 Pi2.phiT ∧
    Pi2.grade2 phiT_swap = grade2obj tGate ∧
    Pi2.grade2 phiT_swap = 1 := by
  refine ⟨?_, ?_, grade2_phiT_swap⟩
  · rw [phiT_swap, grade2_swap_conj_invariant]
  · rw [grade2_phiT_swap, grade3_T]

end Pi3
