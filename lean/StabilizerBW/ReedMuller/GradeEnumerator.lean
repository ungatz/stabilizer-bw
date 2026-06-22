import StabilizerBW.ReedMuller.GradeLinear

/-!
# ReedMuller — the pure-linear Barnes–Wall grade enumerator (Tier S headline)

For diagonal Clifford+T operators on `m` qubits with phase polynomial of degree
`≤ 1`, the generating function of the Barnes–Wall grade is
```
  G_m(z) = ∑_{P : deg ≤ 1} z^{g(D_P)} = 8 · 4^m · (1 + z)^m .
```

This file assembles the closed form from `gradeOf_eq_tCount` (the grade equals
the per-monomial T-count at degree `≤ 1`) and the per-coordinate factorisation of
the operator count.
-/

namespace ReedMuller

open scoped Classical
open Finset

/-! ## Per-monomial generating-function factors -/

/-- **Sub-lemma 5.** The constant in the ANF contributes a factor `8` (any of the
8 ℤ/8 values, all with grade contribution `0`). -/
theorem constant_GF (z : ℤ) : (∑ _c : ZMod 8, z ^ (0 : ℕ)) = 8 := by simp

/-
**Sub-lemma 4.** Per-linear-monomial generating function: `4` even-coefficient
choices give T-count `0`, `4` odd-coefficient choices give T-count `1`.
-/
theorem perLinearMonomial_GF (z : ℤ) :
    (∑ c : ZMod 8, z ^ (if c.val % 2 = 1 then 1 else 0)) = 4 + 4 * z := by
  erw [ Fin.sum_univ_eight ] ; simp +decide ; ring

/-! ## The operator-sum generating function -/

/-
The T-count generating function factorises over qubits.
-/
theorem tcount_GF (m : ℕ) (z : ℤ) :
    (∑ P : LinPhase m, z ^ tCountLin P) = 8 * (4 + 4 * z) ^ m := by
  have h_sum : ∑ P : (ZMod 8) × (Fin m → ZMod 8), z ^ (∑ i : Fin m, if (P.2 i).val % 2 = 1 then 1 else 0) = 8 * (∑ c : ZMod 8, z ^ (if c.val % 2 = 1 then 1 else 0)) ^ m := by
    erw [ Finset.sum_product ] ; norm_num [ Finset.prod_ite ] ; ring;
    rw [ ← Fin.prod_const ];
    rw [ Finset.prod_sum ];
    refine' Finset.sum_bij ( fun x _ => fun i _ => x i ) _ _ _ _ <;> simp +decide [ Finset.prod_ite ];
    · simp +decide [ funext_iff ];
    · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
    · intro a; rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ] ; congr; ext; aesop;
  convert h_sum using 2;
  exact ReedMuller.perLinearMonomial_GF z ▸ rfl

/-- **Sub-lemma 6 / headline (factored form).** The pure-linear grade generating
function factorises as `constant × per-qubit-linear^m`. -/
theorem grade_GF_linear_factorises (m : ℕ) (z : ℤ) :
    (∑ P : LinPhase m, z ^ gradeOf P) = 8 * (4 + 4 * z) ^ m := by
  rw [← tcount_GF]
  exact Finset.sum_congr rfl (fun P _ => by rw [gradeOf_eq_tCount])

/-- **Tier S headline.** `G_m(z) = 8 · 4^m · (1 + z)^m`. -/
theorem grade_GF_linear_headline (m : ℕ) (z : ℤ) :
    (∑ P : LinPhase m, z ^ gradeOf P) = 8 * 4 ^ m * (1 + z) ^ m := by
  rw [grade_GF_linear_factorises]
  rw [show (4 : ℤ) + 4 * z = 4 * (1 + z) by ring, mul_pow]
  ring

/-
**Headline (binomial / coefficient form).** Expanding `(1+z)^m`, the grade
enumerator is `∑_k 8·4^m·C(m,k)·z^k`.
-/
theorem grade_GF_binomial (m : ℕ) (z : ℤ) :
    (∑ k ∈ Finset.Iic m, (Nat.choose m k : ℤ) * (8 * 4 ^ m) * z ^ k)
      = 8 * 4 ^ m * (1 + z) ^ m := by
  rw [ add_comm 1 z, add_pow ];
  rw [ Finset.mul_sum _ _ _ ] ; rw [ Finset.range_eq_Ico ] ; exact Finset.sum_congr rfl fun _ _ => by ring;

end ReedMuller