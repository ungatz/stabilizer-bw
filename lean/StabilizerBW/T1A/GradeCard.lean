import StabilizerBW.T1A.GradeEnumerator

/-!
# T1A — the pure-linear grade enumerator in cardinality form

Coefficient extraction from the generating function gives the per-grade operator
counts:
```
  #{ P : deg ≤ 1 | g(D_P) = k } = 8 · 4^m · C(m, k).
```

We prove a generic (any commutative semiring) version of the generating-function
factorisation, specialise it to `ℤ[X]`, and read off the coefficient at `z^k`.
-/

namespace T1A

open scoped Classical
open Finset

/-
Per-linear-monomial GF over any commutative semiring.
-/
theorem perLinearMonomial_GF_generic {R : Type*} [CommSemiring R] (z : R) :
    (∑ c : ZMod 8, z ^ (if c.val % 2 = 1 then 1 else 0)) = 4 + 4 * z := by
  erw [ Fin.sum_univ_eight ] ; simp +decide ; ring!;

/-
The T-count GF factorisation over any commutative semiring.
-/
theorem tcount_GF_generic {R : Type*} [CommSemiring R] (m : ℕ) (z : R) :
    (∑ P : LinPhase m, z ^ tCountLin P) = 8 * (4 + 4 * z) ^ m := by
  -- By definition of tCountLin, we can write it as a sum over the components of P.
  have h_tCountLin : ∀ P : LinPhase m, tCountLin P = ∑ i : Fin m, (if (P.2 i).val % 2 = 1 then 1 else 0) := by
    -- By definition of `tCountLin`, we have `tCountLin P = ∑ i, oddIndic (P.2 i)`.
    simp [tCountLin, oddIndic];
  -- Apply the definition of `tCountLin` to rewrite the sum.
  simp_rw [h_tCountLin];
  -- Apply the definition of `Finset.sum_product` to rewrite the sum.
  have h_sum_product : ∑ x : ZMod 8 × (Fin m → ZMod 8), z ^ (∑ i : Fin m, if (x.2 i).val % 2 = 1 then 1 else 0) = 8 * ∑ f : Fin m → ZMod 8, z ^ (∑ i : Fin m, if (f i).val % 2 = 1 then 1 else 0) := by
    erw [ Finset.sum_product ] ; simp +decide [ Finset.sum_const, nsmul_eq_mul ];
  convert h_sum_product using 2;
  rw [ ← perLinearMonomial_GF_generic z ];
  rw [ ← Fin.prod_const, Finset.prod_sum ];
  refine' Finset.sum_bij ( fun f _ => fun i => f i ( Finset.mem_univ i ) ) _ _ _ _ <;> simp +decide;
  · simp +decide [ funext_iff ];
  · exact fun b => ⟨ fun i _ => b i, rfl ⟩;
  · simp +decide [ Finset.prod_ite ]

/-
The grade GF as a polynomial in `ℤ[X]`.
-/
theorem grade_GF_poly (m : ℕ) :
    (∑ P : LinPhase m, (Polynomial.X : Polynomial ℤ) ^ gradeOf P)
      = (8 * 4 ^ m : ℤ) • (1 + Polynomial.X) ^ m := by
  -- Now use `tcount_GF_generic` to rewrite the sum in terms of `(4 + 4 * Polynomial.X)^m`.
  have h_sum : ∑ P : T1A.LinPhase m, Polynomial.X ^ tCountLin P = 8 * (4 + 4 * (Polynomial.X : Polynomial ℤ)) ^ m := by
    convert tcount_GF_generic m ( Polynomial.X : Polynomial ℤ ) using 1;
  rw [ Finset.sum_congr rfl fun _ _ => by rw [ gradeOf_eq_tCount ] ];
  rw [ h_sum, show ( 4 + 4 * Polynomial.X : Polynomial ℤ ) = 4 * ( 1 + Polynomial.X ) by ring, mul_pow ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, Polynomial.smul_eq_C_mul ]

/-
**Cardinality form (`grade_GF_linear`).** The number of degree-`≤ 1` phase
polynomials whose operator has Barnes–Wall grade `k`.
-/
theorem grade_GF_linear (m k : ℕ) :
    (Finset.univ.filter (fun P : LinPhase m => gradeOf P = k)).card
      = 8 * 4 ^ m * Nat.choose m k := by
  by_contra h_contra;
  have h_card : (∑ P : LinPhase m, (Polynomial.X : Polynomial ℤ) ^ gradeOf P).coeff k = (8 * 4 ^ m : ℤ) * (Nat.choose m k : ℤ) := by
    rw [ grade_GF_poly ];
    rw [ Polynomial.coeff_smul, Polynomial.coeff_one_add_X_pow ] ; norm_num;
  simp_all +decide [ Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow ];
  exact h_contra <| by rw [ Finset.filter_congr fun x hx => eq_comm ] at h_card; exact_mod_cast h_card;

end T1A