import StabilizerBW.Grade.StratifiedMonotone.PhysicalDensity

/-!
# T2 — the Pauli-weight enumerator `(1 + 3z)^m`

This is the **corrected** generating function for the corrected construction.  The original construction wrongly transported
`T1A.grade_GF_linear_factorises = 8·4^m·(1+z)^m`, which enumerates *linear phase polynomials*
graded by T-count, NOT the Pauli strings graded by Pauli weight that the Dutta–Tushar `ℓ¹`
functional actually sees.

The correct enumerator (MacWilliams–Sloane, Heisenberg–Weyl at `d = 2`) is
```
  W_m(z) = ∑_{P : PauliIdx m} z^{wt(P)} = (1 + 3z)^m ,
```
the factor `3 = |{X, Y, Z}|` being the number of non-identity single-qubit Paulis.  The coefficient
of `z^g` is the **weight-`g` stratum cardinality** `C(m,g)·3^g`.
-/

namespace BWGradeStratifiedMonotoneR2

open Finset

/-- The **Pauli-weight enumerator** `∑_{P} z^{wt(P)}`. -/
noncomputable def pauliWeightEnumerator (m : ℕ) (z : ℝ) : ℝ :=
  ∑ P : PauliIdx m, z ^ (BWGradeOfPauli m P)

/-
**Closed form (MacWilliams–Sloane).** `W_m(z) = (1 + 3z)^m`.
-/
theorem pauliWeightEnumerator_factorises (m : ℕ) (z : ℝ) :
    pauliWeightEnumerator m z = (1 + 3 * z) ^ m := by
  -- Apply the lemma that states the sum of the weights of all Pauli strings is equal to the product of (1 + 3z) over all positions.
  have h_sum_weights : ∑ P : PauliIdx m, z ^ (BWGradeOfPauli m P) = ∏ i : Fin m, ∑ c : Fin 4, (if c ≠ 0 then z else 1) := by
    rw [ Finset.prod_sum ];
    refine' Finset.sum_bij ( fun P _ => fun i _ => P i ) _ _ _ _ <;> simp +decide [ BWGradeOfPauli ];
    · simp +decide [ funext_iff ];
    · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
    · simp +decide [ Finset.prod_ite, Finset.filter_not ];
  convert h_sum_weights using 1;
  norm_num [ Fin.sum_univ_four ] ; ring;
  simp +decide ; ring

/-
**Weight-stratum cardinality.** The number of Pauli strings of weight exactly `g` on `m`
qubits is `C(m,g)·3^g`.
-/
theorem pauliWeightStratumCardinality (m g : ℕ) :
    (Finset.univ.filter (fun P : PauliIdx m => BWGradeOfPauli m P = g)).card
      = Nat.choose m g * 3 ^ g := by
  -- For each subset of size `g` in `{0, 1, ..., m-1}`, there are `3^g` ways to assign values to the elements of `P`.
  have h_count : ∀ (S : Finset (Fin m)), (Finset.filter (fun P : Fin m → Fin 4 => (Finset.univ.filter (fun i => P i ≠ 0)) = S) Finset.univ).card = 3 ^ S.card := by
    intro S; rw [ show ( Finset.filter ( fun P : Fin m → Fin 4 => Finset.filter ( fun i => P i ≠ 0 ) Finset.univ = S ) Finset.univ ) = Finset.image ( fun f : S → Fin 3 => fun i => if hi : i ∈ S then Fin.succ ( f ⟨ i, hi ⟩ ) else 0 ) ( Finset.univ : Finset ( S → Fin 3 ) ) from ?_ ] ; rw [ Finset.card_image_of_injective ] ;
    · simp +decide [ Finset.card_univ ];
    · intro f g hfg; ext ⟨ i, hi ⟩ ; replace hfg := congr_fun hfg i; aesop;
    · ext P; simp [Finset.mem_image];
      constructor;
      · intro hP; use fun i => Fin.pred ( P i ) ( by
          grind ) ; ext i; by_cases hi : i ∈ S <;> simp +decide [ hi ] ;
        grind +qlia;
      · grind;
  -- By summing over all subsets of size `g`, we get the total number of Pauli strings of weight `g`.
  have h_sum : (Finset.univ.filter (fun P : Fin m → Fin 4 => BWGradeOfPauli m P = g)).card = ∑ S ∈ Finset.powersetCard g (Finset.univ : Finset (Fin m)), (Finset.filter (fun P : Fin m → Fin 4 => Finset.univ.filter (fun i => P i ≠ 0) = S) Finset.univ).card := by
    simp +decide only [card_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  simp_all +decide [ Finset.sum_powersetCard ]

end BWGradeStratifiedMonotoneR2