import StabilizerBW.T1A.GradeEnumerator
import Mathlib

/-!
# T3 — The BW grade distribution under uniform sampling is `Binomial(m, 1/2)`

For a uniformly random degree-`≤ 1` phase polynomial `P : LinPhase m`
(`= ZMod 8 × (Fin m → ZMod 8)`), the Barnes–Wall grade `gradeOf P` is
distributed as a (scaled) binomial: the number of `P` with `gradeOf P = k` is
`8 · 4^m · C(m, k)`, so the normalised distribution is `C(m,k)/2^m`,
i.e. `Binomial(m, 1/2)`.

This is the `p = 1/2` symmetric-transition equilibrium marginal of LaRacuente's
parity-conditioned chain, and it is exactly the coefficient form of the T1A
generating function `8·4^m·(1+z)^m` (`T1A.grade_GF_binomial`).

The proof routes through the kernel-checked `T1A.gradeOf_eq_tCount`
(`gradeOf P = tCountLin P = #{i : cᵢ odd}`).
-/

namespace ParityChainBWGradeMixing.BWGradeBijection

open Finset T1A

/-- For each `i`, exactly four of the eight residues in `ZMod 8` are odd. -/
theorem card_odd_zmod8 :
    (Finset.univ.filter (fun c : ZMod 8 => c.val % 2 = 1)).card = 4 := by
  decide

/-- The per-coordinate odd indicator equals the membership indicator of the
"odd" subset of `ZMod 8`. -/
theorem oddIndic_eq_one_iff (c : ZMod 8) : oddIndic c = 1 ↔ c.val % 2 = 1 := by
  unfold oddIndic; split <;> simp_all

/-
**Counting lemma.**  The number of functions `Fin m → ZMod 8` with exactly
`k` odd coordinates is `4^m · C(m, k)`: choose the `k` odd positions
(`C(m,k)` ways), each odd position has `4` odd values and each of the other
positions has `4` even values (`4^m` total).
-/
theorem card_oddCount (m k : ℕ) :
    (Finset.univ.filter
        (fun f : Fin m → ZMod 8 => (∑ i, oddIndic (f i)) = k)).card
      = 4 ^ m * Nat.choose m k := by
  induction' m with m ih generalizing k <;> simp_all +decide [ Fin.sum_univ_succ, Nat.choose_succ_succ ];
  · cases k <;> simp +decide [ Nat.choose ];
  · -- We can split the sum into two parts: one where the first coordinate is odd and one where it is even.
    have h_split : (Finset.univ.filter (fun f : Fin (Nat.succ m) → ZMod 8 => oddIndic (f 0) + ∑ i : Fin m, oddIndic (f i.succ) = k)).card =∑ c : ZMod 8, (if oddIndic c = 1 then if k ≥ 1 then (Finset.univ.filter (fun f : Fin m → ZMod 8 => ∑ i : Fin m, oddIndic (f i) = k - 1)).card else 0 else (Finset.univ.filter (fun f : Fin m → ZMod 8 => ∑ i : Fin m, oddIndic (f i) = k)).card) := by
      have h_split : Finset.univ.filter (fun f : Fin (Nat.succ m) → ZMod 8 => oddIndic (f 0) + ∑ i : Fin m, oddIndic (f i.succ) = k) = Finset.biUnion (Finset.univ : Finset (ZMod 8)) (fun c => Finset.image (fun f : Fin m → ZMod 8 => Fin.cons c f) (Finset.univ.filter (fun f : Fin m → ZMod 8 => oddIndic c + ∑ i : Fin m, oddIndic (f i) = k))) := by
        ext f; simp [Fin.cons];
        exact ⟨ fun h => ⟨ f 0, fun i => f i.succ, h, by ext i; cases i using Fin.inductionOn <;> rfl ⟩, by rintro ⟨ a, b, h, rfl ⟩ ; exact h ⟩;
      rw [ h_split, Finset.card_biUnion ];
      · refine' Finset.sum_congr rfl fun c hc => _;
        rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa [ Fin.ext_iff ] using hxy ] ; split_ifs <;> simp_all +decide [ add_comm ] ;
        · convert ih ( k - 1 ) using 1 ; rw [ show k = 1 + ( k - 1 ) by rw [ add_tsub_cancel_of_le ‹1 ≤ k› ] ] ; simp +decide [ add_comm ];
        · unfold oddIndic at *; aesop;
      · intros c hc d hd hcd; simp_all +decide [ Finset.disjoint_left ] ;
        aesop;
    simp_all +decide [ Finset.sum_ite ];
    rw [ show ( Finset.univ.filter fun x : ZMod 8 => oddIndic x = 1 ).card = 4 by rfl, show ( Finset.univ.filter fun x : ZMod 8 => ¬oddIndic x = 1 ).card = 4 by rfl ] ; rcases k with ( _ | k ) <;> simp_all +decide [ Nat.choose_succ_succ, pow_succ' ] ; ring

/-
The total number of linear phase polynomials: `|LinPhase m| = 8 · 8^m`.
-/
theorem card_linPhase (m : ℕ) : Fintype.card (LinPhase m) = 8 * 8 ^ m := by
  -- By definition of split, we have `split m = Prod.mk a (f a)` if and only if `a = (split m).1` and `f a = (split m).2`.
  simp [LinPhase]

/-
**T3 headline (count form).**  The number of degree-`≤ 1` phase polynomials
with Barnes–Wall grade `k` is `8 · 4^m · C(m, k)`.
-/
theorem bwGrade_eq_binomial (m k : ℕ) :
    (Finset.univ.filter (fun P : LinPhase m => gradeOf P = k)).card
      = 8 * 4 ^ m * Nat.choose m k := by
  rw [ show gradeOf = fun P => tCountLin P from funext fun _ => gradeOf_eq_tCount _ ];
  unfold tCountLin;
  convert congr_arg ( · * 8 ) ( card_oddCount m k ) using 1;
  · rw [ mul_comm, Finset.card_filter ];
    erw [ Finset.sum_product ] ; norm_num;
  · grobner

/-- **T3 headline (normalised / probability form).**  The uniform BW grade
distribution equals `Binomial(m, 1/2)`: `P(grade = k) = C(m,k)/2^m`. -/
theorem bwGrade_equilibrium_eq_binomial (m k : ℕ) :
    ((Finset.univ.filter (fun P : LinPhase m => gradeOf P = k)).card : ℝ)
        / (Fintype.card (LinPhase m) : ℝ)
      = (Nat.choose m k : ℝ) / 2 ^ m := by
  rw [bwGrade_eq_binomial, card_linPhase]
  have h8 : (8 : ℝ) ^ m = 4 ^ m * 2 ^ m := by
    rw [← mul_pow]; norm_num
  push_cast
  rw [h8]
  field_simp

end ParityChainBWGradeMixing.BWGradeBijection