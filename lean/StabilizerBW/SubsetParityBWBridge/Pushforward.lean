import StabilizerBW.SubsetParityBWBridge.TauMap
import StabilizerBW.SubsetParityBWBridge.BinomialEnum
import StabilizerBW.SubsetParityBWBridge.GradeIsParityCount

/-!
# SubsetParityBWBridge — T5: the operator-side grade fiber count

Combining the uniform `τ`-pushforward (T2), the grade = parity-count identity
(T3) and the binomial parity-vector enumerator (T4) gives the closed-form
count of linear phase polynomials of a given Barnes–Wall grade:
```
  #{P : LinPhase m | gradeOf P = k} = 8 · 4^m · C(m, k).
```
-/

namespace SubsetParityBWBridge.Pushforward

open Finset SubsetParityBWBridge.ParityBit SubsetParityBWBridge.TauMap
open SubsetParityBWBridge.BinomialEnum

/-- The per-monomial odd-indicator sum equals the number of odd parity
coordinates. -/
theorem sum_oddIndic_eq {m : ℕ} (f : Fin m → ZMod 8) :
    (∑ i, T1A.oddIndic (f i)) = (Finset.univ.filter (fun i => parityBit (f i) = true)).card := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  unfold T1A.oddIndic parityBit
  by_cases h : (f i).val % 2 = 1 <;> simp [h]

/-- The weighted coefficient-vector count: `4^m · C(m, k)` vectors
`f : Fin m → ZMod 8` have total odd-indicator weight `k`. -/
theorem weight_count (m k : ℕ) :
    (Finset.univ.filter (fun f : Fin m → ZMod 8 => (∑ i, T1A.oddIndic (f i)) = k)).card
      = 4 ^ m * Nat.choose m k := by
  classical
  rw [← parityVec_grade_count m k]
  set t := Finset.univ.filter (fun b : Fin m → Bool =>
      (Finset.univ.filter (fun i => b i = true)).card = k) with ht
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun f : Fin m → ZMod 8 => (fun i => parityBit (f i))) (t := t)]
  · have hfib : ∀ b ∈ t, (Finset.filter (fun f => (fun i => parityBit (f i)) = b)
        (Finset.univ.filter (fun f : Fin m → ZMod 8 => (∑ i, T1A.oddIndic (f i)) = k))).card
          = 4 ^ m := by
      intro b hb
      simp only [ht, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [← fiber_card (m := m) b]
      congr 1
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · intro h2
        refine ⟨?_, h2⟩
        rw [sum_oddIndic_eq]
        have h3 : ∀ i, parityBit (f i) = b i := funext_iff.mp h2
        simp_rw [h3]; exact hb
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf
    rw [Finset.mem_coe, ht, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hf, sum_oddIndic_eq]

/-- **T5 headline.** The number of linear phase polynomials with Barnes–Wall
grade `k` is `8 · 4^m · C(m, k)`. -/
theorem grade_fiber_card {m : ℕ} (k : ℕ) :
    (Finset.univ.filter (fun P : T1A.LinPhase m => T1A.gradeOf P = k)).card
      = 8 * 4 ^ m * Nat.choose m k := by
  classical
  have hset : (Finset.univ.filter (fun P : T1A.LinPhase m => T1A.gradeOf P = k))
      = (Finset.univ : Finset (ZMod 8)) ×ˢ
          (Finset.univ.filter (fun f : Fin m → ZMod 8 => (∑ i, T1A.oddIndic (f i)) = k)) := by
    ext ⟨c, f⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    rw [T1A.gradeOf_eq_tCount]
    exact Iff.rfl
  rw [hset, Finset.card_product, weight_count]
  simp only [Finset.card_univ, ZMod.card]
  ring

end SubsetParityBWBridge.Pushforward
