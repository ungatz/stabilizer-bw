import StabilizerBW.SubsetParityBWBridge.ParityBit

/-!
# SubsetParityBWBridge — T4: the binomial parity-vector enumerator

`parityVec_grade_count` is the classical counting identity at the
function-from-`Fin m`-to-`Bool` level: the number of Boolean vectors with
exactly `k` ones is `C(m, k)`.  This is the measurement-side input that
identifies the parity-count marginal with `Binomial(m, 1/2)`.
-/

namespace SubsetParityBWBridge.BinomialEnum

open Finset

/-- **T4 headline.** The number of Boolean vectors `b̄ : Fin m → Bool` with
exactly `k` ones is `C(m, k)`. -/
theorem parityVec_grade_count (m k : ℕ) :
    (Finset.univ.filter (fun b : Fin m → Bool =>
        (Finset.univ.filter (fun i => b i = true)).card = k)).card = Nat.choose m k := by
  classical
  have hrw : Nat.choose m k = (Finset.powersetCard k (Finset.univ : Finset (Fin m))).card := by
    rw [Finset.card_powersetCard]; simp
  rw [hrw]
  apply Finset.card_bij (fun b _ => Finset.univ.filter (fun i => b i = true))
  · intro b hb
    simp only [Finset.mem_filter] at hb
    simp only [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hb.2⟩
  · intro b1 hb1 b2 hb2 h
    funext i
    have := congrArg (fun s => i ∈ s) h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    rcases hb1' : b1 i <;> rcases hb2' : b2 i <;> simp_all
  · intro s hs
    simp only [Finset.mem_powersetCard] at hs
    refine ⟨fun i => decide (i ∈ s), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hs.2]; congr 1; ext i; simp
    · ext i; simp

end SubsetParityBWBridge.BinomialEnum
