import StabilizerBW.SubsetParityBWBridge.Pushforward

/-!
# SubsetParityBWBridge — T6: the closed-form Barnes–Wall grade distribution

Normalising the operator-side fiber count by the size `8^{m+1}` of the
linear stratum gives the closed-form distribution of the Barnes–Wall grade:
```
  #{P : LinPhase m | gradeOf P = k} / 8^{m+1} = C(m, k) / 2^m,
```
i.e. the grade is distributed as `Binomial(m, 1/2)`.
-/

namespace SubsetParityBWBridge.Distribution

open Finset

/-- **T6 headline.** The Barnes–Wall grade distribution on the linear stratum is
`Binomial(m, 1/2)`: the fraction of linear phase polynomials with grade `k` is
`C(m, k) / 2^m`.  (The hypothesis `hk : k ≤ m`, requested, is not
needed — the identity holds for every `k`, since both sides vanish for `k > m`.)
-/
theorem grade_distribution_BW {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    ((Finset.univ.filter (fun P : ReedMuller.LinPhase m => ReedMuller.gradeOf P = k)).card : ℚ) / 8 ^ (m + 1)
      = (Nat.choose m k : ℚ) / 2 ^ m := by
  rw [SubsetParityBWBridge.Pushforward.grade_fiber_card]
  push_cast
  have h8 : (8 : ℚ) ^ (m + 1) = 4 ^ m * 2 ^ m * 8 := by rw [pow_succ, ← mul_pow]; norm_num
  rw [h8]
  have h4 : (4 : ℚ) ^ m ≠ 0 := by positivity
  have h2 : (2 : ℚ) ^ m ≠ 0 := by positivity
  field_simp

end SubsetParityBWBridge.Distribution
