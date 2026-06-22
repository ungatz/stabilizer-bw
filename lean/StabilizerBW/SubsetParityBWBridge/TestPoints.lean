import StabilizerBW.SubsetParityBWBridge.Pushforward
import StabilizerBW.SubsetParityBWBridge.Distribution

/-!
# SubsetParityBWBridge — mandated falsification test points

The development pre-registers explicit small-`m` falsification witnesses
(§3, §5).  These are kernel-decided instances of the general headline
`grade_fiber_card` (the operator-side count `8·4^m·C(m,k)`) and
`grade_distribution_BW` (the normalised distribution `C(m,k)/2^m`).
Failure at any single one would refuse the round; all pass.
-/

namespace SubsetParityBWBridge.TestPoints

open SubsetParityBWBridge.Pushforward SubsetParityBWBridge.Distribution

/-! ## Operator-side counts `#{P | gradeOf P = k} = 8·4^m·C(m,k)` -/

example : (Finset.univ.filter (fun P : ReedMuller.LinPhase 2 => ReedMuller.gradeOf P = 0)).card = 128 := by
  rw [grade_fiber_card]; decide
example : (Finset.univ.filter (fun P : ReedMuller.LinPhase 2 => ReedMuller.gradeOf P = 1)).card = 256 := by
  rw [grade_fiber_card]; decide
example : (Finset.univ.filter (fun P : ReedMuller.LinPhase 2 => ReedMuller.gradeOf P = 2)).card = 128 := by
  rw [grade_fiber_card]; decide

example : (Finset.univ.filter (fun P : ReedMuller.LinPhase 3 => ReedMuller.gradeOf P = 0)).card = 512 := by
  rw [grade_fiber_card]; decide
example : (Finset.univ.filter (fun P : ReedMuller.LinPhase 3 => ReedMuller.gradeOf P = 1)).card = 1536 := by
  rw [grade_fiber_card]; decide
example : (Finset.univ.filter (fun P : ReedMuller.LinPhase 3 => ReedMuller.gradeOf P = 2)).card = 1536 := by
  rw [grade_fiber_card]; decide
example : (Finset.univ.filter (fun P : ReedMuller.LinPhase 3 => ReedMuller.gradeOf P = 3)).card = 512 := by
  rw [grade_fiber_card]; decide

/-! ## Normalised-distribution test points `#{…}/8^{m+1} = C(m,k)/2^m` -/

example : ((Finset.univ.filter (fun P : ReedMuller.LinPhase 2 => ReedMuller.gradeOf P = 0)).card : ℚ) / 8 ^ 3
    = (Nat.choose 2 0 : ℚ) / 2 ^ 2 := grade_distribution_BW 0 (by norm_num)
example : ((Finset.univ.filter (fun P : ReedMuller.LinPhase 2 => ReedMuller.gradeOf P = 1)).card : ℚ) / 8 ^ 3
    = (Nat.choose 2 1 : ℚ) / 2 ^ 2 := grade_distribution_BW 1 (by norm_num)
example : ((Finset.univ.filter (fun P : ReedMuller.LinPhase 2 => ReedMuller.gradeOf P = 2)).card : ℚ) / 8 ^ 3
    = (Nat.choose 2 2 : ℚ) / 2 ^ 2 := grade_distribution_BW 2 (by norm_num)
example : ((Finset.univ.filter (fun P : ReedMuller.LinPhase 4 => ReedMuller.gradeOf P = 2)).card : ℚ) / 8 ^ 5
    = (Nat.choose 4 2 : ℚ) / 2 ^ 4 := grade_distribution_BW 2 (by norm_num)
example : ((Finset.univ.filter (fun P : ReedMuller.LinPhase 4 => ReedMuller.gradeOf P = 4)).card : ℚ) / 8 ^ 5
    = (Nat.choose 4 4 : ℚ) / 2 ^ 4 := grade_distribution_BW 4 (by norm_num)

end SubsetParityBWBridge.TestPoints
