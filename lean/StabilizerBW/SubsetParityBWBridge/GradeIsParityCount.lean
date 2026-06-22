import StabilizerBW.SubsetParityBWBridge.TauMap

/-!
# SubsetParityBWBridge — T3: the Barnes–Wall grade is the parity-count

The Barnes–Wall grade of a linear phase polynomial equals the number of `true`
coordinates of its parity tag: `gradeOf P = #{i | τ P i}`.  This is the
operator-side ↔ measurement-side dictionary entry that makes the grade
distribution and the parity-count distribution literally the same object.
-/

namespace SubsetParityBWBridge.GradeIsParityCount

open Finset SubsetParityBWBridge.ParityBit SubsetParityBWBridge.TauMap

/-- **T3 headline.** The Barnes–Wall grade equals the number of odd parity
coordinates of the tag `τ P`. -/
theorem gradeOf_eq_tau_countOnes {m : ℕ} (P : ReedMuller.LinPhase m) :
    ReedMuller.gradeOf P = (Finset.univ.filter (fun i => tau P i = true)).card := by
  rw [ReedMuller.gradeOf_eq_tCount]
  unfold ReedMuller.tCountLin
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  unfold tau ReedMuller.oddIndic parityBit
  by_cases h : (P.2 i).val % 2 = 1 <;> simp [h]

end SubsetParityBWBridge.GradeIsParityCount
