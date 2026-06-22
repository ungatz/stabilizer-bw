import StabilizerBW.Grade.EnumeratorBound.CliffordMenuAllN
import StabilizerBW.Grade.EnumeratorBound.BandwidthScalingAllN
import StabilizerBW.Grade.EnumeratorBound.MagicConserved

/-!
# BandwidthScaling / Summary — the combined all-`n` statement

A single statement combining the all-`n` closed-form bandwidth scaling and the
per-qubit-conserved magic-state gap.
-/

open scoped BigOperators

namespace BandwidthScaling

/-- **T6: the all-`n` bandwidth headline.**  For every `n ≥ 2`, at the `n`-qubit
all-ones Clifford menu:

1. the bandwidth gap obeys the closed-form scaling `gap ≥ V / (12 n)` on every
   profile with nonnegative violation, and
2. the bandwidth gap on the `n`-qubit Bloch magic state is the per-qubit-conserved
   constant `(√3 − 1)/6`, independent of `n`. -/
theorem bandwidth_allN_summary (n : ℕ) (hn : 2 ≤ n) :
    (∀ E : Fin (3 * n) → ℝ, 0 ≤ (cliffordFacetN n).violation E →
        (cliffordFacetN n).violation E / (12 * n) ≤ facetGap (cliffordFacetN n) E)
      ∧ facetGap (cliffordFacetN n) (magicProfileN n) = (Real.sqrt 3 - 1) / 6 := by
  refine ⟨fun E hV => bandwidth_scaling_allN n hn E hV, magic_gap_conserved_allN n hn⟩

end BandwidthScaling
