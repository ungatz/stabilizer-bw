import StabilizerBW.Grade.Catalyst.Headline

/-!
# CHKRS S13 — falsification branch

If a single witness word `w₀` violates the literal inequality, then the carrier
`CompositeS13Discharge` is provably false (and CHKRS Conjecture S13 is refuted in the
level-3 composite case).  This is the kernel-checked structural reduction; it is
**sorry-free**.  No such witness is supplied here — the hypothesis is left open so that the
lemma is a genuine refutation hook rather than a refutation.
-/

namespace CHKRS_S13_CompositeCatalystGrade

open Pi3 SqWord

/-- **Falsification hook.** A counterexample word `w₀` with
`grade₃ w₀ < grade₂(Φ₃ w₀)` makes the carrier `CompositeS13Discharge` false. -/
theorem composite_S13_refuted_of_witness (w₀ : SqWord)
    (h_counterex : grade2obj (toPi3 w₀) < Pi2.grade2 (toPi2 w₀)) :
    ¬ CompositeS13Discharge := by
  intro h_discharge
  exact absurd (phi3_composite_grade_le_discharged h_discharge w₀) (not_le.mpr h_counterex)

end CHKRS_S13_CompositeCatalystGrade
