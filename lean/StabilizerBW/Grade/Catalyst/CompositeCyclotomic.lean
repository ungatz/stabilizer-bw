import StabilizerBW.Grade.Catalyst.CarrierProp

/-!
# CHKRS S13 — the composite step

The composite step is the genuinely-deep ingredient (the catalyst-identity content of
CHKRS S13).  It is carried by the `composite` field of `CompositeS13Discharge`.  The lemma
below exposes it in the inductive-hypothesis shape used by the headline discharge.

The corpus diagnosis (`Pi3.Headline_T3_general`) explains why a *naive* induction cannot
supply this step unconditionally: the lattice grade is only subadditive under composition,
so `grade₂(Φ₃(a ⊚ b)) ≤ grade₂(Φ₃ a) + grade₂(Φ₃ b) ≤ grade₃ a + grade₃ b` does **not**
collapse to `grade₃(a ⊚ b)` (which is `≤`, not `=`, the sum).  The genuine content of the
step is therefore conditioned on the carrier.
-/

namespace CatalystGrade

open Pi3 SqWord

/-- **The composite-level step.** Given the carrier and the inequality on the two sub-words
`a`, `b`, the inequality lifts to the composite `comp a b`. -/
theorem composite_step (h : CompositeS13Discharge) (a b : SqWord)
    (iha : Pi2.grade2 (toPi2 a) ≤ grade2obj (toPi3 a))
    (ihb : Pi2.grade2 (toPi2 b) ≤ grade2obj (toPi3 b)) :
    Pi2.grade2 (toPi2 (.comp a b)) ≤ grade2obj (toPi3 (.comp a b)) :=
  h.composite a b iha ihb

end CatalystGrade
