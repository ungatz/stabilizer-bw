import StabilizerBW.Grade.Catalyst.CarrierProp

/-!
# CHKRS S13 — generator baseline

The generator part of the carrier `CompositeS13Discharge.gen` is discharged unconditionally
from the corpus's `Pi3.grade2_toPi2_gen_eq` (the corrected rule `Γ(g) = g` on generators).
-/

namespace CatalystGrade

open Pi3 SqWord

/-- **Generator-level discharge.** On each of the four single-qubit generators `X, V, S, T`
the catalytic embedding satisfies the literal inequality `grade₂(Φ₃ g) ≤ grade₃ g`.  Indeed
equality holds (`Pi3.grade2_toPi2_gen_eq`); we record the inequality form needed by the carrier. -/
theorem gen_discharged :
    Pi2.grade2 (toPi2 .xg) ≤ grade2obj (toPi3 .xg) ∧
    Pi2.grade2 (toPi2 .vg) ≤ grade2obj (toPi3 .vg) ∧
    Pi2.grade2 (toPi2 .sg) ≤ grade2obj (toPi3 .sg) ∧
    Pi2.grade2 (toPi2 .tg) ≤ grade2obj (toPi3 .tg) := by
  obtain ⟨h1, h2, h3, h4⟩ := Pi3.grade2_toPi2_gen_eq
  exact ⟨h1.le, h2.le, h3.le, h4.le⟩

end CatalystGrade
