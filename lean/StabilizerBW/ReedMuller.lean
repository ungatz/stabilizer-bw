import StabilizerBW.ReedMuller.ZpowFacts
import StabilizerBW.ReedMuller.Leaves
import StabilizerBW.ReedMuller.GradeLinear
import StabilizerBW.ReedMuller.GradeEnumerator
import StabilizerBW.ReedMuller.GradeCard
import StabilizerBW.ReedMuller.Tcount2
import StabilizerBW.ReedMuller.RMJoint

/-!
# ReedMuller — Closed-form Barnes–Wall grade enumerator for diagonal Clifford+T

Aggregator for the ReedMuller modules.

* `ReedMuller.ZpowFacts` — per-coefficient `λ`-factorisation in `ℤ[ζ₈]`.
* `ReedMuller.Leaves` — leaf reconstruction and the Möbius factorisation for linear phases.
* `ReedMuller.GradeLinear` — the pure-linear grade equals the per-monomial T-count.
* `ReedMuller.GradeEnumerator` — the Tier-S grade generating function `8·4^m·(1+z)^m`.
* `ReedMuller.GradeCard` — the cardinality (coefficient) form.
* `ReedMuller.Tcount2` — degree-`≤ 2` syntactic T-count enumerator + tCount/grade
  disagreement witness.
* `ReedMuller.RMJoint` — the RM(1, m) bivariate (weight, grade) joint enumerator.
-/
