import StabilizerBW.T1A.ZpowFacts
import StabilizerBW.T1A.Leaves
import StabilizerBW.T1A.GradeLinear
import StabilizerBW.T1A.GradeEnumerator
import StabilizerBW.T1A.GradeCard
import StabilizerBW.T1A.Tcount2
import StabilizerBW.T1A.RMJoint

/-!
# T1A — Closed-form Barnes–Wall grade enumerator for diagonal Clifford+T

Aggregator for the T1A modules.

* `T1A.ZpowFacts` — per-coefficient `λ`-factorisation in `ℤ[ζ₈]`.
* `T1A.Leaves` — leaf reconstruction and the Möbius factorisation for linear phases.
* `T1A.GradeLinear` — the pure-linear grade equals the per-monomial T-count.
* `T1A.GradeEnumerator` — the Tier-S grade generating function `8·4^m·(1+z)^m`.
* `T1A.GradeCard` — the cardinality (coefficient) form.
* `T1A.Tcount2` — degree-`≤ 2` syntactic T-count enumerator + tCount/grade
  disagreement witness.
* `T1A.RMJoint` — the RM(1, m) bivariate (weight, grade) joint enumerator.
-/
