import StabilizerBW.Grade.EnumeratorBound.CliffordMenuAllN
import StabilizerBW.Grade.EnumeratorBound.GradeEnumeratorAllN
import StabilizerBW.Grade.EnumeratorBound.BandwidthScalingAllN
import StabilizerBW.Grade.EnumeratorBound.MagicConserved
import StabilizerBW.Grade.EnumeratorBound.Summary
import StabilizerBW.Grade.EnumeratorBound.AxiomProbe

/-!
# BandwidthScaling — closed-form bandwidth scaling for all `n`

Aggregator for the all-`n` bandwidth-scaling development (the original was
`BandwidthScaling`).  It lifts the n=4 closed-form bandwidth scaling of
`StabilizerBW.BandwidthN4` to **all** `n ≥ 2`, using the menu facet ↔
bandwidth bridge of `MenuBridge`.

## Contents

* `BandwidthScaling.CliffordMenuAllN` — the `n`-qubit Clifford menu (`3n`
  single-qubit Pauli observables), the proved stabilizer facet bound `W ≤ n`, and
  the all-ones facet `cliffordFacetN` (`S = 3n`, `N = 6n`).
* `BandwidthScaling.GradeEnumeratorAllN` — the closed-form grade-enumerator
  bound `6n + 2g`, with the all-ones instance discharged unconditionally.
* `BandwidthScaling.BandwidthScalingAllN` — the headline closed-form
  bandwidth scaling `gap ≥ V / (12 n)` at all `n`.
* `BandwidthScaling.MagicConserved` — the per-qubit-conserved magic-state gap
  `(√3 − 1)/6`, independent of `n`.
  instances and the development values.
* `BandwidthScaling.Summary` — the single combined all-`n` statement.
* `BandwidthScaling.AxiomProbe` — the kernel-axiom audit.
-/
