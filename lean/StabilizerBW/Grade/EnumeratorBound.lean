import StabilizerBW.Grade.EnumeratorBound.CliffordMenuAllN
import StabilizerBW.Grade.EnumeratorBound.GradeEnumeratorAllN
import StabilizerBW.Grade.EnumeratorBound.BandwidthScalingAllN
import StabilizerBW.Grade.EnumeratorBound.MagicConserved
import StabilizerBW.Grade.EnumeratorBound.Summary
import StabilizerBW.Grade.EnumeratorBound.AxiomProbe

/-!
# MenuBandwidthAllN — closed-form bandwidth scaling for all `n`

Aggregator for the all-`n` bandwidth-scaling development (the original was
`MenuBandwidthAllN-r1`).  It lifts the n=4 closed-form bandwidth scaling of
`StabilizerBW.MenuBandwidthN4` to **all** `n ≥ 2`, using the menu facet ↔
bandwidth bridge of `MenuBridge`.

## Contents

* `MenuBandwidthAllN.CliffordMenuAllN` (T1) — the `n`-qubit Clifford menu (`3n`
  single-qubit Pauli observables), the proved stabilizer facet bound `W ≤ n`, and
  the all-ones facet `cliffordFacetN` (`S = 3n`, `N = 6n`).
* `MenuBandwidthAllN.GradeEnumeratorAllN` (T2) — the closed-form grade-enumerator
  bound `6n + 2g`, with the all-ones instance discharged unconditionally.
* `MenuBandwidthAllN.BandwidthScalingAllN` (T3) — the headline closed-form
  bandwidth scaling `gap ≥ V / (12 n)` at all `n`.
* `MenuBandwidthAllN.MagicConserved` (T4) — the per-qubit-conserved magic-state gap
  `(√3 − 1)/6`, independent of `n`.
  instances and the Layer 13 / Layer 68 values.
* `MenuBandwidthAllN.Summary` (T6) — the single combined all-`n` statement.
* `MenuBandwidthAllN.AxiomProbe` (T7) — the kernel-axiom audit.
-/
