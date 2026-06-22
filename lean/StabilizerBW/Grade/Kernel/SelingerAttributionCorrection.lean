/-!
# T6 — Selinger 2013 attribution corrigendum (internal note)

This file records, as an internal corrigendum surfaced by the Phase 0.5 audit, a citation
correction for the corpus's `T`-count attributions.  It does **not** modify the
standardStabilizerBW.Grade.TightWitnesses.`Roster.lean`; it only documents the
correction for a separate corpus pass.

## The correction

* **Selinger, P. (2013), "Quantum circuits of T-depth one", Phys. Rev. A 87, 042302
  (arXiv:1210.0974)** is the **`T`-DEPTH-one** analysis paper.  It is *not* the source for
  ancilla-free **`T`-COUNT** values.

* The correct attribution for the ancilla-free `T`-counts of the multiply-controlled
  diagonal gates is **Amy, M.; Maslov, D.; Mosca, M.; Roetteler, M. (2013), "A
  meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits",
  IEEE TCAD 32(6):818–830, Table I** (abbreviated AMMR 2013).  In particular the
  ancilla-free `T`-count `T(CCZ) = 7` (Toffoli class) is AMMR 2013, Table I.

* The pre-existing chapter convention that attributes single-qubit and singly-controlled `T`-count
  values (e.g. `T(CS) = 2`, `T(cT) = 3`) to "Selinger 2013" should be read as the
  meet-in-the-middle / optimal-synthesis literature (AMMR 2013); Selinger 2013 governs the
  `T`-depth analysis, not the `T`-count.

This corrigendum is internal: the operative roster constants are unchanged, and downstream
theorems are unaffected.
-/

namespace BWGradeKernelClassification.SelingerAttributionCorrection

/-- No-op carrier for the Selinger 2013 attribution corrigendum (see module docstring).
The correction is documentary; it changes no operative constant. -/
theorem selinger_attribution_corrigendum : True := trivial

end BWGradeKernelClassification.SelingerAttributionCorrection
