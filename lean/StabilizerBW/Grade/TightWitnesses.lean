import StabilizerBW.Grade.TightWitnesses.Roster
import StabilizerBW.Grade.TightWitnesses.Tight
import StabilizerBW.Grade.TightWitnesses.Loose
import StabilizerBW.Grade.TightWitnesses.Summary
import StabilizerBW.Grade.TightWitnesses.TightGradeCarrier
import StabilizerBW.Grade.TightWitnesses.NonTautology
import StabilizerBW.Grade.TightWitnesses.AxiomProbe

/-!
# BWGradeTightWitnesses — the BW grade equals the Selinger-optimal ancilla-free T-count on a
roster of concrete Clifford+T gates

This directory closes the chapter's "where the grade is tight" promise: on a roster of
concrete small-`n` Clifford+T gates it certifies the relationship between the kernel-checked
Barnes–Wall grade `g_n(D)` and the **published ancilla-free T-count** `T_opt(D)`.

## Roster and results

| Gate              | BW grade | published T-count | relation        | source        |
|-------------------|----------|-------------------|-----------------|---------------|
| `T`   at `n = 1`  | `1`      | `1`               | `g = T_opt`     | Selinger 2013 |
| `CS`  at `n = 2`  | `2`      | `2`               | `g = T_opt`     | Selinger 2013 |
| `cT`  at `n = 2`  | `3`      | `3`               | `g = T_opt`     | Selinger 2013 |
| `CCZ` at `n = 3`  | `2`      | `7`               | `g < T_opt`     | AMMM 2013     |
| `CCS` at `n = 3`  | `4`      | `7`               | `g < T_opt`     | AMMM 2013     |
| `ccT` at `n = 3`  | `5`      | `7`               | `g < T_opt`     | AMMM 2013     |

## Files

* `Roster.lean` (T1): the `SmallGate` inductive and `selingerTOpt`/`selingerTOptRef` with
  citation strings.
* `Tight.lean` (T2): the tightness theorems `g = T_opt` for `T`, `CS`, `cT`.
* `Loose.lean` (T3): the strict-looseness theorems `g < T_opt` for `CCZ`, `CCS`, `ccT`.
* `Summary.lean` (T4): the unified roster table.
* `TightGradeCarrier.lean` (T5): the `TightGrade` structure plus the concrete certificates
  `T_TightGrade`, `CS_TightGrade`, `cT_TightGrade`.
* `NonTautology.lean` (T6): the non-vacuity certificate — the literature T-counts are
  positive, are the published constants, and are independent of the grades.
* `AxiomProbe.lean` (T7): the axiom audit.

Everything is kernel-checked (`decide` / `rfl`); **no `native_decide`** is used.  The
grade values are imported from the corpus (`Roots.grade_T`, `Roots.grade2_CS`,
`Roots.grade2_cT`, `Roots.grade3_CCZ`, `Roots.grade3_CCS`, `Roots.grade3_ccT`); the
T-counts are independently sourced literature constants (Selinger 2013 Thm 6.2 / §6.2;
Amy–Maslov–Mosca–Roetteler 2013 Table I).
-/
