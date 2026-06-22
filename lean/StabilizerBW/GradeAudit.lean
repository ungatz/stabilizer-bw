import StabilizerBW.GradeAudit.CircuitGrade
import StabilizerBW.GradeAudit.QFT
import StabilizerBW.GradeAudit.Shor
import StabilizerBW.GradeAudit.Grover
import StabilizerBW.GradeAudit.Comparison
import StabilizerBW.GradeAudit.Trotter

/-!
# GradeAudit — a Barnes–Wall λ-adic grade audit of standard quantum algorithms (the corrected)

Aggregator for the corrected gate-level grade audit.  Relative to the original, two
substantive math errors are fixed:

1. **Grade convention (Option A, strict Clifford+T basis).**  The gate inductive
   is exactly `{H, S, T, CNOT}`, on which the chapter's Barnes–Wall λ-adic grade
   and the per-gate `T`-count coincide (`g(H)=g(S)=g(CNOT)=0`, `g(T)=1`).  No
   controlled-rotation gate is assigned a fabricated closed-form grade; non-Clifford
   rotations are modelled by their honest Clifford+T syntheses.

2. **Jiang–Wang / Beverland bounds (Option α, honest named-Prop carries).**  The
   cited **unitary** stabilizer-nullity `ν(U) = 2n − log₂|U·Pₙ·U† ∩ Pₙ|` is carried
   as explicit data (with a genuine unitarity proof and the cited bound as a carried
   hypothesis).  No hardcoded `0` and no `Nat.zero_le` tautologies; the comparison
   theorems dominate the genuine (possibly positive) invariant.

Contents:

* `CircuitGrade` — the circuit-side λ-adic grade `circuitGrade` (= `T`-count);
* `QFT` — the approximate `AQFT_n^ε` grade `tPerRot · n(n-1)/2 = Θ(n² log 1/ε)`;
* `Shor` — the CDKM/Toffoli modular-arithmetic grade `tPerToff · toffCount`
  (`Θ(n³)` for the schoolbook construction);
* `Grover` — the AND-of-bits oracle grade `tPerToff · (n-1) = Θ(n)`;
* `Trotter` — the dyadic Heisenberg step grade `3 · tPerRot · (L-1) = Θ(L)`;
* `Comparison` — the substantive head-to-head theorems against the carried
  Jiang–Wang and Beverland unitary-nullity bounds.
-/
