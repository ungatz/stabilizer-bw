import StabilizerBW.Grade.Kernel.AmbiguityResolution
import StabilizerBW.Grade.Kernel.LiteralKernel
import StabilizerBW.Grade.Kernel.ClosedForm
import StabilizerBW.Grade.Kernel.StratumEquivalence
import StabilizerBW.Grade.Kernel.CrossLinkLayer65Layer76
import StabilizerBW.Grade.Kernel.SelingerAttributionCorrection
import StabilizerBW.Grade.Kernel.AxiomProbe

/-!
# BWGradeKernelClassification — algebraic characterization of `ker(g_n)`

This directory characterizes the kernel of the Barnes–Wall grade homomorphism
`g_n : Cliff+T_n → ℕ` (the `λ`-adic valuation of the down-set Möbius transform,
`Roots.graden`; codomain `ℕ` per the Phase 0.5 audit, not `ℤ/8`).

## Result (Branch A — positive, for the literal kernel)

The literal kernel `bwGradeKernel n = {D | graden n D = 0}` has a finite algebraic
description: it equals the grade-`0` **lattice stabilizer** (Clifford-type sector)
`bwLatticeStabilizer n = {D | gradeLEn n D 0}` — the diagonal operators that already
preserve `BW_n` with no `λ`-adic depth.  This set contains the identity and is closed
under composition, hence is a submonoid (`BWGradeKernelFinitelyPresented`).  It is a
**proper** subset: the maximal `T`-monomial `bwT (n+1)` (grade `2(n+1)−1`) is excluded.

## Result (Branch-B-flavoured — for the stratum reading)

At a fixed non-zero grade the `T`-count is **not** determined: `CS` (`n = 2`) and `CCZ`
(`n = 3`) both have BW grade `2` but published ancilla-free `T`-counts `2` and `7`
(`BWGradeStratumEquivalence`).  So a grade-`g` stratum is not a single `T`-count class.

## Cross-links

* Layer 65 (Jiang–Wang nullity): `CZ` lies in both the BW kernel and the nullity kernel
  (`g = ν = 0`), while `cT` lies in neither (`g = 3`, `ν = 2`).
* Layer 76 (tight roster): the `(CS, CCZ)` pair sits outside the BW kernel.

## Files

* `AmbiguityResolution.lean` (T1): the kernel object and core characterization.
* `LiteralKernel.lean` (T2): kernel = lattice stabilizer; non-triviality; `Mat2` corroboration.
* `ClosedForm.lean` (T3): submonoid closure and `BWGradeKernelFinitelyPresented`.
* `StratumEquivalence.lean` (T4): the grade-`2` stratum carries distinct `T`-counts.
* `CrossLinkLayer65Layer76.lean` (T5): nullity / tight-roster cross-links.
* `SelingerAttributionCorrection.lean` (T6): internal citation corrigendum.
* `AxiomProbe.lean` (T6): the axiom audit.

All results are kernel-checked (`decide` / `rfl` / `omega`); no `sorry`, no `native_decide`,
no custom axioms.
-/
