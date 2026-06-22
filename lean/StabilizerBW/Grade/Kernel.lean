import StabilizerBW.Grade.Kernel.AmbiguityResolution
import StabilizerBW.Grade.Kernel.LiteralKernel
import StabilizerBW.Grade.Kernel.ClosedForm
import StabilizerBW.Grade.Kernel.StratumEquivalence
import StabilizerBW.Grade.Kernel.CrossLinkLayer65Layer76
import StabilizerBW.Grade.Kernel.SelingerAttributionCorrection
import StabilizerBW.Grade.Kernel.AxiomProbe

/-!
# KernelClassification — algebraic characterization of `ker(g_n)`

This directory characterizes the kernel of the Barnes–Wall grade homomorphism
`g_n : Cliff+T_n → ℕ` (the `λ`-adic valuation of the down-set Möbius transform,
`Roots.graden`; codomain `ℕ` per the the audit step, not `ℤ/8`).

## Result (positive, for the literal kernel)

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

* the development (Jiang–Wang nullity): `CZ` lies in both the BW kernel and the nullity kernel
  (`g = ν = 0`), while `cT` lies in neither (`g = 3`, `ν = 2`).
* the development (tight roster): the `(CS, CCZ)` pair sits outside the BW kernel.

## Files

* `AmbiguityResolution.lean` : the kernel object and core characterization.
* `LiteralKernel.lean` : kernel = lattice stabilizer; non-triviality; `Mat2` corroboration.
* `ClosedForm.lean` : submonoid closure and `BWGradeKernelFinitelyPresented`.
* `StratumEquivalence.lean` : the grade-`2` stratum carries distinct `T`-counts.
* `CrossLinkLayer65Layer76.lean` : nullity / tight-roster cross-links.
* `SelingerAttributionCorrection.lean` : internal citation corrigendum.
* `AxiomProbe.lean` : the axiom audit.

All results are kernel-checked (`decide` / `rfl` / `omega`); no `sorry`, no `native_decide`,
no custom axioms.
-/
