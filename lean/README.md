# Lean sources

Lean 4 formalisations of the theorems stated in [`../narrative/`](../narrative/).
Everything sits under one namespace, `StabilizerBW`, mirroring the file layout.

```
lean/
└── StabilizerBW/
    ├── BarnesWall.lean                  single-qubit lattice, Clifford-orbit enumeration
    ├── BWFreeModule.lean                free-module decomposition; pinned; Bell theory
    ├── Stab2CHSHBridge.lean             stabilizer / CHSH bridge at n = 2
    ├── LogicalLatticeTransport.lean
    ├── LogicalLatticeTransport/
    │   ├── BW2Transport.lean            n = 2 Clifford generators preserve BW₂
    │   └── BW3Transport.lean            n = 3 Clifford generators preserve BW₃
    ├── DecoderN1.lean                   base case n = 1
    ├── DecoderTheorems.lean             aggregator + axiom audit
    ├── DecoderThreshold.lean            bounded-distance threshold
    ├── DecoderUniqueness.lean           uniqueness inside the promise
    ├── DecoderFidelity.lean             fidelity via decoding
    ├── DecoderLogical.lean              logical-decoding corollary
    ├── PauliLogic/
    │   ├── Syntax.lean                  signed Pauli words; symplectic representation
    │   ├── Rules.lean                   Ax, Mul, UnitI, Cut
    │   ├── Soundness.lean               every derivable literal is valid
    │   ├── Tableau.lean                 tableau-step correspondence
    │   ├── CutElimination.lean          cut elimination as a total recursive function
    │   ├── Completeness.lean            converse to soundness via a trace identity
    │   └── Categorical/                 dagger compact closed semantics
    │       ├── Dagger.lean
    │       ├── DaggerMonoidal.lean
    │       ├── DaggerCompact.lean
    │       ├── PLnCategory.lean         Cat_PL_n + the symplectic strictification
    │       ├── Interpret.lean           interpretation functor into Stab_n
    │       ├── Universality.lean        Selinger-2011-shape universality
    │       └── ZXComparison.lean        Backens-2014 comparison statement
    ├── Roots/
    │   ├── Core.lean                    Z[ζ₈] arithmetic
    │   ├── Matrices.lean                2 × 2 matrices over Z[ζ₈]
    │   ├── Lattice.lean                 L₃ membership predicate
    │   ├── Adjoint.lean
    │   ├── Grades.lean                  the λ-adic grade
    │   ├── Filtration.lean
    │   ├── BWModel.lean                 self-contained computable model
    │   ├── Zeta16.lean
    │   ├── BW2.lean                     n = 2 diagonal table
    │   ├── BW3.lean                     n = 3 grades
    │   ├── BW4.lean                     n = 4 grades
    │   ├── BWn.lean                     all-n lattice recursion
    │   ├── Tensor.lean
    │   ├── LinearBound.lean
    │   ├── Level4.lean
    │   ├── UpperBoundAllN.lean          all-n upper bound 2d − 2^ν
    │   ├── LowerBoundAllN.lean          maximal-monomial lower bound at every ν
    │   ├── StrictSubsetLowerBoundAllN.lean   strict-subset lower bound, all n
    │   ├── MultimonomialClosedForm.lean
    │   ├── CrossLevelSelfSimilarity.lean
    │   ├── E3.lean
    │   ├── Z8Valuation.lean
    │   ├── MoebiusClosedFormAllN.lean
    │   ├── MoebiusGradeAllN.lean
    │   ├── MoebiusGradeClosedFormAllN.lean
    │   ├── AutL3Unitary.lean            unitary Aut(L₃) at one qubit, integral over Z[ζ₈]
    │   └── AutL3HalfSqrt2.lean          order 8 → 24 under denominator change
    ├── T1A/
    │   ├── ZpowFacts.lean
    │   ├── Leaves.lean
    │   ├── GradeLinear.lean             grade = T-count on linear phases
    │   ├── GradeEnumerator.lean         G_m(z) = 8·4^m·(1+z)^m
    │   ├── GradeCard.lean
    │   ├── Tcount2.lean                 degree-≤ 2 enumerator + grade/T-count gap
    │   └── RMJoint.lean                 RM(1, m) bivariate (weight, grade) enumerator
    └── BWCss/
        ├── ReedMuller.lean              binary Reed–Muller theory
        ├── CSS.lean                     CSS code data + Reed–Muller-pair member
        ├── Grade.lean                   grade-refined logical-operator enumerator
        └── BWCssParameters.lean         entry point + headline parameter table
```

## How they fit together

A reader who opens any file should be able to navigate from there:

* `BarnesWall.lean` and `BWFreeModule.lean` set up the lattice tower and the
  free-module decomposition; everything else depends on them.
* `LogicalLatticeTransport/` closes the Clifford-transport step of the
  logical-lattice theorem at the two headline cases.
* `Decoder*.lean` formalises the Micciancio–Nicolosi decoder and its
  contracts; `DecoderLogical.lean` is the logical-decoding corollary that
  consumes the logical-lattice theorem.
* `PauliLogic/` is the sequent calculus, its cut-elimination theorem (cashed
  out as Aaronson–Gottesman row reduction by `Tableau.lean`), its
  trace-identity completeness in `Completeness.lean`, and the dagger compact
  closed categorical reading in `Categorical/`.
* `Roots/` is the λ-adic grade infrastructure: single-qubit, BW₂–BW₄, general
  *n*, multi-monomial Möbius closed form, and the one-qubit unitary
  Kliuchnikov–Schönnenbeck converse.
* `T1A/` and `BWCss/` recover the same closed-form grade enumerator for
  linear phases from two independent paths — the Barnes–Wall λ-adic grade and
  a Reed–Muller-based CSS construction.
* `Stab2CHSHBridge.lean` is the *n* = 2 stabilizer / CHSH bridge.

## Hygiene

Every theorem is proved without `sorry`. The transitive axioms used are
restricted to the standard ones (`propext`, `Classical.choice`, `Quot.sound`),
with a few finite-group enumerations in `BarnesWall.lean` and
`Stab2CHSHBridge.lean` using Lean's `native_decide` tactic, documented in
those files and justified by the finiteness of the search space (the
24-element single-qubit Clifford group; the $|\mathrm{CHSH}| \le 2$ bound on
every valid stabilizer tableau).

## Reading suggestions

The pairing between Lean files and narrative documents is one-to-one where
it makes sense to be:

* [`../narrative/01-bw-family.md`](../narrative/01-bw-family.md) ↔
  `BarnesWall.lean`, `BWFreeModule.lean`
* [`../narrative/02-presentation.md`](../narrative/02-presentation.md) ↔
  `BarnesWall.lean`, `Roots/AutL3Unitary.lean`, `Roots/AutL3HalfSqrt2.lean`
* [`../narrative/03-logical-lattice.md`](../narrative/03-logical-lattice.md) ↔
  `BWFreeModule.lean` (pinned case) and `LogicalLatticeTransport/` (transport step)
* [`../narrative/04-prop-computes.md`](../narrative/04-prop-computes.md) ↔
  the decoder modules
* [`../narrative/05-pauli-logic.md`](../narrative/05-pauli-logic.md) ↔
  `PauliLogic/`
* [`../narrative/06-grade.md`](../narrative/06-grade.md) ↔ `Roots/`, `T1A/`,
  `BWCss/`
* [`../narrative/07-transport.md`](../narrative/07-transport.md) ↔
  `LogicalLatticeTransport/`

## Building

These sources were closed against Mathlib v4.28.0 (Lean toolchain
`leanprover/lean4:v4.28.0`).  To check them, point Lake at that Mathlib
revision; individual files reflect the API of that snapshot.
