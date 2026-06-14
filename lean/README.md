# Lean sources

Lean 4 formalisations of every theorem stated in
[`../narrative/`](../narrative/). The files are organised by topic.

## Files

```
lean/
├── BarnesWall/
│   ├── BarnesWall.lean            (single-qubit lattice, Clifford-orbit enumeration)
│   └── BWFreeModule.lean          (free-module decomposition; uniqueness; pinned; Bell theory)
├── Stabilizer/
│   └── Stab2CHSHBridge.lean       (stabilizer / CHSH bridge at n = 2)
├── LogicalLatticeTransport/
│   ├── LogicalLatticeTransport.lean
│   ├── BW2Transport.lean          (the eleven n = 2 Clifford generators preserve BW_2)
│   └── BW3Transport.lean          (the fourteen n = 3 generators preserve BW_3)
├── Decoder/
│   ├── DecoderN1.lean             (base case)
│   ├── DecoderTheorems.lean       (the four-candidate reconciliation)
│   ├── DecoderThreshold.lean      (the bounded-distance threshold)
│   ├── DecoderUniqueness.lean     (uniqueness inside the promise)
│   ├── DecoderFidelity.lean       (fidelity via decoding)
│   └── DecoderLogical.lean        (logical decoding corollary)
├── PauliLogic/
│   ├── Syntax.lean                (Pauli words, sequents, derivations)
│   ├── Rules.lean                 (Ax, Mul, UnitI, Cut)
│   ├── Soundness.lean             (every derivable literal is valid)
│   ├── Tableau.lean               (the tableau-step correspondence)
│   └── CutElimination.lean        (normalize as a total recursive function)
└── Arithmetic/
    └── Roots/
        ├── Z8.lean                (Z[zeta_8] arithmetic and the prime lambda)
        ├── Z16.lean               (the level-raising identity)
        ├── Matrices.lean          (single-qubit grade; grade_mul; grade_eq_zero_iff)
        ├── E3.lean                (the four square roots of X against the four primitive eighth roots)
        ├── BW2.lean               (BW_2 with decidable membership; diagonal grade table)
        ├── BW3.lean               (kernel-verified BW_3 grades; CCZ = 2, CCS = 4, ccT = 5)
        ├── BW4.lean               (kernel-verified BW_4 grades; CCCS = 6, cccT = 7)
        ├── BWn.lean               (general-n Barnes–Wall infrastructure)
        ├── Tensor.lean            (tensor subadditivity; disjoint-support additivity)
        ├── UpperBoundAllN.lean    (max(0, 2|S| - 2^nu_2(c)) at every n)
        ├── LowerBoundAllN.lean    (maximal-monomial lower bound at every n)
        ├── StrictSubsetLowerBoundAllN.lean
        ├── MultimonomialClosedForm.lean
        ├── MoebiusClosedFormAllN.lean
        └── CrossLevelSelfSimilarity.lean
```

## How they fit together

A reader who opens any file should be able to navigate from there:

* `BarnesWall.lean` and `BWFreeModule.lean` set up the lattice tower and
  the free-module decomposition. Everything else depends on them.
* `LogicalLatticeTransport/` closes the Clifford-transport step of the
  logical-lattice theorem at the two headline cases (see
  [`../narrative/07-r11-transport.md`](../narrative/07-r11-transport.md)).
* `Decoder/` formalises the Micciancio–Nicolosi decoder and its
  contracts; `DecoderLogical.lean` is the logical-decoding corollary
  that consumes the logical-lattice theorem.
* `PauliLogic/` is the sequent calculus and its cut-elimination
  theorem; `Tableau.lean` cashes cut elimination as Aaronson–Gottesman
  row reduction.
* `Arithmetic/Roots/` is the $\lambda$-adic grade infrastructure
  (single-qubit, BW₂, BW₃, BW₄, general $n$, closed forms,
  refutations).
* `Stabilizer/Stab2CHSHBridge.lean` is the $n = 2$ stabilizer / CHSH
  bridge, used by downstream operational consequences of the lattice
  structure.

## Hygiene

Every theorem is proved without `sorry`. The transitive axioms used
are restricted to the standard ones: `propext`, `Classical.choice`,
`Quot.sound`. A small number of finite-group enumerations in
`BarnesWall.lean` and `Stab2CHSHBridge.lean` use Lean's `native_decide`
tactic; this is documented in those files and is justified by the
finiteness of the search space (the 24-element single-qubit Clifford
group; the $|CHSH| \le 2$ bound on every valid stabilizer tableau).
No other unsafe tactic is used. Adjacent files contain pre-existing
unverified theorems unrelated to the developments here; those are
documented separately in their own modules.

## Reading suggestions

The pairing between Lean files and narrative documents is one-to-one
where it makes sense to be:

* [`../narrative/01-bw-family.md`](../narrative/01-bw-family.md)
  ↔ `BarnesWall/`.
* [`../narrative/03-logical-lattice.md`](../narrative/03-logical-lattice.md)
  ↔ `BarnesWall/BWFreeModule.lean` (pinned case) and
  `LogicalLatticeTransport/` (transport step).
* [`../narrative/04-prop-computes.md`](../narrative/04-prop-computes.md)
  ↔ `Decoder/`.
* [`../narrative/05-pauli-logic.md`](../narrative/05-pauli-logic.md)
  ↔ `PauliLogic/`.
* [`../narrative/06-grade.md`](../narrative/06-grade.md)
  ↔ `Arithmetic/Roots/`.
* [`../narrative/07-r11-transport.md`](../narrative/07-r11-transport.md)
  ↔ `LogicalLatticeTransport/`.
