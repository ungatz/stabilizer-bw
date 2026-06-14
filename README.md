# Stabilizer ↔ Barnes–Wall

A small library of theorems, executable code, and prose that record what
the Barnes–Wall lattices have to do with the stabilizer fragment of
quantum computing. Three layers in one repository:

* a Lean 4 formalisation of every theorem,
* a Haskell companion that runs every construction on concrete data,
* a chapter-by-chapter prose tour that explains the mathematics and
  marks what is in the literature versus what is new here.

The repository is standalone: nothing in the prose cites material outside
this tree.

## Read

Start with [`narrative/00-overview.md`](narrative/00-overview.md) for the
slogan and the table of contents.

| Document | Topic |
|----------|-------|
| [`narrative/00-overview.md`](narrative/00-overview.md) | What is in the repository, what is new, what is in the literature. |
| [`narrative/01-bw-family.md`](narrative/01-bw-family.md) | The Barnes–Wall lattice tower and its free-module decomposition. |
| [`narrative/02-presentation.md`](narrative/02-presentation.md) | The lattice automorphisms are the Clifford group, presented as a prop. |
| [`narrative/03-logical-lattice.md`](narrative/03-logical-lattice.md) | Stabilizer codes as Barnes–Wall lattices at a finer scale. |
| [`narrative/04-prop-computes.md`](narrative/04-prop-computes.md) | The Micciancio–Nicolosi decoder as a recursion scheme. |
| [`narrative/05-pauli-logic.md`](narrative/05-pauli-logic.md) | A sequent calculus for stabilizer entailment; cut elimination as tableau update. |
| [`narrative/06-grade.md`](narrative/06-grade.md) | A $\lambda$-adic grade on Clifford+$T$ operators. |
| [`narrative/07-r11-transport.md`](narrative/07-r11-transport.md) | Direct closure of the Clifford-transport step at $n = 2$ and $n = 3$. |
| [`narrative/references.md`](narrative/references.md) | Literature pointers used in the prose. |

## Build

**Haskell** (the easier of the two). Plain `base + containers`. No package
manager required:
```
cd haskell
ghc -O2 -isrc Main.hs -o stab-bw && ./stab-bw
```
`Main.hs` exercises every module. The expected numerical output is
documented inline.

**Lean 4.** The Lean sources sit in `lean/`, organised by topic. The
files compile against a Lean 4 toolchain with Mathlib; the upstream
project that hosts them sets the exact Lake configuration. See
[`lean/README.md`](lean/README.md) for the file map.

## What's new versus what's in the literature

The split is recorded in each narrative document and summarised in
[`narrative/00-overview.md`](narrative/00-overview.md). At a glance:

* In the literature: the Barnes–Wall lattice and its free-module
  decomposition (Barnes–Wall 1959; Forest et al.\ 2015;
  Kliuchnikov–Schönnenbeck 2024); the Clifford-as-lattice-automorphism
  identification (Kliuchnikov–Schönnenbeck 2024); the bounded-distance
  decoder (Micciancio–Nicolosi 2008); the tableau formalism (Aaronson–
  Gottesman 2004); the standard equational theories of Clifford
  (Selinger 2015; Backens 2014).
* Contributed here: the assembly of these three pictures into a single
  prop (the presentation theorem); the logical-lattice theorem (codes as
  scaled $\mathrm{BW}_{n-m}$); the reading of the decoder as a
  hylomorphism with equivariance as a free theorem; the sequent calculus
  $\mathsf{PL}_n$ with cut elimination as tableau reduction; the
  $\lambda$-adic grade with its closed-form upper bound and certified
  $T$-count lower bound; the direct closure of the transport step at the
  headline cases $n = 2$ and $n = 3$.

## Directory layout

```
stabilizer-barnes-wall/
├── README.md             (this file)
├── LICENSE
├── haskell/
│   ├── README.md
│   ├── Main.hs           (demo battery)
│   └── src/
│       ├── GaussianInt.hs
│       ├── BW.hs
│       ├── Prop.hs
│       ├── Decoder.hs
│       ├── Fidelity.hs
│       ├── PauliLogic.hs
│       ├── Cyclotomic.hs
│       ├── Grade.hs
│       └── Transport.hs
├── lean/
│   ├── README.md
│   ├── BarnesWall/
│   ├── Stabilizer/
│   ├── LogicalLatticeTransport/
│   ├── Decoder/
│   ├── PauliLogic/
│   └── Arithmetic/Roots/
└── narrative/
    ├── 00-overview.md
    ├── 01-bw-family.md
    ├── 02-presentation.md
    ├── 03-logical-lattice.md
    ├── 04-prop-computes.md
    ├── 05-pauli-logic.md
    ├── 06-grade.md
    ├── 07-r11-transport.md
    └── references.md
```

## Acknowledgments

Parts of this work were assisted by Aristotle (Harmonic) and Claude
(Anthropic).

## Licence

Released under the Apache Licence 2.0 (see [`LICENSE`](LICENSE)).
