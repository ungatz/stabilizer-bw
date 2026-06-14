# Stabilizer ↔ Barnes–Wall

A repository of theorems, executable code, and prose about what the Barnes–Wall lattices have to do with the stabilizer fragment of quantum computing.

The short version. Take the Gaussian integers $\mathbb{Z}[i]$ with the single prime $\varphi = 1 + i$ above two, and build a tower of free modules $\mathrm{BW}_0 \subset \mathrm{BW}_1 \subset \mathrm{BW}_2 \subset \dots$ by tensoring a small $2 \times 2$ basis matrix. A unitary on $n$ qubits preserves $\mathrm{BW}_n$ if and only if it is a Clifford operator times a phase (Kliuchnikov–Schönnenbeck, 2024). Once you know that, the rest of the theory becomes arithmetic, and the right way to read it is as a *prop* — a strict symmetric monoidal category whose objects are natural numbers and whose tensor is concatenation. Stabilizer codes are Barnes–Wall lattices at a finer scale, the Micciancio–Nicolosi decoder is a recursion scheme on the lattice's coordinate trees, and the Aaronson–Gottesman tableau update is the cut-elimination algorithm of a small sequent calculus over signed Pauli words.

## Where to start

Read [`narrative/00-overview.md`](narrative/00-overview.md) first. It is a single page that lists the seven main results and points to the document for each.

| Document | Topic |
|---|---|
| [`narrative/00-overview.md`](narrative/00-overview.md) | Slogan, results, what's new versus what's borrowed |
| [`narrative/01-bw-family.md`](narrative/01-bw-family.md) | The lattice tower and the free-module decomposition |
| [`narrative/02-presentation.md`](narrative/02-presentation.md) | Lattice automorphisms are the Clifford group, presented as a prop |
| [`narrative/03-logical-lattice.md`](narrative/03-logical-lattice.md) | Stabilizer codes as Barnes–Wall lattices at a finer scale |
| [`narrative/04-prop-computes.md`](narrative/04-prop-computes.md) | The Micciancio–Nicolosi decoder as a recursion scheme |
| [`narrative/05-pauli-logic.md`](narrative/05-pauli-logic.md) | A sequent calculus for stabilizer entailment; cut elimination as tableau update |
| [`narrative/06-grade.md`](narrative/06-grade.md) | A $\lambda$-adic grade on Clifford+$T$ operators |
| [`narrative/07-transport.md`](narrative/07-transport.md) | Direct closure of the Clifford-transport step at $n = 2, 3$ |
| [`narrative/references.md`](narrative/references.md) | Literature pointers used in the prose |

## Running things

```
cd haskell
ghc -O2 -isrc Main.hs -o stab-bw && ./stab-bw
```

The `Main.hs` binary exercises every module — lattice membership, kissing-number enumeration, stabilizer-state fidelity, bounded-distance decoding, decoder equivariance, the Pauli-logic simulator, the cyclotomic ring and its $\lambda$-adic valuation, the grade table, and the small-$n$ Clifford-preservation check. Expected output is documented inline.

The Lean 4 sources live in [`lean/`](lean/) organised by topic. 

## What is new versus what is in the literature

In the literature: the Barnes–Wall lattice and its free-module decomposition (Barnes and Wall 1959; Forest, Gosset, Kliuchnikov, McKinnon 2015); the Clifford-as-lattice-automorphism identification (Kliuchnikov and Schönnenbeck 2024); the bounded-distance decoder (Micciancio and Nicolosi 2008); the stabilizer tableau formalism (Aaronson and Gottesman 2004); the standard equational theories of the Clifford fragment (Selinger 2015; Backens 2014).

Contributed here: the presentation theorem as an assembly into a single strict-monoidal prop; the logical-lattice theorem identifying stabilizer codespaces as scaled Barnes–Wall lattices; the reading of the Micciancio–Nicolosi decoder as a hylomorphism, with equivariance as a free theorem; the sequent calculus $\mathsf{PL}_n$ with cut elimination as the tableau update; the $\lambda$-adic grade with its closed-form upper bound and certified $T$-count floor; the direct closure of the Clifford-transport step at the headline cases $n = 2$ and $n = 3$. Each contribution is documented at its own narrative file, with the Lean source for the proof and the Haskell module for the computation cross-referenced.

## Layout

```
stabilizer-bw/
├── README.md                       (this file)
├── LICENSE
├── haskell/
│   ├── README.md
│   ├── Main.hs                     (demo battery)
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
    ├── 07--transport.md
    └── references.md
```

## Acknowledgments

Parts of the Lean development used Aristotle (Harmonic) for automated proof search. Drafting and restructuring of the prose was assisted by Claude (Anthropic).

## Licence

Apache Licence 2.0; see [`LICENSE`](LICENSE).
