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
| [`narrative/08-cyclotomic-arithmetic.md`](narrative/08-cyclotomic-arithmetic.md) | The cyclotomic tower, the $\lambda$-adic valuation, and the $\sqrt{\Pi}$ dictionary |
| [`narrative/09-mixing-time.md`](narrative/09-mixing-time.md) | The parity chain on the grade ladder; closed-form mixing time via Levin–Peres–Wilmer |
| [`narrative/10-decoding.md`](narrative/10-decoding.md) | Closest-stabilizer-state algorithm; single-$T$ branch decoder; verification suite |
| [`narrative/11-automorphisms.md`](narrative/11-automorphisms.md) | $\mathrm{Aut}(L_3) \cap U(2)$ converse; level-4 diagonal automorphisms |
| [`narrative/12-css-and-qutrits.md`](narrative/12-css-and-qutrits.md) | Reed–Muller CSS family; qutrit Barnes–Wall analogue at $d = 3$ |
| [`narrative/references.md`](narrative/references.md) | Literature pointers used in the prose |

## Running things

```
cd haskell
ghc -O2 -isrc Main.hs -o stab-bw && ./stab-bw
```

The `Main.hs` binary exercises every Haskell module — lattice membership, kissing-number enumeration, stabilizer-state fidelity, bounded-distance decoding, decoder equivariance, the Pauli-logic simulator, the cyclotomic ring and its $\lambda$-adic valuation, the grade table, and the small-$n$ Clifford-preservation check. Expected output is documented inline.

The Lean 4 sources live in [`lean/`](lean/) organised by topic. The repository ships as a Lake project: from a clean clone,

```
lake update           # one-time, pulls Mathlib v4.29 via the Azure cache
lake exe cache get    # fetches precompiled Mathlib oleans
lake build StabilizerBW
```

builds the entire library. The umbrella aggregator [`lean/StabilizerBW.lean`](lean/StabilizerBW.lean) imports every public module.

The Python decoder experiments are in [`experiments/bw-decoder/`](experiments/bw-decoder/); see the README in that directory for per-script commands and expected outputs.

## What is new versus what is in the literature

In the literature: the Barnes–Wall lattice and its free-module decomposition (Barnes and Wall 1959; Forest, Gosset, Kliuchnikov, McKinnon 2015); the Clifford-as-lattice-automorphism identification (Kliuchnikov and Schönnenbeck 2024); the bounded-distance decoder (Micciancio and Nicolosi 2008); the stabilizer tableau formalism (Aaronson and Gottesman 2004); the standard equational theories of the Clifford fragment (Selinger 2015; Backens 2014).

Contributed here: the presentation theorem as an assembly into a single strict-monoidal prop; the logical-lattice theorem identifying stabilizer codespaces as scaled Barnes–Wall lattices; the reading of the Micciancio–Nicolosi decoder as a hylomorphism, with equivariance as a free theorem; the sequent calculus $\mathsf{PL}_n$ with soundness, cut elimination as the tableau update, a trace-identity completeness theorem, and a dagger compact closed categorical reading; the $\lambda$-adic grade with its closed-form upper bound, certified $T$-count floor, multi-monomial Möbius closed form, and the closed-form $G_m(z) = 8 \cdot 4^m \cdot (1+z)^m$ on linear phases; a Reed–Muller-based Barnes–Wall CSS family that recovers that same enumerator on its weight side; the direct closure of the Clifford-transport step at the headline cases $n = 2$ and $n = 3$; and the one-qubit unitary $\mathrm{Aut}(L_3)$ converse over $\mathbb{Z}[\zeta_8]$, with a denominator-change companion that restores the full single-qubit Clifford count of 24. Each contribution is documented at its own narrative file, with the Lean source for the proof and the Haskell module for the computation cross-referenced.

## Layout

```
stabilizer-barnes-wall/
├── README.md                       (this file)
├── LICENSE
├── lakefile.toml                   (Lake project, Mathlib v4.29)
├── lean-toolchain                  (leanprover/lean4:v4.29.0)
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
│   ├── StabilizerBW.lean           (umbrella aggregator)
│   └── StabilizerBW/
│       ├── BarnesWall.lean
│       ├── BWFreeModule.lean
│       ├── Stab2CHSHBridge.lean
│       ├── LogicalLatticeTransport.lean, LogicalLatticeTransport/
│       ├── Decoder*.lean
│       ├── PauliLogic/                  syntax, rules, soundness,
│       │                                 cut elimination, tableau,
│       │                                 completeness, Categorical/
│       ├── Roots/                       λ-adic grade, BW2-BW4, all-n,
│       │                                 multi-monomial Möbius, AutL3, AutL4
│       ├── ReedMuller/                         closed-form grade enumerator (linear stratum)
│       ├── BWCss/                       Reed-Muller CSS family
│       ├── Grade/                       grade-stratified content:
│       │     ├── Kernel/                kernel = lattice stabilizer
│       │     ├── StratifiedMonotone/    Pauli-weight enumerator
│       │     ├── TightWitnesses/        T/CS/cT roster + CCZ/CCS/ccT loose triple
│       │     ├── EnumeratorBound/       closed-form bandwidth at all n
│       │     ├── Catalyst/              CHKRS S13 catalyst-identity carrier
│       │     ├── AlgorithmAudit/AQC/    QPE, AA, HHL, VQE grade audits
│       │     └── Comparisons/Incomparability/  grade vs Jiang-Wang nullity
│       ├── Lattice/Mixing/              parity-chain mixing time + Levin-Peres-Wilmer
│       └── Qutrit/                      qutrit Barnes-Wall analogue (d=3)
├── experiments/
│   └── bw-decoder/                 Python verification suite + JSON reports
└── narrative/
    ├── 00-overview.md
    ├── 01-bw-family.md
    ├── 02-presentation.md
    ├── 03-logical-lattice.md
    ├── 04-prop-computes.md
    ├── 05-pauli-logic.md
    ├── 06-grade.md
    ├── 07-transport.md
    ├── 08-cyclotomic-arithmetic.md
    ├── 09-mixing-time.md
    ├── 10-decoding.md
    ├── 11-automorphisms.md
    ├── 12-css-and-qutrits.md
    └── references.md
```

## Acknowledgement

Some private drafting and proof exploration used AI-assisted tools. All public statements, code, proofs, and errors are the author's responsibility.

## Licence

Apache Licence 2.0; see [`LICENSE`](LICENSE).
