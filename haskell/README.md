# Haskell companion

Executable companion to the proofs in [`../lean/`](../lean/) and the prose
in [`../narrative/`](../narrative/). Plain `base + containers`; no
external packages.

## Build

```
ghc -O2 -isrc Main.hs -o stab-bw && ./stab-bw
```

or in GHCi: `ghci -isrc Main.hs`.

## What's here

| Module           | Mathematics                                                            |
|------------------|------------------------------------------------------------------------|
| `GaussianInt`    | `Z[i]`, the prime `phi = 1 + i`, exact division.                       |
| `BW`             | Balanced-tree coordinates; `BW_n` membership by free-module recursion. |
| `Prop`           | Clifford generators acting on trees; minimal-vector orbit.             |
| `Decoder`        | Bounded-distance decoder (`MN08`) as a hylomorphism.                   |
| `Fidelity`       | Closest-stabilizer-state fidelity with a certified lower bound.        |
| `PauliLogic`     | The sequent calculus `PL_n`; cut elimination; measurement as a free monad. |
| `Cyclotomic`     | `Z[zeta_8]`; the prime `lam = 1 - zeta`; `lam`-adic valuation.         |
| `Grade`          | Closed-form lattice grade of diagonal Clifford+T characters.           |
| `Transport`      | The eleven two-qubit Clifford generators; `BW_2`-preservation test.    |

## Reading order

- [`../narrative/00-overview.md`](../narrative/00-overview.md) — the slogan and the scope.
- [`../narrative/01-bw-family.md`](../narrative/01-bw-family.md) — the lattice tower and free-module decomposition (`GaussianInt`, `BW`).
- [`../narrative/02-presentation.md`](../narrative/02-presentation.md) — the prop of lattice-preserving Cliffords (`Prop`).
- [`../narrative/03-logical-lattice.md`](../narrative/03-logical-lattice.md) — stabilizer codes as scaled `BW` (`Prop`, `Transport`).
- [`../narrative/04-prop-computes.md`](../narrative/04-prop-computes.md) — the decoder is the categorical structure run (`Decoder`, `Fidelity`).
- [`../narrative/05-pauli-logic.md`](../narrative/05-pauli-logic.md) — sequents, cut elimination, tableaux (`PauliLogic`).
- [`../narrative/06-grade.md`](../narrative/06-grade.md) — `lam`-adic grade and the `T`-count lower bound (`Cyclotomic`, `Grade`).
- [`../narrative/07-r11-transport.md`](../narrative/07-r11-transport.md) — the transport step at `n = 2, 3` (`Transport`).

## Demo output

`Main.hs` runs through every module. The expected (numerical) output for
each line is documented inline.
