# Overview

The Barnes–Wall lattices are a tower
$$
  \mathrm{BW}_0 = \mathbb{Z}[i] \;\subset\; \mathrm{BW}_1 \;\subset\; \mathrm{BW}_2 \;\subset\; \dots
$$
of free modules over the ring of Gaussian integers, with one new factor at every step. They appear in the literature in three guises: as a fault-tolerant code (Calderbank 1997), as the densest known lattice packings in low dimensions (D₄ at four real dimensions, E₈ at eight, the classical Barnes–Wall lattice at sixteen), and most relevantly for this development, as the unique lattice on the $n$-qubit Hilbert space preserved by the Clifford group up to phase (Kliuchnikov–Schönnenbeck 2024). The third reading is the one this repository pursues.

This codebase makes the third reading concrete. It collects:

* a Lean 4 formalisation of the basic arithmetic of the lattice tower and the theorems that pin stabilizer codes inside it,
* a small but complete Haskell library that runs the same constructions on concrete data, and
* a chapter-by-chapter prose tour of what is proved, where, and what is new versus what is in the literature.

The headline results, in plain English:

1. **The Barnes–Wall lattice has a free-module decomposition.** Every vector in $\mathrm{BW}_n$ is uniquely $(1+i)\lvert 0\rangle\otimes a + (\lvert 0\rangle + \lvert 1\rangle)\otimes b$ with $a, b \in \mathrm{BW}_{n-1}$. This makes lattice membership a structural recursion. See [`01-bw-family.md`](01-bw-family.md).

2. **The Clifford group is the lattice automorphism group, up to phase.** Three independent specifications of the Clifford fragment of quantum computing — circuit relations (Selinger), graphical calculus (Backens), lattice automorphisms — fit together at the level of a single prop. See [`02-presentation.md`](02-presentation.md).

3. **Stabilizer codes are Barnes–Wall lattices at a finer scale.** For a rank-$m$ stabilizer group $S$ on $n$ qubits, the codespace lattice $\mathrm{BW}_n^S$ is an isometric copy of $\mathrm{BW}_{n-m}$ scaled by $(1+i)^m$. Imposing one bit of classicality costs one factor of $(1+i)$. See [`03-logical-lattice.md`](03-logical-lattice.md).

4. **The decoder is the categorical structure run as a program.** The Micciancio–Nicolosi bounded-distance decoder is, line by line, a hylomorphism whose coalgebra is the free-module decomposition and whose algebra is the closest-point reconciliation. See [`04-prop-computes.md`](04-prop-computes.md).

5. **Pauli logic.** A sequent calculus $\mathsf{PL}_n$ in which signed Pauli words are literals, the only nontrivial rule is multiplication of commuting generators, and cut elimination is exactly the Aaronson–Gottesman tableau update. The same proof object simulates the Clifford circuit. See [`05-pauli-logic.md`](05-pauli-logic.md).

6. **The grade.** A $\lambda$-adic valuation on Clifford+$T$ operators, where $\lambda = 1 - \zeta_8$ is the totally ramified prime above 2 in $\mathbb{Z}[\zeta_8]$. The grade is a certified $T$-count floor and stratifies the diagonal characters by an explicit closed-form upper bound. See [`06-grade.md`](06-grade.md).

7. **A direct closure of the Clifford-transport step at small $n$.** At $n = 2$ and $n = 3$, every Clifford generator's preservation of $\mathrm{BW}_n$ is verified by direct computation, removing one citation from the proof of the logical-lattice theorem at those cases. See [`07-r11-transport.md`](07-r11-transport.md).

## What lives where

* [`../lean/`](../lean/) — Lean 4 source for every theorem listed above. The `lean/README.md` is the per-file map.
* [`../haskell/`](../haskell/) — pure Haskell companion. The library runs concrete demonstrations of every construction; its `Main.hs` is a single-binary test battery.
* [`../narrative/`](.) — these documents.
* [`references.md`](references.md) — the literature pointers used here.

## What is new

The split between literature and new work is the same across the documents. In broad strokes:

* The lattice tower, free-module decomposition, kissing-number identification with the stabilizer-state count, and the Clifford-as-lattice-automorphism theorem are in the literature (Barnes–Wall; Calderbank; Kliuchnikov–Schönnenbeck).
* The presentation theorem, the logical-lattice theorem, the decoder-as-recursion-scheme reading, the Pauli-logic sequent calculus with cut-elimination-as-tableau, the $\lambda$-adic grade, and the direct small-$n$ closure of the transport step are stated and proved in this repository (each at its own document).
* Every theorem is tagged in place: the Lean source carries the statement, the narrative document explains it in prose, and the Haskell layer computes it on concrete inputs where computation makes sense.
