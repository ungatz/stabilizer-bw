# Overview

If you teach a programmer "Gaussian integers" — pairs of whole numbers obeying $i^2 = -1$, with the single odd prime $1 + i$ above two — you have given her enough to do most of stabilizer quantum computing. That is the slogan of this repository, and it is roughly the surprise of the subject.

The Barnes–Wall lattices are the structure that makes the slogan precise. They form a tower
```math
\mathrm{BW}_0 \subset \mathrm{BW}_1 \subset \mathrm{BW}_2 \subset \dots
```
of free modules over $\mathbb{Z}[i]$, doubling in rank at every step. Calderbank used them in the 1990s as a fault-tolerant code; lattice theorists have known them since Barnes and Wall in 1959 as some of the densest packings in low dimensions (the real form of $\mathrm{BW}_2$ is $E_8$). What is more recent — Kliuchnikov and Schönnenbeck, 2024 — is the observation that runs through everything here: a unitary on $n$ qubits preserves $\mathrm{BW}\_{n}$ if and only if it is a Clifford operator, up to a phase. The Clifford group, viewed correctly, is a *lattice automorphism group*. Once you know that, the rest of the theory becomes arithmetic.

This repository is the lattice-arithmetic story, in three media. The Lean 4 sources in [`../lean/`](../lean/) carry the theorems with machine-checked proofs. The Haskell library in [`../haskell/`](../haskell/) runs the constructions on concrete data — lattice membership, decoding, fidelities, the Pauli-logic simulator, the grade calculation, the small-*n* Clifford check. The documents in this folder explain what is going on and why, and mark carefully which pieces come from the literature and which are new.

There are seven results worth knowing.

The first is structural: every vector in $\mathrm{BW}\_{n}$ splits uniquely as $\varphi |0\rangle \otimes a + (|0\rangle + |1\rangle) \otimes b$ with $a, b \in \mathrm{BW}_{n-1}$, where $\varphi = 1 + i$. This is the free-module decomposition, and it turns lattice membership into a recursion — read [`01-bw-family.md`](01-bw-family.md).

The second is categorical. Three independent specifications of the Clifford fragment — Selinger's circuit relations, Backens's graphical calculus, Kliuchnikov–Schönnenbeck's lattice automorphisms — are the same object, in the strict-monoidal sense where there is no associator bookkeeping to do. See [`02-presentation.md`](02-presentation.md).

The third is the centerpiece of the chapter, and the only result here we believe is unambiguously new. A rank-*m* stabilizer code on *n* qubits has its codespace lattice equal to the inner $(n - m)$-qubit Barnes–Wall lattice, scaled by exactly $(1+i)^m$. Imposing one bit of stabilizer classicality costs one factor of the lattice's prime above two. Stabilizer codes are Barnes–Wall lattices at a finer scale, and the encoder is a lattice isometry. See [`03-logical-lattice.md`](03-logical-lattice.md).

The fourth is the consequence for the existing Micciancio–Nicolosi decoder: it is, line by line, a recursion scheme on the iterated-pair functor, with the lattice's free-module decomposition as its coalgebra and the closest-point reconciliation as its algebra. The mixing step that the original paper verifies by hand turns out to be the phased Clifford $i \cdot (X\tilde H \otimes I)$, supplied by the presentation theorem. The decoder is the categorical structure run as a program. See [`04-prop-computes.md`](04-prop-computes.md).

The fifth is a sequent calculus, $\mathsf{PL}\_{n}$, whose literals are signed Pauli words and whose only non-trivial rule is multiplying two commuting generators. Cut elimination in this calculus runs in time linear in the proof DAG, and what it is doing is exactly the row-reduction step of Aaronson and Gottesman's tableau algorithm. Measurement is exposed as a free monad over a single coin-flip operation. See [`05-pauli-logic.md`](05-pauli-logic.md).

The sixth is the one quantitative refinement worth carrying across to Clifford+*T*. There is a $\lambda$-adic valuation on diagonal characters of the level-*n* Barnes–Wall lattice, with $\lambda = 1 - \zeta_8$ the ramified prime above two in $\mathbb{Z}[\zeta_8]$. We call it the grade. It vanishes on Clifford and is at least one on every *T* gate, so it is a certified *T*-count floor; it has an explicit closed form $\max(0, 2d - 2^{\nu_2(c)})$ for single-monomial characters, where *d* is the support size and $\nu_2(c)$ the 2-adic valuation of the eighth-root coefficient. See [`06-grade.md`](06-grade.md).

The seventh is bookkeeping that turns out to matter. The Clifford-transport step in the proof of the logical-lattice theorem cites Kliuchnikov–Schönnenbeck for general *n*. We close it directly, by kernel computation, at *n* = 2 and *n* = 3. See [`07-transport.md`](07-transport.md).

What is new versus what is in the literature, in a sentence: the lattice tower, its free-module decomposition, the kissing-number identification with stabilizer counts, and the Clifford-as-lattice-automorphism theorem are in the literature. The presentation theorem (as an assembly), the logical-lattice theorem, the decoder-as-recursion-scheme reading, the Pauli-logic calculus with cut-elimination-as-tableau, the $\lambda$-adic grade, and the small-*n* direct closure are stated and proved here.

For the long view — how three independent traditions (Yates 1937 on algorithmic combinatorics, Barnes–Wall 1959 on geometry of numbers, Bolt–Room–Wall 1961 on finite group theory) spent sixty-five years cultivating the same object without coordinating, and which paper supplied which piece of the story above — see [`08-genealogy.md`](08-genealogy.md). It is read after the technical documents; readers who only want the mathematics can skip it without loss.

For literature pointers used throughout, see [`references.md`](references.md).
