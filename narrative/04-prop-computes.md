# The prop computes

The categorical layer we set up in [`02-presentation.md`](02-presentation.md) is not scaffolding. It is the correctness contract of a fast lattice decoder that already exists in the literature.

## The decoder we are talking about

Micciancio and Nicolosi gave a bounded-distance decoder for the Barnes–Wall lattice in 2008. The contract is: if you hand it a target $s \in \mathbb{C}^{2^n}$ within squared distance $2^n / 4$ of the lattice, the decoder returns the unique closest lattice point. Their algorithm is recursive in *n*, with three ingredients that — read against [`01-bw-family.md`](01-bw-family.md) — are not chosen arbitrarily. They are precisely the data of the Barnes–Wall prop.

Split a target $s$ into halves $s_0, s_1 \in \mathbb{C}^{2^{n-1}}$. The free-module decomposition says the closest lattice point has the form $[u_0, u_0 + \varphi v]$ for some $u_0, v \in \mathrm{BW}_{n-1}$. Solving for $u_0$ and $v$ in terms of $s_0$ and $s_1$ produces four candidate sub-targets:
```math
s_0, \quad s_1, \quad s_- = \tfrac{\varphi}{2}(s_0 - s_1), \quad s_+ = \tfrac{\varphi}{2}(s_0 + s_1).
```
The first two are obvious — they are the projections onto the two halves. The other two come from the mixing automorphism $T: [s_0, s_1] \mapsto [s_-, s_+]$. In the lattice-preserving normalization $T$ turns out to be $i \cdot (X\tilde H \otimes I^{\otimes(n - 1)})$ — a phased Clifford. The mixing step is itself a prop morphism, supplied by the presentation theorem.

Decode each of the four subproblems by recursion, then reassemble the four candidate lattice points by inverting the linear maps that produced the subtargets. Return the candidate closest to *s*. Why the closest candidate is the closest lattice point overall is what the free-module decomposition guarantees: those four candidates exhaust the cases.

## A recursion-scheme reading

Read as a Haskell programmer: this is a hylomorphism, an unfold followed by a fold, fused. The coalgebra is the splitting (target in, four subtargets out). The algebra is the reconciliation (four sub-decoded lattice points in, four candidates out, closest one wins). The lattice is the initial algebra of the pairing functor $F(X) = X \times X$ over the leaf type $\mathbb{Z}[i]$, and the decoder factors through that functor in the obvious way. In our [`../haskell/src/Decoder.hs`](../haskell/src/Decoder.hs) the whole algorithm is two definitions: the coalgebra `splitStep`, the algebra `reconcile`, fused by `hylo`. There is no other code in the module.

This is more than typography. It says the mixing step has to be a prop morphism — a lattice automorphism — for the recursion to be correct, and it says the equivariance theorem below is forced by parametricity in the same way a free theorem is.

## Equivariance, as a free theorem

If $U$ is any lattice-preserving Clifford and $s$ is a target inside the bounded-distance promise, then the decoder commutes with $U$:
```math
\mathrm{decode}(Us) = U \cdot \mathrm{decode}(s).
```
This is naturality for the family of decoders $\{\mathrm{decode}\_{n}\}_n$ on the groupoid of prop morphisms. Operationally it says you can pre-condition any closest-stabilizer computation by a cheap Clifford circuit and pull the answer back exactly. The error analysis of bounded-distance decoding descends to Clifford orbits, so single-representative computations suffice — useful when you want to reason about a stabilizer state's neighbourhood without enumerating its 24-or-larger orbit.

## Closest-stabilizer fidelity

Decoding gives you stabilizer-state fidelity for free. Given a unit state $|\psi\rangle$ on *n* qubits, scale it to lattice length $2^{n/2}$, snap to the grid over a small range of global phases, and keep snaps whose squared norm comes out exactly $2^n$ — the inner shell of $\mathrm{BW}\_{n}$, which is exactly the scaled stabilizer states. Return the best overlap. The result is a certified lower bound on $F_{\mathrm{STAB}}(\psi)$; in the regime $F_{\mathrm{STAB}} \geq 7/8 + \eta$, with grid size of order $\eta^{-1/2}$, the bound is sharp and the witness is the closest stabilizer state. Implementation: [`../haskell/src/Fidelity.hs`](../haskell/src/Fidelity.hs). The Haskell demo reproduces the textbook benchmarks $F(T) = 0.8881$, $F(H) = \cos(\pi/8)$, $F(H \otimes H) = \cos^2(\pi/8)$ exactly.

## Closest logical stabilizer state

Combine the decoder with the logical-lattice theorem of [`03-logical-lattice.md`](03-logical-lattice.md): the closest-point problem on $\mathrm{BW}\_{n}^S$, for a rank-*m* stabilizer $S$, reduces — through the encoder $U$ and the similarity $(1 + i)^m$ — to bounded-distance decoding on $\mathrm{BW}_{n - m}$. The cost is $O(2^{n - m}\,(n - m)^2)$ plus one application of the encoder. So the *closest logical stabilizer state* of an encoded vector, and therefore the logical stabilizer fidelity and the residual magic of the encoded data, is computable in time exponential in the residual qubit count, not the full *n*.

## What's here and where

The Lean side is in [`../lean/Decoder/`](../lean/Decoder/) — the base case $n = 1$, the four-candidate reconciliation, the threshold and uniqueness arguments, the fidelity bridge, and the logical-decoding corollary. The Haskell side is the two-function `Decoder` module and the `Fidelity` module that wraps it.

## What's new, what's borrowed

The decoder and the bounded-distance guarantee are Micciancio and Nicolosi (2008). The reading of the algorithm as a hylomorphism on the iterated-pair functor, the identification of the mixing step with a phased Clifford, the equivariance theorem, the fidelity bridge, and the logical-decoding corollary are what we add.
