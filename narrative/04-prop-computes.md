# The prop computes

## The slogan

The categorical layer of the Barnes–Wall story is not scaffolding. It is the correctness contract of an existing decoding algorithm — the Micciancio–Nicolosi bounded-distance decoder for Barnes–Wall lattices.

## The decoder, in three steps

Given a target $s \in \mathbb{C}^{2^n}$ with $\mathrm{dist}^2(s, \mathrm{BW}_n) < 2^n / 4$, the decoder returns the unique closest lattice point. The recursion has three ingredients.

**Splitting.** Write $s = [s_0, s_1]$ with $s_0, s_1 \in \mathbb{C}^{2^{n-1}}$ the two halves. The free-module decomposition of [`01-bw-family.md`](01-bw-family.md) says the closest lattice point has the form $[u_0, u_0 + \varphi v]$ for some $u_0, v \in \mathrm{BW}_{n - 1}$. Solving for $u_0$ and $v$ in terms of $s_0$ and $s_1$ gives four subproblems on half-size targets.

**Mixing.** The two new targets are
$$
  s_- \;=\; \tfrac{\varphi}{2}(s_0 - s_1), \qquad s_+ \;=\; \tfrac{\varphi}{2}(s_0 + s_1).
$$
The map $[s_0, s_1] \mapsto [s_-, s_+]$ is the lattice automorphism $T$ of Micciancio–Nicolosi; in this normalisation it is the phased Clifford $i \cdot ((X\tilde H) \otimes I^{\otimes(n - 1)})$. The mixing step is itself a prop morphism.

**Reconciliation.** Solve the four subproblems independently; assemble four candidate lattice points; return the one closest to $s$. Correctness — that one of the four candidates is in fact the closest lattice point — is the free-module decomposition again.

## The recursion scheme

The decoder is a hylomorphism whose coalgebra is the splitting and whose algebra is the reconciliation:
$$
  \mathrm{decode} \;=\; \mathrm{hylo}(\mathrm{reconcile},\;\mathrm{splitStep}).
$$
In Haskell this is one line of code (see [`../haskell/src/Decoder.hs`](../haskell/src/Decoder.hs)). The Lean version of the contract — "the closest lattice point is among the four candidates" — is in [`../lean/Decoder/DecoderTheorems.lean`](../lean/Decoder/DecoderTheorems.lean) and `DecoderN1.lean`.

## Equivariance, as a free theorem

If $U \in \mathfrak{BW}(n, n)$ is a lattice-preserving Clifford and $s$ is inside the promise radius, then
$$
  \mathrm{decode}(U s) \;=\; U \cdot \mathrm{decode}(s).
$$
This is naturality for the family $\{\mathrm{decode}_n\}_n$ on the groupoid $\mathfrak{BW}$. Operationally: closest-stabilizer-state computations can be preconditioned by any cheap Clifford circuit and pulled back exactly. The error analysis of bounded-distance decoding descends to Clifford orbits, so single-representative computations suffice.

## Closest-stabilizer fidelity

For a unit state $\lvert\psi\rangle$, scale to lattice length $2^{n/2}$, snap to the grid over a small range of global phases, keep snaps whose squared norm equals $2^n$ (the inner shell of $\mathrm{BW}_n$ — the stabilizer states), and return the best overlap. The result is a certified lower bound on the closest-stabilizer fidelity $F_{\mathrm{STAB}}(\psi)$; under the bounded-distance promise $F_{\mathrm{STAB}} \ge 7/8 + \eta$ (grid size $O(\eta^{-1/2})$), it is the exact maximum and the closest stabilizer state. See [`../haskell/src/Fidelity.hs`](../haskell/src/Fidelity.hs) for the implementation, and [`../lean/Decoder/DecoderFidelity.lean`](../lean/Decoder/DecoderFidelity.lean) for the proof.

## Logical decoding

Combined with the logical-lattice theorem of [`03-logical-lattice.md`](03-logical-lattice.md), the decoder solves the closest-point problem on the constraint sublattice $\mathrm{BW}_n^S$ at cost $O(2^{n - m} \cdot (n - m)^2)$ plus one application of the encoder. This gives the **closest logical stabilizer state** of an encoded vector, with the logical stabilizer fidelity and the residual magic computable in time exponential in $n - m$ only. See [`../lean/Decoder/DecoderLogical.lean`](../lean/Decoder/DecoderLogical.lean).

## What's proved

* Bounded-distance correctness, uniqueness, the threshold value, and the equivariance theorem — kernel-checked across `DecoderN1.lean`, `DecoderTheorems.lean`, `DecoderThreshold.lean`, `DecoderUniqueness.lean`.
* Fidelity via decoding with the certified-lower-bound property — `DecoderFidelity.lean`.
* The logical-decoding corollary — `DecoderLogical.lean`.
* The Haskell layer reproduces every fidelity benchmark numerically: $F(T) = 0.8881$, $F(H) = \cos(\pi/8)$, $F(H \otimes H) = \cos^2(\pi/8)$.

## What is in the literature

The decoder algorithm and its bounded-distance guarantee are Micciancio–Nicolosi 2008. The reading of the algorithm as a recursion scheme (hylomorphism on the iterated-pair functor), the identification of the mixing step with a phased Clifford, and the equivariance theorem are stated and proved in this repository. The fidelity-via-decoding pipeline and the logical-decoding corollary are also new here.
