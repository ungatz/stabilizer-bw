# Direct closure of the transport step at $n = 2$ and $n = 3$

## The gap this closes

The logical-lattice theorem of [`03-logical-lattice.md`](03-logical-lattice.md) has a two-step proof: the pinned case (free-module decomposition) and the Clifford transport step. The transport step relies on the fact that every Clifford operator in the lattice-preserving normalisation maps $\mathrm{BW}\_{n}$ to itself. For general $n$ this is cited from Kliuchnikov–Schönnenbeck 2024, Theorem 4.3.

This document records the direct closure of the transport step at $n = 2$ and $n = 3$, by kernel computation, without invoking the cited theorem. The logical-lattice theorem is therefore kernel-proved at its two headline cases with no external dependency for the lattice-automorphism input.

## What is checked

**At $n = 2$.** Each of the eleven generators

```math
\{Z_1, Z_2, X_1, X_2, S_1, S_2, \mathrm{CNOT}_{1,2}, \mathrm{CNOT}_{2,1}, CZ, \mathrm{Had}_1, \mathrm{Had}_2\}
```

is shown to preserve $\mathrm{BW}\_{2}$. The proof is by direct computation against the explicit characterisation

```math
(a, b, c, d) \in \mathrm{BW}_2 \iff (1+i) \mid a + b, \ (1+i) \mid c + d, \ \text{and}\ (1+i)^2 \mid (a + b) - (c + d),
```

which is itself a one-line consequence of the free-module decomposition. The corresponding Lean lemmas are `inBW2_iff`, `Z1_preserves_BW2`, …, `Had2_preserves_BW2`. The abstract transport theorem `transport_general` composes them.

**At $n = 3$.** The analogous fourteen-generator set

```math
\{H_i, S_i, Z_i, \mathrm{CNOT}_{1,2}, \mathrm{CNOT}_{1,3}, \mathrm{CNOT}_{2,3}\}\quad i \in \{1, 2, 3\}
```

is shown to preserve $\mathrm{BW}\_{3}$, via structural preservation lemmas at $\mathrm{BW}\_{n+1}$ (`lift23_preserves`, `pinZ_preserves`, `swapBlocks_preserves`, `hadOuter_preserves`, `sgateOuter_preserves`) and the witness identity $v - X_i \cdot v \in (1+i) \cdot \mathrm{BW}\_{2}$ for $i \in \{1, 2\}$.

**Subgroup closure at every $n$.** Along the way, $\mathrm{BW}\_{n}$ is verified to be an additive subgroup at every $n$: `InBWn_add`, `InBWn_neg`, `InBWn_sub`.

**Concrete instances.** The chapter's two named transport identities are now kernel-derived:

```math
\mathrm{BW}_2^{\langle ZZ\rangle} = \mathrm{CNOT}_{2,1}\bigl(\mathrm{BW}_2^{\langle Z_1\rangle}\bigr) \quad (\texttt{ZZ\_lattice\_eq\_transport}),
```

```math
\mathrm{BW}_3^{\langle Z_1 Z_2\rangle} = \mathrm{CNOT}_{1,2}\bigl(\mathrm{BW}_3^{\langle Z_2\rangle}\bigr) \quad (\texttt{repetition\_code\_transport}),
```

plus the cross-check `bell_minimal_via_transport`, which reproduces the four Bell-state minimal vectors of $\mathrm{BW}\_{2}^{\langle ZZ, XX\rangle}$ through the transport identification.

## The Hadamard convention

A modelling note kept honest. The genuine $1/\sqrt 2$ Hadamard

```math
H = \tfrac{1}{\sqrt 2}\begin{pmatrix}1 & 1\\ 1 & -1\end{pmatrix}
```

is not representable as a lattice map over $\mathbb{Z}[i]$: it has irrational entries. The kernel and the Haskell implementation use the $\sqrt 2$-scaled integer lift

```math
\tilde H_{\mathbb{Z}} = \begin{pmatrix}1 & 1\\ 1 & -1\end{pmatrix},
```

which preserves the Barnes–Wall lattice as a set (and is what the transport step needs). The phase is absorbed in the unit prefactor of the minimal-vector formula. Pauli, $S$, $\mathrm{CNOT}$, and $CZ$ are honest $\mathbb{Z}[i]$-unitaries and exact lattice automorphisms. The genuine $1/\sqrt 2$ Hadamard requires the larger ring $\mathbb{Z}[\zeta_8] = \mathbb{Z}[\sqrt 2, i]$, which is also why the general-$n$ statement of the transport step (for $n \ge 4$) continues to cite Kliuchnikov–Schönnenbeck.

## What's proved

* Generator-by-generator preservation at $n = 2$ — [`../lean/LogicalLatticeTransport/BW2Transport.lean`](../lean/LogicalLatticeTransport/BW2Transport.lean).
* Generator-by-generator preservation at $n = 3$ — [`../lean/LogicalLatticeTransport/BW3Transport.lean`](../lean/LogicalLatticeTransport/BW3Transport.lean).
* The abstract `transport_general` theorem composing these — [`../lean/LogicalLatticeTransport/LogicalLatticeTransport.lean`](../lean/LogicalLatticeTransport/LogicalLatticeTransport.lean).
* The Haskell layer reproduces the same check on the explicit four-element $\mathbb{Z}[i]$-basis of $\mathrm{BW}\_{2}$: `preservesBW2` returns true for every member of `twoQubitGenerators`. See [`../haskell/src/Transport.hs`](../haskell/src/Transport.hs).

## What this does not close

The transport step at $n \ge 4$ continues to use Kliuchnikov–Schönnenbeck for the lattice-automorphism input. The reason is structural: the genuine Hadamard needs $\mathbb{Z}[\zeta_8]$, not $\mathbb{Z}[i]$, and the present development's small-$n$ computations are over the smaller ring. Lifting to general $n$ requires either porting the entire computation to $\mathbb{Z}[\zeta_8]$ (a substantial extension) or replacing the integer-Hadamard convention with the genuine one, where the lattice argument is already in the literature. Neither is in scope here.
