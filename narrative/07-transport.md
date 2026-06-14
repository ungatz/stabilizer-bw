# Closing the transport step directly at *n* = 2 and *n* = 3

The logical-lattice theorem of [`03-logical-lattice.md`](03-logical-lattice.md) has a two-step proof. Step one handles the principal case by free-module decomposition; step two transports to general stabilizer groups by Clifford conjugation. The second step relies on a single external input: every Clifford operator, in the lattice-preserving normalization, maps $\mathrm{BW}\_{n}$ to itself. We cite Kliuchnikov–Schönnenbeck for this fact at general *n*.

This document records that the Kliuchnikov–Schönnenbeck citation can be removed at *n* = 2 and *n* = 3 — the two cases where every theorem in the chapter is exhibited concretely — by direct kernel computation. At these two cases the logical-lattice theorem is therefore kernel-proved with no external dependency for the lattice-automorphism input.

## Two qubits

At *n* = 2, eleven generators suffice for the Clifford group: the four Pauli generators $Z_1, Z_2, X_1, X_2$, the two phase gates $S_1, S_2$, both CNOTs $\mathrm{CNOT}_{1,2}$ and $\mathrm{CNOT}_{2,1}$, the controlled-$Z$, and both Hadamards $\mathrm{Had}_1, \mathrm{Had}_2$. We check that each preserves $\mathrm{BW}_2$ as a set.

The check rests on an explicit characterisation of $\mathrm{BW}_2$ in coordinates: a vector $(a, b, c, d) \in \mathbb{Z}[i]^4$ lies in $\mathrm{BW}_2$ if and only if $(1+i) \mid a + b$, $(1+i) \mid c + d$, and $(1+i)^2 \mid (a + b) - (c + d)$. The first two conditions are the free-module decomposition applied to the two halves; the third comes from the recursive step at the outer level. The Lean lemma `inBW2_iff` proves the characterisation, and then `Z1_preserves_BW2` through `Had2_preserves_BW2` apply it to each generator.

A small numerical experiment lives in [`../haskell/src/Transport.hs`](../haskell/src/Transport.hs). It works with the explicit $\mathbb{Z}[i]$-basis $\{v_0, v_1, v_2, v_3\}$ of $\mathrm{BW}_2$ — the four columns of $B^{\otimes 2}$, which are the four scaled basis vectors $\varphi^2|00\rangle$, $\varphi(|0\rangle \otimes (|0\rangle + |1\rangle))$, $\varphi((|0\rangle + |1\rangle) \otimes |0\rangle)$, and $(|0\rangle + |1\rangle)^{\otimes 2}$ — and checks that each named generator preserves all four basis vectors. The Haskell demo in `Main.hs` prints "True" for all eleven.

## Three qubits

At *n* = 3 the analogous fourteen-generator set $\{H_i, S_i, Z_i, \mathrm{CNOT}_{1,2}, \mathrm{CNOT}_{1,3}, \mathrm{CNOT}_{2,3}\}$ preserves $\mathrm{BW}_3$. The proof is by structural lemmas at $\mathrm{BW}_{n+1}$ — lifting a one-qubit generator at depth $n$ to depth $n + 1$, pinning the Z-block, swapping the two children of the outer node, and the outer-level Hadamard and S — together with the witness identity $v - X_i v \in (1+i) \cdot \mathrm{BW}_2$ for $i \in \{1, 2\}$, which is what the recursive coordinate condition demands. Along the way, $\mathrm{BW}\_{n}$ is verified to be an additive subgroup at every *n*: closed under addition, negation, and subtraction.

## Two named consequences

The two concrete transport identities the rest of the chapter relies on are now derived. First,
```math
\mathrm{BW}_2^{\langle ZZ \rangle} = \mathrm{CNOT}_{2,1}\bigl(\mathrm{BW}_2^{\langle Z_1 \rangle}\bigr),
```
which is the Bell-theory case stated against the pinned theory. Second, the *n* = 3 analogue,
```math
\mathrm{BW}_3^{\langle Z_1 Z_2 \rangle} = \mathrm{CNOT}_{1,2}\bigl(\mathrm{BW}_3^{\langle Z_2 \rangle}\bigr),
```
which is the repetition-code identity. A cross-check `bell_minimal_via_transport` reproduces the four Bell minimal vectors of $\mathrm{BW}_2^{\langle ZZ, XX \rangle}$ through the transport identification.

## The Hadamard convention, made explicit

A modelling note worth flagging. The genuine $1/\sqrt 2$ Hadamard
```math
H = \tfrac{1}{\sqrt 2}\begin{pmatrix}1 & 1\\ 1 & -1\end{pmatrix}
```
has irrational entries and is not a lattice map over $\mathbb{Z}[i]$. The kernel and the Haskell implementation use the $\sqrt 2$-scaled integer lift
```math
\tilde H_{\mathbb{Z}} = \begin{pmatrix}1 & 1\\ 1 & -1\end{pmatrix},
```
which sends $\mathrm{BW}\_{n}$ into itself (as a set, up to a uniform rescaling that does not affect lattice membership). The Pauli gates, *S*, $\mathrm{CNOT}$, and $CZ$ are honest $\mathbb{Z}[i]$-unitaries and exact lattice automorphisms. The genuine $1/\sqrt 2$ Hadamard requires the larger ring $\mathbb{Z}[\zeta_8] = \mathbb{Z}[\sqrt 2, i]$, which is also why the general-*n* statement of the transport step at $n \ge 4$ continues to cite Kliuchnikov–Schönnenbeck.

## What this does not close

The transport step at $n \ge 4$ still uses the external citation for the lattice-automorphism input. Closing that would require either porting the entire computation to $\mathbb{Z}[\zeta_8]$ — a substantial extension that would generalize a lot more than just transport — or replacing the integer-Hadamard convention with the genuine one, at which point the lattice argument is already in the literature. Neither extension is in scope here.
