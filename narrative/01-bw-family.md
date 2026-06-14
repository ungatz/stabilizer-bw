# The Barnes–Wall family

## The lattice

Fix the ring $R = \mathbb{Z}[i]$, with prime element $\varphi = 1 + i$ of norm $|\varphi|^2 = 2$. The **$n$-qubit Barnes–Wall lattice** $\mathrm{BW}_n$ is the rank-$2^n$ free $R$-module on $(\mathbb{C}^2)^{\otimes n}$ with basis matrix $B^{\otimes n}$, where
$$
  B \;=\; \begin{pmatrix} 1 + i & 1 \\ 0 & 1 \end{pmatrix} \;=\; \begin{pmatrix} \varphi & 1 \\ 0 & 1 \end{pmatrix}.
$$
Equivalently:
$$
  \mathrm{BW}_n \;=\; B^{\otimes n}\,R^{2^n} \;\subset\; \mathbb{C}^{2^n}.
$$
Three properties are immediate.

**Tensor structure.** Because the basis matrices tensor, $\mathrm{BW}_{m + n} = \mathrm{BW}_m \otimes_R \mathrm{BW}_n$. Every construction below respects the tensor on the nose, with no associator bookkeeping.

**Free-module decomposition.** The columns of $B$ span $R^2$ freely: the first column is $\varphi\lvert 0\rangle$ and the second is $\lvert 0\rangle + \lvert 1\rangle$. Tensoring, every $w \in \mathrm{BW}_n$ has a unique representation
$$
  w \;=\; \varphi\lvert 0\rangle \otimes a \;+\; \bigl(\lvert 0\rangle + \lvert 1\rangle\bigr) \otimes b,
  \qquad a, b \in \mathrm{BW}_{n - 1}.
$$
In coordinates: if $w = [w_0, w_1]$ with $w_0, w_1 \in \mathbb{C}^{2^{n-1}}$ the two halves, then $w \in \mathrm{BW}_n$ iff $w_0 \in \mathrm{BW}_{n-1}$ and $w_1 - w_0 \in \varphi \cdot \mathrm{BW}_{n-1}$.

**Minimal vectors.** The minimal vectors of $\mathrm{BW}_n$ have squared norm $2^n$. There are exactly $|\mathrm{Stab}_n| \cdot 4$ of them, where $|\mathrm{Stab}_n|$ is the number of $n$-qubit stabilizer states; each minimal vector is $\zeta^k \cdot \varphi^n \cdot C\lvert 0\rangle^{\otimes n}$ for $C$ Clifford and $\zeta^k$ an eighth root of unity (Kliuchnikov–Schönnenbeck 2024, Theorem 3.4). At $n = 1, 2, 3$ the counts are $24$, $240$, $4320$ — the kissing numbers of the real forms $D_4$, $E_8$, $\Lambda_{16}$ (the classical Barnes–Wall lattice).

## The Hadamard convention

The textbook Hadamard $H = \tfrac{1}{\sqrt 2}\begin{psmallmatrix}1 & 1\\ 1 & -1\end{psmallmatrix}$ has entries outside $\mathbb{Z}[i]$. Its rephased form
$$
  \tilde H \;=\; \zeta_8^{-1}\,H \;=\; \tfrac{1 - i}{2}\begin{pmatrix}1 & 1\\ 1 & -1\end{pmatrix}
$$
has entries in $\mathbb{Q}(i)$ and is a lattice automorphism of $\mathrm{BW}_1$; together with $S = \mathrm{diag}(1, i)$ and the controlled-NOT it generates the Clifford group in the lattice-preserving normalization. All phase bookkeeping below uses this convention; the leftover unit $\zeta^k$ is absorbed in the minimal-vector formula above.

## What's proved

* Free-module decomposition with uniqueness, the membership test, and the explicit basis — in [`../lean/BarnesWall/BWFreeModule.lean`](../lean/BarnesWall/BWFreeModule.lean).
* The $n = 1$ minimal-vector enumeration (24 vectors, four Clifford-orbit equivalence classes after units) — in [`../lean/BarnesWall/BarnesWall.lean`](../lean/BarnesWall/BarnesWall.lean).
* The membership test, the $n = 2$ kissing-number identity, and the Clifford-orbit reconstruction — in the Haskell module [`../haskell/src/BW.hs`](../haskell/src/BW.hs) and verified by the `minimalVectors` enumeration in [`../haskell/src/Prop.hs`](../haskell/src/Prop.hs).

## What is in the literature

The construction goes back to Barnes–Wall (1959); the modern view over cyclotomic rings is in Forest–Gosset–Kliuchnikov–McKinnon (2015) and Kliuchnikov–Schönnenbeck (2024). The kissing-number identification with stabilizer counts is the operative content of Calderbank (1997) plus Kliuchnikov–Schönnenbeck's Theorem 3.4. The free-module decomposition itself is a one-line consequence of the definition; its consequences (the logical-lattice theorem in [`03-logical-lattice.md`](03-logical-lattice.md), the decoder reading in [`04-prop-computes.md`](04-prop-computes.md), and the prop-level Pauli logic in [`05-pauli-logic.md`](05-pauli-logic.md)) are this development's contribution.
