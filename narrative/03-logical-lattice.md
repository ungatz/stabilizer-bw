# The logical-lattice theorem

## Setup

Let $S = \langle g_1, \dots, g_m\rangle$ be a rank-$m$ stabilizer group on $n$ qubits, with $-I \notin S$. Its **constraint sublattice** is

```math
\mathrm{BW}_n^S = \{\,v \in \mathrm{BW}_n : g \cdot v = v \text{ for every } g \in S\,\}.
```

Equivalently $\mathrm{BW}\_{n}^S$ is the intersection of $\mathrm{BW}\_{n}$ with the codespace of $S$.

## The theorem

Let $U$ be any Clifford encoder for $S$ — that is, $U Z_j U^\dagger = g_j$ for $j \le m$ — in the lattice-preserving normalization. Then

```math
\mathrm{BW}_n^S = U\bigl(\,(1 + i)^m\,|0\rangle^{\otimes m} \otimes \mathrm{BW}_{n - m}\bigr).
```

That is: the constraint sublattice is an isometric copy of $\mathrm{BW}\_{n - m}$ scaled by $(1 + i)^m$, embedded back into $\mathrm{BW}\_{n}$ by the encoder.

**One-line consequence.** Imposing one bit of stabilizer classicality costs exactly one factor of $\varphi = 1 + i$. Stabilizer codes are Barnes–Wall lattices at a finer scale, sitting inside the big one; the encoder is a lattice isometry.

## Proof outline

The proof has two steps.

**Step 1 — the pinned case.** Take the principal stabilizer group $S_0 = \langle Z_1, \dots, Z_m\rangle$ and decompose any $w \in \mathrm{BW}\_{n}$ via the free-module decomposition of [`01-bw-family.md`](01-bw-family.md): $w = \varphi |0\rangle \otimes a + (|0\rangle + |1\rangle) \otimes b$ with $a, b \in \mathrm{BW}\_{n - 1}$. The condition $(Z \otimes I) w = w$ forces $b = 0$, so the fixed sublattice is exactly $\varphi |0\rangle \otimes \mathrm{BW}\_{n - 1}$. Iterating pins the first $m$ factors.

**Step 2 — Clifford transport.** For Clifford $U$ in the lattice-preserving normalization, $U\,\mathrm{BW}\_{n} = \mathrm{BW}\_{n}$ (the presentation theorem of [`02-presentation.md`](02-presentation.md)). Substituting $w = Uv$ converts the fixed-point condition for $S$ into the fixed-point condition for $S_0$ on $v$, so $\mathrm{BW}\_{n}^S = U(\mathrm{BW}\_{n}^{S_0})$. Step 1 finishes.

Unitarity of $U$ makes the identification isometric; the scaling factor $(1 + i)^m$ multiplies squared norms by $2^m$.

## What's proved

* The pinned case $m = 1$ and the free-module decomposition that drives it: [`../lean/BarnesWall/BWFreeModule.lean`](../lean/BarnesWall/BWFreeModule.lean) (`freeModuleDecomp`, `pinned_one`).
* The Bell-theory case ($m = n = 2$), with the minimal-vector classification: [`../lean/BarnesWall/BWFreeModule.lean`](../lean/BarnesWall/BWFreeModule.lean) (`bell_theory`, `bell_minimal_iff`).
* The Clifford-transport step **at the chapter's headline cases $n = 2$ and $n = 3$**, by direct computation: [`../lean/LogicalLatticeTransport/`](../lean/LogicalLatticeTransport/). See [`07-r11-transport.md`](07-r11-transport.md) for what is verified there.
* A Haskell realisation of the eleven two-qubit Clifford generators and the spanning-set preservation test: [`../haskell/src/Transport.hs`](../haskell/src/Transport.hs).

## What is in the literature

The kissing-number identification (the minimal vectors of $\mathrm{BW}\_{n}$ are the scaled stabilizer states) is Kliuchnikov–Schönnenbeck 2024, Theorem 3.4. The rectangular characterization of Clifford operators as lattice automorphisms is also theirs, Theorem 4.3.

The theorem above is stated and proved in this repository in **code form**: it identifies the codespace lattice as a scaled copy of the inner Barnes–Wall lattice, rather than as the image of an isometry. The two statements are equivalent up to the encoder isometry, but the code form is the one consumed by the logical-decoding corollary of [`04-prop-computes.md`](04-prop-computes.md) and by the lattice semantics of the Pauli logic in [`05-pauli-logic.md`](05-pauli-logic.md).
