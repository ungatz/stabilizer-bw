# The presentation theorem

## Three views of the Clifford group

The Clifford fragment of quantum computing admits three distinct presentations.

**Circuits and relations** (Selinger 2015). Generators $S, \tilde H, \mathrm{CNOT}$ with an explicit finite list of relations between gate words; every Clifford circuit identity is derivable in this calculus.

**Graphical calculus** (Backens 2014). Generators are spiders in the ZX-calculus; the stabilizer fragment is complete for Clifford up to global phase.

**Lattice automorphisms** (Kliuchnikov–Schönnenbeck 2024). The unitary $U$ on $(\mathbb{C}^2)^{\otimes n}$ satisfies $U\,\mathrm{BW}\_{n} = \mathrm{BW}\_{n}$ if and only if $U$ is a Clifford operator times a phase.

The presentation theorem says: when one normalises so that all three are strict symmetric monoidal categories with natural-number objects, they all present the same object — a single prop $\mathfrak{BW}$.

## The prop $\mathfrak{BW}$

Define $\mathfrak{BW}$ as the symmetric monoidal groupoid whose objects are natural numbers $n$ (standing for $\mathrm{BW}\_{n}$), whose morphisms $n \to n$ are the unitaries $U$ on $(\mathbb{C}^2)^{\otimes n}$ with $U\,\mathrm{BW}\_{n} = \mathrm{BW}\_{n}$, and whose monoidal product is the tensor product of operators. Strictness comes for free from the tensor-on-the-nose structure of the lattice itself (see [`01-bw-family.md`](01-bw-family.md)).

## What the theorem says

The presentation theorem is the statement that the following three identifications hold simultaneously:

1. The objects of $\mathfrak{BW}$ in degree $n$ are exactly the rank-$2^n$ unitaries preserving $\mathrm{BW}\_{n}$.
2. Selinger's relations on $\{S, \tilde H, \mathrm{CNOT}\}$ are precisely the equations between morphism words in $\mathfrak{BW}$.
3. The ZX-calculus's stabilizer fragment, interpreted in $\mathfrak{BW}$, is sound and complete.

Strict monoidal structure means no associator paths to chase: a program against the Clifford interface runs against the lattice without any coherence bookkeeping. Downstream sections rely on this absence: the decoder recursion in [`04-prop-computes.md`](04-prop-computes.md) and the cut-elimination algorithm in [`05-pauli-logic.md`](05-pauli-logic.md) both consume strict tensor.

## What's proved

* The Clifford generators act on the coordinate tree representation of $\mathrm{BW}\_{n}$, and the $n = 1$ orbit of $\varphi^n|0\rangle$ has 24 elements (the lattice's kissing-number 24 minimal vectors) — kernel-checked in [`../lean/BarnesWall/BarnesWall.lean`](../lean/BarnesWall/BarnesWall.lean) with documented exceptions for the finite enumerations.
* The generators are implemented as `Tree GI -> Tree GI` actions in [`../haskell/src/Prop.hs`](../haskell/src/Prop.hs); the orbit-enumeration function `minimalVectors` returns $24, 240, 4320$ at $n = 1, 2, 3$.

## What is in the literature

The three pieces — circuits (Selinger), graphics (Backens, Jeandel–Perdrix–Vilmart), lattice (Kliuchnikov–Schönnenbeck) — are each due to their authors. The assembly into a single prop with strict structure is the contribution here: there is no new hard mathematics in the theorem, but the assembly is what lets the downstream constructions (logical-lattice, prop-computes, Pauli logic) cash the categorical vocabulary as concrete computation.
