# Lattice automorphisms

The grade vanishes on lattice automorphisms — that statement is the source of every Clifford-fragment-as-grade-zero theorem in this repository. Three results are kernel-checked. At the qubit level the unitary automorphism group of $L_3$ is exactly the phased single-qubit Clifford group. The integral converse fails without unitarity, by an explicit counterexample. The diagonal automorphism group of $L_4$ at level 4 is the cyclotomic-units group of order $128$, in a specific parity-conditioned form.

## $\mathrm{Aut}(L_3) \cap U(2)$ is the phased Clifford-24

The level-3 Barnes–Wall lattice is

```math
L_3 = \{ (a, b) \in \mathbb{Z}[\zeta_8]^2 \;:\; (1 + i) \mid a + b \}.
```
A $\mathbb{Z}[\zeta_8]$-linear endomorphism of $L_3$ is integral; if it also preserves the inner product induced by the standard $\mathbb{C}^2$ Hermitian form, it is unitary. The unitary automorphism group is

```math
\mathrm{Aut}(L_3) \cap U(2) \;=\; \{\pm \zeta_8^k\} \cdot \langle S, \tilde H \rangle,
```
where $S = \mathrm{diag}(1, i)$ is the phase gate, $\tilde H = \zeta_8^{-1} H$ is the lattice-preserving Hadamard rephasing, and $\langle S, \tilde H \rangle$ is the group they generate. The right factor is the single-qubit Clifford-24 (the group of $24$ Clifford operators acting projectively on the Bloch sphere as the rotational symmetries of the regular octahedron). The left factor $\{\pm \zeta_8^k\}$ contributes the $16$ central phases that fix the lattice setwise. The unitary group has order $|\{\pm \zeta_8^k\}| \cdot |\mathrm{Clifford}_1| = 16 \cdot 24 = 384$.

This is the converse to the standard direction. The forward direction — Clifford is lattice-preserving — is immediate from the explicit matrix entries of $S$ and $\tilde H$ in $\mathbb{Z}[\zeta_8]$. The converse — every unitary lattice automorphism is phased Clifford — requires showing that no other unitary matrix has integral entries that fix $L_3$. The proof in [`../lean/StabilizerBW/Roots/AutL3Unitary.lean`](../lean/StabilizerBW/Roots/AutL3Unitary.lean) finite-cases the determinant and trace constraints over $\mathbb{Z}[\zeta_8]$, reducing to a kernel `decide` on a $16$-element search space.

The phased Clifford group of order $24$ recovers from the same construction by quotienting out the central phases:

```math
\bigl( \mathrm{Aut}(L_3) \cap U(2) \bigr) \big/ \{\pm \zeta_8^k\} \;=\; \mathrm{Clifford}_1.
```
The half-$\sqrt{2}$ extension `clifford24_card = 24` is the parity-conditioned form that picks $\tilde H$ over $H$; it is kernel-checked in [`../lean/StabilizerBW/Roots/AutL3HalfSqrt2.lean`](../lean/StabilizerBW/Roots/AutL3HalfSqrt2.lean).

## Unitarity is essential

The natural unconditional version of the converse — "every integral grade-zero endomorphism of $L_3$ is Clifford" — is *false*. The explicit witness is

```math
D \;=\; \mathrm{diag}(1, 1 + \sqrt{2}).
```
Compute: the entries $1$ and $1 + \sqrt{2} = 1 + (\zeta_8 + \zeta_8^{-1})$ are both integral in $\mathbb{Z}[\zeta_8]$, so $D$ is an integral diagonal matrix. The determinant is $1 \cdot (1 + \sqrt{2}) = 1 + \sqrt{2}$, a unit in $\mathbb{Z}[\zeta_8]^\times$, so $\lambda^0 D \cdot L_3 = L_3$ as a lattice (the determinant being a unit means the lattice index does not increase). The grade of $D$ is therefore zero. But $D$ is not unitary: $|1 + \sqrt{2}|^2 = (1 + \sqrt{2})^2 = 3 + 2\sqrt{2} \ne 1$. So $D$ is in $\mathrm{Aut}(L_3)$ as a lattice but not in $U(2)$, and the unconditional converse fails.

The unit $1 + \sqrt{2}$ in $\mathbb{Z}[\zeta_8]^\times$ is the fundamental unit of the real subfield $\mathbb{Z}[\sqrt{2}]$, and it generates a free $\mathbb{Z}$ of infinite rank inside the unit group. Multiplying any matrix by $(1 + \sqrt{2})^k$ scales it without affecting grade, since multiplication by a unit does not change the $\lambda$-adic valuation. The integral grade-zero stratum at the single qubit is therefore *not* a finite group — it has infinite-order non-unitary elements. Forgetting the unitarity hypothesis loses the finiteness.

## $\mathrm{Aut}_{\mathrm{diag}}(L_4)$ has order $128$

At level 4 the Barnes–Wall lattice is

```math
L_4 \subset \mathbb{Z}[\zeta_{16}]^4,
```
and the unitary automorphism group is the level-4 Clifford group, of size approximately $92$ million. The full converse at level 4 is computationally infeasible by the same enumeration argument that works at level 3. What is feasible at level 4 is the diagonal sub-converse: classify the diagonal unitary matrices that preserve $L_4$.

The result, proved in [`../lean/StabilizerBW/Roots/AutL4aDiagonalUnitary.lean`](../lean/StabilizerBW/Roots/AutL4aDiagonalUnitary.lean): a unitary diagonal $D \in U(2) \otimes U(2)$ acting on the $4$-dimensional lattice $L_4$ as $\mathrm{diag}(\zeta_{16}^{k_1}, \zeta_{16}^{k_2})$ preserves $L_4$ if and only if

```math
k_1 \equiv k_2 \pmod 2.
```
The condition is parity, not full divisibility. Either $k_1$ and $k_2$ are both even (so $D$ is in fact diagonal in $\zeta_8$), or both odd. The naive strawman conjecture "$k_1 \equiv k_2 \pmod 8$" — which would force $D$ to be a scalar — is *strictly stronger* and *false*.

The witness for the parity rule is the matrix

```math
T_2 \;=\; \mathrm{diag}(1, \zeta_8) \;=\; \mathrm{diag}(\zeta_{16}^0, \zeta_{16}^2),
```
whose $k$-difference is $2$, not a multiple of $8$, but which is a known lattice automorphism of $L_4$ (it acts on the diagonal sub-lattice with the right determinant and the right denominator). The naive "$\pmod 8$" rule would forbid this. The correct rule "$\pmod 2$" allows it.

The cardinality count is

```math
\bigl| \mathrm{Aut}_{\mathrm{diag}}(L_4) \cap U(2)^{\otimes 2} \bigr| \;=\; 128 \;=\; 16 \cdot 8.
```
There are $16$ choices for $k_1 \in \mathbb{Z}/16$, and given $k_1$, exactly $8$ choices of $k_2 \in \mathbb{Z}/16$ with $k_2 \equiv k_1 \pmod 2$. The straightforward "$\pmod 8$" rule would have given $16 \cdot 2 = 32$, off by a factor of $4$.

## Where this fits

The qubit-level converse extends the Kliuchnikov–Schönnenbeck result on minimal vectors of Barnes–Wall lattices (see [References](references.md)) to the integral-of-coefficients setting, recovering the phased Clifford-24 group from the lattice structure alone. The half-$\sqrt{2}$ extension is the parity-conditioned form that pins the unique lattice-preserving Hadamard $\tilde H$. The level-4 diagonal converse is, to the best of our knowledge, the first kernel-checked parity-conditioned diagonal automorphism converse for $L_4$.

The full level-4 converse (without restriction to diagonal) is open and likely infeasible by enumeration. A useful structural intermediate step is the level-4 monomial automorphism group, which restricts to diagonals composed with permutation matrices; the kernel-clean treatment is queued for a separate development.

## What's new, what's borrowed

The classical reference for the level-3 unitary automorphism group is Kliuchnikov–Maslov–Mosca (2013) for the integral synthesis side, and Beverland et al. (2020) for the resource-theoretic side. The half-$\sqrt{2}$ rephasing $\tilde H = \zeta_8^{-1} H$ is implicit in Selinger 2015 *Generators and relations for Clifford+T* and made explicit by us at the lattice level. The level-4 diagonal parity rule is, to the author's knowledge, new at the kernel-checked level; the strawman counter-rule "$\pmod 8$" and its falsification via $T_2 = \mathrm{diag}(1, \zeta_8)$ is recorded as a publishable structural finding. The integral-grade-zero counterexample $\mathrm{diag}(1, 1 + \sqrt{2})$ is folklore in the cyclotomic-unit literature and is pinned here as the standing argument for why unitarity is required in the level-3 converse.
