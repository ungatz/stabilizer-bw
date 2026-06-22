# Cyclotomic arithmetic and the √Π dictionary

The grade picture in chapter 06 took $\mathbb{Z}[\zeta_8]$ and the totally ramified prime $\lambda = 1 - \zeta_8$ as given. This chapter sits one level down and asks what the right ring is, why $\lambda$ is the right local parameter, and what the Carette–Heunen–Kaarsgaard–Sabry $\sqrt{\Pi}$ language has to do with all of it. The short answer is that the cyclotomic tower $\mathbb{Z}[i] \subset \mathbb{Z}[\zeta_8] \subset \mathbb{Z}[\zeta_{16}] \subset \cdots$ is the same tower as $\Pi \to \sqrt{\Pi} \to \sqrt[4]{\Pi} \to \cdots$: each square-root step is a ramified extension at the prime above two, and the $\lambda$-adic valuation is the depth in that tower.

## The cyclotomic tower

The starting ring is the Gaussian integers $\mathbb{Z}[i] = \mathbb{Z}[\zeta_4]$. The rational prime $2$ ramifies in $\mathbb{Z}[i]$ as $(2) = (1 + i)^2$ up to a unit. Climbing the tower one step to $\mathbb{Z}[\zeta_8] = \mathbb{Z}[\zeta_4][\sqrt{i}]$, the prime $(1 + i)$ ramifies further: writing $\lambda = 1 - \zeta_8$,
```math
(1 + i) = (\lambda)^2 \cdot u
```
for a unit $u \in \mathbb{Z}[\zeta_8]^\times$. Composing the two steps, $(2) = (\lambda)^4 \cdot u'$ for a unit $u'$. The single prime above $2$ at this level is $\lambda$; its residue field is $\mathbb{F}_2$; its ramification index over $\mathbb{Q}$ is $4$. The $\lambda$-adic valuation $v_\lambda \colon \mathbb{Z}[\zeta_8] \setminus \{0\} \to \mathbb{Z}_{\ge 0}$ counts the factors of $\lambda$ in a non-zero element, and $v_\lambda(2) = 4$, $v_\lambda(1 + i) = 2$, $v_\lambda(\zeta_8 - 1) = 1$.

The next level up is $\mathbb{Z}[\zeta_{16}] = \mathbb{Z}[\zeta_8][\sqrt{\zeta_8}]$. The unique prime above $2$ at this level is $1 - \zeta_{16}$; its ramification index over $\mathbb{Q}$ is $8$; and one has $(1 - \zeta_{16})^2 = \lambda \cdot u''$ for another unit $u''$. The pattern continues: each cyclotomic doubling $\mathbb{Z}[\zeta_{2^m}] \to \mathbb{Z}[\zeta_{2^{m+1}}]$ doubles the ramification index above $2$ and halves the value of the local parameter on the previous level's parameter.

## Why $\lambda$ is the right local parameter

For the Barnes–Wall lattice $L_3 \subset \mathbb{Z}[\zeta_8]^2$ from chapter 01, a $\mathbb{Z}[\zeta_8]$-linear endomorphism $M$ has integer entries but need not preserve $L_3$. The obstruction is exactly local at $\lambda$: there exists a non-negative integer $k$ such that $\lambda^k \cdot M$ preserves $L_3$, and the smallest such $k$ is the grade $g(M)$.

This is not an accident of the lattice. The relevant fact is that $L_3$ is a finitely generated free $\mathbb{Z}[\zeta_8]$-module of rank one in $\mathbb{Z}[\zeta_8]^2$, and the question "does $M$ preserve $L_3$?" reduces, after localising at every prime, to a question at the single prime $\lambda$ — every other prime of $\mathbb{Z}[\zeta_8]$ is unramified and contributes no obstruction. The level-3 grade is therefore the $\lambda$-adic depth of $M$, computed by the formula $g(M) = -v_\lambda(\det \text{lift})$ on the canonical lift to lattice generators.

The same statement at level $m$ replaces $\lambda$ by the parameter $\lambda_m = 1 - \zeta_{2^{m+1}}$, and the grade becomes $g_m(M) = -v_{\lambda_m}(\det \text{lift}_m)$. The level-raising identity is

```math
g_{m+1}(\Phi(M)) = g_m(M)
```
for the standard cyclotomic embedding $\Phi \colon L_m \hookrightarrow L_{m+1}$, kernel-verified for the level-3-to-level-4 step in [`../lean/StabilizerBW/Roots/CrossLevelSelfSimilarity.lean`](../lean/StabilizerBW/Roots/CrossLevelSelfSimilarity.lean). One cyclotomic doubling is one ramified step.

## The $\sqrt{\Pi}$ dictionary

The Carette–Heunen–Kaarsgaard–Sabry language treats $\sqrt{\Pi}$ as the type system whose values are square roots of permutations: a programming-language object $V$ with $V^2 = \pi$ for a fixed permutation $\pi$. Read concretely at the qubit, the canonical generator is the controlled square root $V = \sqrt{\mathrm{SWAP}}$, satisfying $V^2 = \mathrm{SWAP}$ and acting unitarily on $\mathbb{C}^2 \otimes \mathbb{C}^2$. The lattice-side reading translates this to one specific cyclotomic identity.

Define $V := H S H$ at the single qubit. Then a direct matrix computation gives $V^2 = X$, $S V S = \zeta_8 \cdot \tilde H$ (with $\tilde H = \zeta_8^{-1} H$ the lattice-preserving Hadamard rephasing), and the central identity

```math
(1 - \zeta_8)^2 \;=\; (1 + i) \cdot \mathrm{unit}.
```
The dictionary lines up: $V$, $V^2$, and $S V S$ are exactly the three lattice-preserving Clifford operators visible from the $\sqrt{\Pi}$ side, and the algebraic identity $(1 - \zeta_8)^2 \sim (1 + i)$ is the explicit residue-field-of-characteristic-two identity that makes $\sqrt{\cdot}$ behave as a ramified extension at the prime above two.

The benchmark grades drop out of the dictionary directly:

| operator | role in $\sqrt{\Pi}$ | grade |
|---|---|---|
| $X$ | the underlying permutation $\pi$ | $0$ |
| $V = H S H$ | $\sqrt{\pi}$ at level 3 | $0$ |
| $S V S = \zeta_8 \tilde H$ | conjugate of $V$ | $0$ |
| $S$ | second cube root, $S^4 = I$ | $0$ |
| $T$ | first $\zeta_8$-phase, $T^8 = I$ | $1$ |

The $\sqrt{\Pi}$ generators all sit at grade zero — they preserve the lattice unconditionally because $V, V^2, S V S$ are all in the unitary automorphism group of $L_3$. The first non-zero-grade entry is $T$, the eighth-root phase gate that breaks the lattice automorphism property by exactly one factor of $\lambda$.

## Square roots are ramified extensions

The deeper reading is that taking square roots in the qubit world is the same operation as taking square roots in the cyclotomic ring. The $\sqrt{\Pi}$-language requirement that one can iterate $\pi \to \sqrt{\pi} \to \sqrt[4]{\pi} \to \cdots$ matches the cyclotomic tower's allowance of $\zeta_{2^m} \to \zeta_{2^{m+1}}$: each iteration is a ramified extension of degree two at the unique prime above two. The Lean module [`../lean/StabilizerBW/SqrtPi/`](../lean/StabilizerBW/SqrtPi/) records the dictionary as a sequence of kernel-checked identities, including $V = H S H$ at the matrix level, $V^2 = X$, $(1 - \zeta_8)^2 = (1 + i) \cdot u$ for an explicit unit $u$, and the grade-zero status of $V, V^2, S V S$ on $L_3$.

The conjecture that motivated the $\sqrt{\Pi}$ language — that square roots can be iterated as a programming primitive — is then explained by the cyclotomic tower: the operation is iterable exactly because the tower is infinite, with one ramified prime at each level, and the depth of an operator in the tower is its grade.

## Units, the unit group, and the integral converse

The unit group of $\mathbb{Z}[\zeta_8]$ has rank one as an abelian group: it is $\{\pm \zeta_8^k\} \times (1 + \sqrt{2})^{\mathbb{Z}}$, where the cyclotomic units $\pm \zeta_8^k$ form a finite torsion subgroup of order $8$, and the fundamental unit $1 + \sqrt{2}$ generates a free $\mathbb{Z}$ of infinite rank. Concretely, $1 + \sqrt{2} = 1 + (\zeta_8 + \zeta_8^{-1}) \in \mathbb{Z}[\zeta_8]^\times$ has $\lambda$-adic valuation zero (it is a unit), so multiplying any operator by $1 + \sqrt{2}$ does not change its grade.

This observation has a bite. The naive integral converse to the grade-zero theorem — "every integral grade-zero endomorphism of $L_3$ is Clifford" — is *false*. The diagonal matrix $\mathrm{diag}(1, 1 + \sqrt{2})$ is integral, grade zero, but not unitary, and so is not in any Clifford group. Unitarity is essential to the converse. The correct statement is the kernel-checked

> Every *unitary* integral grade-zero endomorphism of $L_3$ is in the phased Clifford group $\{\pm \zeta_8^k\} \cdot \mathrm{Clifford}_1$.

The corresponding cardinality count $|\mathrm{Clifford}_{1,\text{phased}}| = 24$ is recovered as a permutation action of the lattice-preserving Hadamard $\tilde H$ and the phase generator $S$.

## What's new, what's borrowed

The cyclotomic tower $\mathbb{Z}[\zeta_{2^m}]$ and its ramification structure at the prime above two are classical — the standard reference for the local arithmetic at $\lambda$ is Hardy–Wright, *An Introduction to the Theory of Numbers*, chapter XV. The use of $\mathbb{Z}[\zeta_8]$ in exact synthesis is in Kliuchnikov–Maslov–Mosca (2013) and in the survey form of Selinger (2013). The $\sqrt{\Pi}$ language is Carette–Heunen–Kaarsgaard–Sabry (POPL 2024). What this repository adds, on the arithmetic-and-square-root side, is the explicit identification of the level-$m$ grade with the $\lambda_m$-adic valuation on lift determinants, the level-raising identity $g_{m+1}(\Phi(M)) = g_m(M)$, the explicit kernel-checked $\sqrt{\Pi}$ dictionary at level 3, and the counterexample $\mathrm{diag}(1, 1 + \sqrt{2})$ that pins the unitarity hypothesis in the grade-zero converse.
