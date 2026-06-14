# The grade

## The ring

Move from $\mathbb{Z}[i]$ to the slightly larger ring $\mathbb{Z}[\zeta_8] = \mathbb{Z}[x]/(x^4 + 1)$, where $\zeta_8 = e^{2\pi i/8}$ is a primitive eighth root of unity. The ring contains $i = \zeta_8^2$ and a new prime
$$
  \lambda \;=\; 1 - \zeta_8,
$$
the **totally ramified prime above 2**: the field norm $N(\lambda) = 2$ and $\lambda^4 = -2\zeta_8 + 6\zeta_8^2 - 4\zeta_8^3 = \text{(an associate of 2)}$. The single equality $(\lambda)^4 = (2)$ encodes everything about how the lattice tower handles the new resource ($T$ gate) introduced by Clifford+$T$.

## The grade

Let $L_3$ be the level-3 single-qubit Barnes–Wall lattice over $\mathbb{Z}[\zeta_8]$ — equivalently, $L_3 = \{(a, b) \in \mathbb{Z}[\zeta_8]^2 : (1 + i) \mid a + b\}$. For an integral single-qubit operator $M$ over $\mathbb{Z}[\zeta_8]$, define
$$
  g(M) \;=\; \min\bigl\{\,k : \lambda^k \cdot M \cdot L_3 \subseteq L_3\,\bigr\}.
$$
The grade is the lattice-theoretic cost of $M$. By construction $g$ is sub-multiplicative ($g(MN) \le g(M) + g(N)$), respects adjoints, and vanishes precisely on lattice automorphisms — the Clifford fragment.

Three benchmark values, kernel-verified:
$$
  g(Z) = g(S) = g(\tilde H) = 0, \qquad g(T) = 1.
$$
The $T$ gate sits at grade exactly $1$: it is the cheapest non-Clifford operator the level-3 lattice can see. Longer Clifford+$T$ circuits accumulate grade only by their $T$-count, never by the Clifford parts or by composition.

## Diagonal characters and the closed form

A **diagonal character** on $n$ qubits is an operator $D_e\,\lvert x\rangle = \zeta_8^{e(x)}\lvert x\rangle$ for some function $e\colon \mathbb{F}_2^n \to \mathbb{Z}_8$. Write the function as a multilinear polynomial $e(x) = c \cdot x_S$ where $S \subseteq \{1, \dots, n\}$ is its support and $c \in \mathbb{Z}/8\mathbb{Z}$ its eighth-root coefficient. For these **single-monomial** characters there is a closed form for the grade at the level-$n$ Barnes–Wall lattice:
$$
  g\bigl(D_{c\,x_S}\bigr) \;=\; \max\bigl(0,\;2|S| - 2^{\nu_2(c)}\bigr),
$$
where $\nu_2(c)$ is the 2-adic valuation of $c$ taken mod 8. Examples:

| character | $|S|$ | $c$ | formula | grade |
|-----------|-------|-----|---------|-------|
| $S$       | 1 | 2 | $\max(0, 2 - 2) = 0$ | 0 |
| $T$       | 1 | 1 | $\max(0, 2 - 1) = 1$ | 1 |
| $CZ$      | 2 | 4 | $\max(0, 4 - 4) = 0$ | 0 |
| $CS$      | 2 | 2 | $\max(0, 4 - 2) = 2$ | 2 |
| $cT$      | 2 | 1 | $\max(0, 4 - 1) = 3$ | 3 |
| $CCZ$     | 3 | 4 | $\max(0, 6 - 4) = 2$ | 2 |
| $CCS$     | 3 | 2 | $\max(0, 6 - 2) = 4$ | 4 |
| $ccT$     | 3 | 1 | $\max(0, 6 - 1) = 5$ | 5 |
| $cccT$    | 4 | 1 | $\max(0, 8 - 1) = 7$ | 7 |

The upper-bound half — $g(D_{c\,x_S}) \le \max(0, 2|S| - 2^{\nu_2(c)})$ — is proved at every $n$ by factoring the character through a projector. The lower-bound half is proved at every $n$ for the maximal monomial ($|S| = n$) and every $\nu_2(c) \in \{0, 1, 2\}$, by exhibiting a witness vector. For strict-subset monomials ($|S| < n$) at general $n$, the linear closed form is verified by direct kernel computation at $n \le 4$ and routed for general $n$ through a structured induction.

## The $T$-count corollary

For a word $w$ over the integral generator set $\{S, X, T\}$ on a fixed number of qubits, $g(\llbracket w\rrbracket) \le \#T(w)$, with equality on $w = T$. This is the **$T$-count lower bound**: a circuit cannot denote a gate of grade $g$ using fewer than $g$ instances of $T$.

## What's proved

* Single-qubit grade infrastructure: $\mathbb{Z}[\zeta_8]$, $\lambda$, $\lambda$-adic valuation, single-qubit grade `grade`, `grade_mul`, `grade_adj`, `grade_eq_zero_iff` — [`../lean/Arithmetic/Roots/Matrices.lean`](../lean/Arithmetic/Roots/Matrices.lean), `Z8.lean`.
* The two-qubit Barnes–Wall lattice $\mathrm{BW}_2$ with decidable membership, and the kernel-verified diagonal table $g(CZ) = 0$, $g(T \otimes I) = 1$, $g(CS) = 2$, $g(T \otimes T) = 2$, $g(cT) = 3$ — [`../lean/Arithmetic/Roots/BW2.lean`](../lean/Arithmetic/Roots/BW2.lean), `Tensor.lean`.
* Three- and four-qubit grades, including the kernel-verified $g(ccT) = 5$ and $g(cccT) = 7$ — `BW3.lean`, `BW4.lean`.
* The general-$n$ upper bound $g(D_{c\,x_S}) \le \max(0, 2|S| - 2^{\nu_2(c)})$ — `UpperBoundAllN.lean`.
* The maximal-monomial lower bound at every $n$ and every $\nu_2(c) \in \{0, 1, 2\}$ — `LowerBoundAllN.lean`.
* The strict-subset lower bound — `StrictSubsetLowerBoundAllN.lean`.
* Multi-monomial closed-form data and the refutation of the Reed–Muller leading-degree formula — `MultimonomialClosedForm.lean`, `MoebiusClosedFormAllN.lean`.
* Cross-level self-similarity grounded in $g(T) = 1$ — `CrossLevelSelfSimilarity.lean`.
* The Haskell layer reproduces the closed-form upper bound and the named-character table; it also exposes basic $\mathbb{Z}[\zeta_8]$ arithmetic with the $\lambda$-adic valuation. See [`../haskell/src/Cyclotomic.hs`](../haskell/src/Cyclotomic.hs) and [`../haskell/src/Grade.hs`](../haskell/src/Grade.hs).

## What is in the literature

The cyclotomic ring $\mathbb{Z}[\zeta_8]$ and its use in exact synthesis are standard (Forest–Gosset–Kliuchnikov–McKinnon 2015; Amy–Glaudell–Ross 2020). Certified $T$-count floors via stabilizer-rank or nullity-style invariants appear in Beverland et al. 2020 and Jiang–Wang 2023.

The $\lambda$-adic grade as a lattice invariant of Clifford+$T$ operators, the explicit closed-form upper bound for single-monomial diagonal characters, the level-raising identity (cyclotomic doubling = ramified step), and the cross-level table are this development's contribution.
