# The grade

So far everything has been over $\mathbb{Z}[i]$, which is the right ring for Clifford. The *T* gate breaks this: it has the entry $\zeta_8 = e^{i\pi/4}$, which is not in $\mathbb{Z}[i]$. To say anything about Clifford+*T* we have to move up the cyclotomic tower one step, to $\mathbb{Z}[\zeta_8] = \mathbb{Z}[x] / (x^4 + 1)$. The new ring contains $\mathbb{Z}[i]$ (since $\zeta_8^2 = i$), and the new prime that matters is
```math
\lambda = 1 - \zeta_8,
```
the totally ramified prime above two. The norm $N(\lambda) = 2$, and $(\lambda)^4 = (2)$ — the four conjugates of $\lambda$ multiply to a unit times $2$. The single equation $(\lambda)^4 = (2)$ is the arithmetic that organises the *T*-side of the theory.

## What "grade" means

The Barnes–Wall lattice at this level is $L_3 = \{(a, b) \in \mathbb{Z}[\zeta_8]^2 : (1 + i) \mid a + b\}$ — the single-qubit lattice over the new ring. For an integral single-qubit operator *M* with entries in $\mathbb{Z}[\zeta_8]$, the *grade* of *M* is
```math
g(M) = \min\{\,k \ge 0 : \lambda^k \cdot M \cdot L_3 \subseteq L_3\,\}.
```
In words: how many factors of the prime $\lambda$ does it take to pull *M* into the lattice? The grade is the lattice-theoretic cost of the operator.

By construction $g$ is sub-multiplicative — $g(MN) \le g(M) + g(N)$ — and respects adjoints. It vanishes on lattice automorphisms, which is to say on the Clifford fragment. Three benchmark values, kernel-verified: $g(Z) = g(S) = g(\tilde H) = 0$ and $g(T) = 1$. The *T* gate sits at grade exactly one. It is the cheapest non-Clifford operator the level-3 lattice sees, and longer Clifford+*T* circuits accumulate grade only by their *T* count: never by their Clifford parts, never by composition slack. The grade is a *T*-count lower bound.

## A closed form for diagonal characters

A diagonal character on *n* qubits is an operator that acts on each computational basis vector by an eighth-root phase:
```math
D_e \cdot |x\rangle = \zeta_8^{e(x)} |x\rangle, \qquad e \colon \mathbb{F}_2^n \to \mathbb{Z}/8\mathbb{Z}.
```
Writing $e(x)$ as a multilinear polynomial in the bits and isolating a single monomial $c \cdot x_S$ (with support $S \subseteq \{1, \dots, n\}$ and eighth-root coefficient $c \bmod 8$), the grade of the corresponding character has an explicit closed form:
```math
g(D_{c\,x_S}) = \max\bigl(0,\ 2d - 2^{\nu_2(c)}\bigr),
```
where $d = |S|$ is the support size and $\nu_2(c)$ is the 2-adic valuation of $c \bmod 8$. The closed form is sharp on every named single-monomial character we know how to check.

| character | $d$ | $c$ | formula | grade |
|---|---|---|---|---|
| $S$ | 1 | 2 | $\max(0, 2-2)=0$ | 0 |
| $T$ | 1 | 1 | $\max(0, 2-1)=1$ | 1 |
| $CZ$ | 2 | 4 | $\max(0, 4-4)=0$ | 0 |
| $CS$ | 2 | 2 | $\max(0, 4-2)=2$ | 2 |
| $cT$ | 2 | 1 | $\max(0, 4-1)=3$ | 3 |
| $CCZ$ | 3 | 4 | $\max(0, 6-4)=2$ | 2 |
| $CCS$ | 3 | 2 | $\max(0, 6-2)=4$ | 4 |
| $ccT$ | 3 | 1 | $\max(0, 6-1)=5$ | 5 |
| $cccT$ | 4 | 1 | $\max(0, 8-1)=7$ | 7 |

The upper-bound half — that the grade is at most $\max(0, 2d - 2^{\nu_2(c)})$ — is proved at every *n* by factoring the character through a projector whose cost is computable, and we close that proof in the Lean source [`../lean/Arithmetic/Roots/UpperBoundAllN.lean`](../lean/Arithmetic/Roots/UpperBoundAllN.lean). The lower-bound half is proved at every *n* for the maximal monomial $d = n$ and every $\nu_2(c) \in \{0, 1, 2\}$, by exhibiting an explicit vector that fails to be in the lattice after the predicted scaling. For strict-subset monomials $d < n$ at general *n*, the formula is verified by direct kernel computation at $n \le 4$ and routed for general *n* through a structured induction.

## The *T*-count corollary

The closed form gives a syntactic *T*-count lower bound. For a circuit word *w* over the integral Clifford+*T* generator set $\{S, X, T\}$ — fix the qubit count — the grade of the denoted operator is at most the number of *T* letters in *w*, with equality on $w = T$. So a circuit cannot denote an operator of grade *g* using fewer than *g* instances of *T*. This is the certified-floor reading of the grade. It applies on the integral fragment; the half-integral version that handles Hadamard is bookkeeping for a later pass.

## Multi-monomial characters

Single monomials are the cleanest case. The general diagonal character $e(x)$ is a sum of monomials, and the grade does not in general satisfy a simple monomial-by-monomial formula. Disjoint-support additivity holds when the monomials live on disjoint coordinates — $g(D_{x_1 \cdot x_2 + x_3}) = g(cT) + g(T) = 3 + 1 = 4$ at *n* = 3, for instance — but overlapping supports trigger inclusion-exclusion-style depression that the single-monomial formula does not anticipate. The kernel sources `MultimonomialClosedForm.lean` and `MoebiusClosedFormAllN.lean` record the data and the Möbius/finite-difference closed form that does hold. We also record the explicit refutation of the natural-looking Reed–Muller leading-degree candidate, which fits the *n* = 2 data and breaks at *n* = 3.

## What's here and where

The arithmetic of $\mathbb{Z}[\zeta_8]$ and $\lambda$ — the addition, multiplication, $\lambda$-adic valuation — is the Haskell module [`../haskell/src/Cyclotomic.hs`](../haskell/src/Cyclotomic.hs). The closed-form upper bound and the named-character table are [`../haskell/src/Grade.hs`](../haskell/src/Grade.hs); the demo in `Main.hs` cross-checks every row of the table against the formula. The Lean side carries the formal proofs: single-qubit grade infrastructure in [`Matrices.lean`](../lean/Arithmetic/Roots/Matrices.lean), the two-qubit kernel-verified diagonal table in `BW2.lean`, the three- and four-qubit grades in `BW3.lean` and `BW4.lean`, the all-*n* upper bound in `UpperBoundAllN.lean`, the lower-bound machinery in `LowerBoundAllN.lean` and `StrictSubsetLowerBoundAllN.lean`, the cross-level self-similarity in `CrossLevelSelfSimilarity.lean`, and the multi-monomial closed-form data in `MultimonomialClosedForm.lean` and `MoebiusClosedFormAllN.lean`.

## What's new, what's borrowed

The cyclotomic ring $\mathbb{Z}[\zeta_8]$ and its use in exact synthesis are standard, going back to Forest–Gosset–Kliuchnikov–McKinnon (2015) and Amy–Glaudell–Ross (2020). Certified *T*-count floors via stabilizer-rank or unitary-stabilizer-nullity invariants appear in Beverland et al. (2020) and Jiang–Wang (2023). What we add is the $\lambda$-adic grade itself, the explicit closed form for single-monomial characters, the all-*n* upper bound, the level-raising identity (one cyclotomic doubling = one ramified step), and the cross-level table; the Möbius closed form, the maximal-monomial lower bound at every $\nu$, and the strict-subset lower bound are recorded with the kernel proofs that establish them.
