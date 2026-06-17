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

The upper-bound half — that the grade is at most $\max(0, 2d - 2^{\nu_2(c)})$ — is proved at every *n* by factoring the character through a projector whose cost is computable, and we close that proof in the Lean source [`../lean/StabilizerBW/Roots/UpperBoundAllN.lean`](../lean/StabilizerBW/Roots/UpperBoundAllN.lean). The lower-bound half is proved at every *n* for the maximal monomial $d = n$ and every $\nu_2(c) \in \{0, 1, 2\}$, by exhibiting an explicit vector that fails to be in the lattice after the predicted scaling. For strict-subset monomials $d < n$, the same identity is proved at every *n* in [`../lean/StabilizerBW/Roots/StrictSubsetLowerBoundAllN.lean`](../lean/StabilizerBW/Roots/StrictSubsetLowerBoundAllN.lean), via the canonical leading-$d$ placement and the sub-coordinate conductor lemma `topProj_inBW_iff`.

## The *T*-count corollary

The closed form gives a syntactic *T*-count lower bound. For a circuit word *w* over the integral Clifford+*T* generator set $\{S, X, T\}$ — fix the qubit count — the grade of the denoted operator is at most the number of *T* letters in *w*, with equality on $w = T$. So a circuit cannot denote an operator of grade *g* using fewer than *g* instances of *T*. This is the certified-floor reading of the grade. It applies on the integral fragment; the half-integral version that handles Hadamard is bookkeeping for a later pass.

## Multi-monomial characters

Single monomials are the cleanest case. The general diagonal character $e(x)$ is a sum of monomials, and the grade does not in general satisfy a simple monomial-by-monomial formula. Disjoint-support additivity holds when the monomials live on disjoint coordinates — $g(D_{x_1 \cdot x_2 + x_3}) = g(cT) + g(T) = 3 + 1 = 4$ at *n* = 3, for instance — but overlapping supports trigger inclusion-exclusion-style depression that the single-monomial formula does not anticipate. The kernel sources `MultimonomialClosedForm.lean` and `MoebiusClosedFormAllN.lean` record the data and the Möbius/finite-difference closed form that does hold. We also record the explicit refutation of the natural-looking Reed–Muller leading-degree candidate, which fits the *n* = 2 data and breaks at *n* = 3.

## A closed-form enumerator on linear phases

On the *linear-phase stratum* — phase polynomials of degree at most one in the input bits — the grade collapses to the per-monomial *T*-count. Writing $P(x) = c_0 + \sum_i c_i x_i$ with $c_i \in \mathbb{Z}/8$, the grade $g(D_P)$ equals the count of *T*-flavoured generators, i.e. the number of coefficients $c_i$ that are odd modulo two:
```math
g(D_P) = \#\{i : c_i \text{ is odd}\}.
```
The bivariate generating function over all linear phases at level *m* factorises along the qubits: each $c_0 \in \mathbb{Z}/8$ contributes a factor of 8 (eight choices, all of grade 0); each $c_i \in \mathbb{Z}/8$ contributes $4 + 4z$ (four even choices and four odd, weighted by $z^0$ and $z^1$). Multiplying through,
```math
\sum_{P : \deg P \le 1} z^{g(D_P)} = 8 \cdot (4 + 4z)^m = 8 \cdot 4^m \cdot (1 + z)^m.
```
This is the kernel-checked headline of [`../lean/StabilizerBW/T1A/`](../lean/StabilizerBW/T1A/).

## Off the linear stratum: grade is not the *T*-count

A natural conjecture extrapolates the linear identity to all phase polynomials: the grade should equal the syntactic per-monomial *T*-count, summed over all monomial supports $S \subseteq \{1, \dots, n\}$. This is *false*. The smallest disagreement sits at *n* = 3 with the phase polynomial $x_1 x_2 + x_1 x_3$: the per-monomial *T*-count is six, but the Barnes–Wall grade is four. Two units of *T*-count are absorbed by the overlap on $x_1$. The correct invariant is the Möbius/finite-difference transform of the previous section, which weighs the down-set of overlapping monomials with alternating signs and recovers the true grade on the full multi-monomial cube.

## The same closed form from coding theory

The factorised $8 \cdot 4^m \cdot (1 + z)^m$ also appears on the *coding-theory* side of the Barnes–Wall tower, where there are no phase polynomials at all. We build a small CSS-code family from a Reed–Muller pair.

A binary Reed–Muller code $\mathrm{RM}(r, m)$ has block length $2^m$, dimension $\sum_{i \le r} \binom{m}{i}$, and minimum distance $2^{m - r}$. The duality identity $\mathrm{RM}(r, m)^\perp = \mathrm{RM}(m - r - 1, m)$ implies that for any pair $r_2 < r_1$ with $r_1 + r_2 \le m - 1$, the inclusion
```math
\mathrm{RM}(r_2, m) \subseteq \mathrm{RM}(r_1, m)^\perp
```
is satisfied. This is exactly the *CSS condition* that turns two classical codes into a quantum stabilizer code. We take the Calderbank–Shor–Steane construction with $C_2 := \mathrm{RM}(r_2, m)$ as the *X*-stabilizer and $C_1 := \mathrm{RM}(r_1, m)$ as the *Z*-stabilizer, and call the resulting code $\mathrm{BWCss}(m, r_1, r_2)$. Its parameters are
```math
n = 2^m, \quad k = \sum_{r_2 < i \le r_1} \binom{m}{i}, \quad d = 2^{m - r_1}.
```
Setting $(m, r_1, r_2) = (3, 1, 0)$ recovers the extended Hamming-CSS code $[[8, 3, 4]]$ (parent of the Steane code by one puncture); $(4, 2, 0)$ recovers the standard $[[16, 10, 4]]$; $(4, 2, 1)$ and $(5, 2, 1)$ give $[[16, 6, 4]]$ and $[[32, 10, 8]]$.

The grade-refined enumerator of the family — counting logical-X representatives by their grade rather than their Hamming weight — factorises into the same closed form $8 \cdot 4^m \cdot (1 + X)^m$ that we derived combinatorially above. Two independent paths reach the same expression: one from the $\lambda$-adic arithmetic of $\mathbb{Z}[\zeta_8]$, one from binary linear algebra in $\mathbb{F}_2^{2^m}$.

The arithmetic and coding-theoretic readings are not the same proof. The Lean module [`../lean/StabilizerBW/BWCss/Grade.lean`](../lean/StabilizerBW/BWCss/Grade.lean) closes the closed-form identity unconditionally on the grade enumerator of phase polynomials of degree at most one; the *logical*-operator enumerator of $\mathrm{BWCss}(m, r_1, r_2)$ equals the same expression provided one accepts the standard identification of the CSS logical-X coset structure with the grade-1 phase-polynomial stratum, carried in that file as a named hypothesis. The structural convergence is the substantive thing: same closed form, different objects, same combinatorial skeleton.

## What's here and where

The arithmetic of $\mathbb{Z}[\zeta_8]$ and $\lambda$ — the addition, multiplication, $\lambda$-adic valuation — is the Haskell module [`../haskell/src/Cyclotomic.hs`](../haskell/src/Cyclotomic.hs). The closed-form upper bound and the named-character table are [`../haskell/src/Grade.hs`](../haskell/src/Grade.hs); the demo in `Main.hs` cross-checks every row of the table against the formula. The Lean side carries the formal proofs: single-qubit grade infrastructure in [`Matrices.lean`](../lean/StabilizerBW/Roots/Matrices.lean), the two-qubit kernel-verified diagonal table in `BW2.lean`, the three- and four-qubit grades in `BW3.lean` and `BW4.lean`, the all-*n* upper bound in `UpperBoundAllN.lean`, the lower-bound machinery in `LowerBoundAllN.lean` and `StrictSubsetLowerBoundAllN.lean`, the cross-level self-similarity in `CrossLevelSelfSimilarity.lean`, the multi-monomial Möbius closed form in `MultimonomialClosedForm.lean` and `MoebiusClosedFormAllN.lean`, the linear-phase grade enumerator in `T1A/`, and the Reed–Muller CSS construction in `BWCss/`.

## What's new, what's borrowed

The cyclotomic ring $\mathbb{Z}[\zeta_8]$ and its use in exact synthesis are standard, going back to Forest–Gosset–Kliuchnikov–McKinnon (2015) and Amy–Glaudell–Ross (2020). Certified *T*-count floors via stabilizer-rank or unitary-stabilizer-nullity invariants appear in Beverland et al. (2020) and Jiang–Wang (2023). What we add is the $\lambda$-adic grade itself, the explicit closed form for single-monomial characters, the all-*n* upper bound, the level-raising identity (one cyclotomic doubling = one ramified step), and the cross-level table; the Möbius closed form, the maximal-monomial lower bound at every $\nu$, and the strict-subset lower bound, all of which are recorded with the kernel proofs that establish them; the closed-form generating function on linear phases and its CSS-side recovery from a Reed–Muller pair.
