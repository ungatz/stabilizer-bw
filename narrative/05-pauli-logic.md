# Pauli logic

## The calculus $\mathsf{PL}_n$

Fix $n \ge 1$. The **literals** of $\mathsf{PL}\_{n}$ are signed Pauli words on $n$ qubits: triples $(\sigma, x, z)$ where $\sigma \in \{+, -\}$ and $x, z \in \mathbb{F}_2^n$ encode the $X$- and $Z$-content. The **multiplication** of literals is the symplectic product on $\mathbb{F}_2^{2n}$ paired with the sign rule that tracks the $i$-exponent of the underlying Pauli product. Two literals commute when their symplectic form vanishes.

The sequents of $\mathsf{PL}\_{n}$ have the shape $\Gamma \vdash P$, where $\Gamma$ is a finite list of literals (the **stabilizer theory**) and $P$ is one literal. The proof rules are:

* **(Ax)** $\Gamma \vdash \Gamma_k$ — the $k$-th element of $\Gamma$.
* **(Mul)** If $\Gamma \vdash P$ and $\Gamma \vdash Q$ and $P, Q$ commute, then $\Gamma \vdash P \cdot Q$.
* **(UnitI)** $\Gamma \vdash +I$.
* **(Cut)** If $\Gamma \vdash P$ and $\Gamma, P \vdash Q$, then $\Gamma \vdash Q$.

The (Mul) rule has a commutativity side condition because the product of two anticommuting Hermitian Paulis is not Hermitian.

## Soundness

A literal $P$ is **valid in** a theory $\Gamma$ when every common eigenvector of $\Gamma$ with eigenvalue $+1$ is a $+1$-eigenvector of $P$. Equivalently: the codespace of $\Gamma$ lies inside the $+1$-eigenspace of $P$. The four rules above are sound for validity in this sense.

## Cut elimination

Every derivation in $\mathsf{PL}\_{n}$ normalises to a cut-free derivation in linear time. The cut-free derivations of a literal $Q$ from $\Gamma$ are in bijection with **subset-product certificates**: subsets $T \subseteq \{1, \dots, m\}$ (with $m$ the size of $\Gamma$) such that $Q = \prod_{k \in T} \Gamma_k$, the multiplication evaluated in any order with signs tracked by the $i$-exponent.

The cut-elimination procedure is, literally, the row-multiplication of stabilizer tableau algorithms (Aaronson–Gottesman 2004). Splicing the proof of the cut formula into every reference of it in the right premise is one constant-time tableau update; the total cost is linear in the proof DAG.

Tableau reduction in the conventional sense — taking a generating set for a stabilizer group and reducing it to row-echelon form — corresponds to **proof search** in $\mathsf{PL}\_{n}$: starting from a theory, decide whether $\Gamma \vdash Q$ by greedy support-reducing row multiplications. This is the $O(n^2)$ step of the Aaronson–Gottesman algorithm, read as entailment checking.

## Measurement

Measurement is the only place the logic interacts with non-deterministic data. A literal $q$ is measured against a maximal theory $\Gamma$:

* If $q$ commutes with every generator of $\Gamma$, then $\Gamma \vdash q$ or $\Gamma \vdash -q$ (entailment is decidable); the outcome is deterministic and the theory is unchanged.
* Otherwise, the outcome is a fair coin flip $r \in \{+, -\}$, and the theory updates: pick any generator $g_1$ anticommuting with $q$, replace it by $(-1)^r q$, and multiply every other anticommuting generator by $g_1$ to restore commutativity.

In Haskell, the coin flip is the **only effect** in the entire stabilizer simulator. It is exposed as a free monad over a single operation `FlipCoin :: (Bool -> k) -> MeasF k`; everything else is pure proof normalisation. See [`../haskell/src/PauliLogic.hs`](../haskell/src/PauliLogic.hs).

## What's proved

* Syntax, rules, and the soundness theorem — [`../lean/PauliLogic/Syntax.lean`](../lean/PauliLogic/Syntax.lean), `Rules.lean`, `Soundness.lean`.
* Cut elimination as a total recursive function `normalize`, and the corresponding tableau reduction — [`../lean/PauliLogic/CutElimination.lean`](../lean/PauliLogic/CutElimination.lean) and `Tableau.lean`. The Aaronson–Gottesman tableau-step correspondence (`tableau_step_eq_mul`) is kernel-checked there.
* The Haskell layer realises the data type, cut elimination, the tableau search, and the measurement effect; running `Main.hs` derives $XX$ from $\{XI, IX\}$, checks the certificate via cut elimination, and runs a small Bell-state measurement sequence.

## What is in the literature

The signed-Pauli / symplectic representation, the row multiplication rule, and the tableau update for measurement are standard (Aaronson–Gottesman 2004; the CHP algorithm). The presentation as a sequent calculus, the cut-elimination theorem (with its identification with tableau reduction at linear cost), and the measurement-as-algebraic-effect reading are this development's contribution. The soundness theorem is stated and proved in this repository.

The arithmetic-side reading — every (Mul) step is one factor of $\varphi$ in the lattice semantics — is the bridge to the grade story of [`06-grade.md`](06-grade.md): a derivation of length $\ell$ in $\mathsf{PL}\_{n}$ corresponds to a coordinate move that loses $\ell$ factors of $\varphi$. This bridge is why the logical-lattice theorem of [`03-logical-lattice.md`](03-logical-lattice.md) supplies the lattice semantics of $\mathsf{PL}\_{n}$, with the denotation of a sequent a containment of constraint sublattices.
