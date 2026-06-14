# Pauli logic

Stabilizer circuit simulation has a beautiful little algorithm at its heart — Aaronson and Gottesman's tableau update — and a beautiful little observation about what that algorithm is doing. The observation is that the tableau update is cut elimination. The Pauli words are propositions; the stabilizer groups are theories; the Aaronson–Gottesman row operations are the rules of a sequent calculus. We call this calculus $\mathsf{PL}\_{n}$.

## Literals and theories

Fix *n* qubits. The literals of $\mathsf{PL}\_{n}$ are signed Pauli words: triples $(\sigma, x, z)$ with $\sigma \in \{+, -\}$ a sign and $x, z \in \mathbb{F}_2^n$ encoding the *X*- and *Z*-content qubit by qubit. The multiplication of two literals — read as Pauli operators — combines the bit vectors by XOR and tracks the sign through the *i*-exponent of the underlying letter-wise product. Two literals commute exactly when the symplectic form $\langle x_1, z_2 \rangle + \langle z_1, x_2 \rangle$ vanishes over $\mathbb{F}_2$. A *stabilizer theory* $\Gamma$ is a finite list of literals; the codespace of $\Gamma$ is the simultaneous $+1$-eigenspace of its elements.

## The rules

Sequents have the shape $\Gamma \vdash P$, meaning "from the theory $\Gamma$, the literal $P$ is derivable". There are four rules.

The axiom rule says $\Gamma \vdash \Gamma_k$ for every index *k*: each element of the theory is derivable from itself. The unit rule says $\Gamma \vdash +I$: the identity is always derivable. The multiplication rule says that if $\Gamma \vdash P$ and $\Gamma \vdash Q$ and *P*, *Q* commute, then $\Gamma \vdash P \cdot Q$. The cut rule says that if $\Gamma \vdash P$ and $\Gamma, P \vdash Q$, then $\Gamma \vdash Q$ — derivable lemmas may be used as if they were axioms.

The commutativity side condition in multiplication is not optional. The product of two anticommuting Hermitian Pauli words is anti-Hermitian (it carries an *i*), so it is not a literal. The calculus refuses to combine them.

## Soundness

A literal *P* is *valid* in a theory $\Gamma$ when the codespace of $\Gamma$ is contained in the $+1$-eigenspace of *P*. The four rules above preserve validity in this sense, which is the soundness theorem. Proof is a small finite-dimensional linear algebra exercise; it is mechanized at [`../lean/PauliLogic/Soundness.lean`](../lean/PauliLogic/Soundness.lean).

## Cut elimination is the tableau update

Cut elimination is the algorithm `normalize` in [`../haskell/src/PauliLogic.hs`](../haskell/src/PauliLogic.hs). Structurally, it splices the proof of a cut formula in for every reference to it on the right premise, recursively. Each splice is a constant-time tableau row update — multiplying one Pauli word by another. The cost is linear in the proof DAG. This is the proof-theoretic content of Aaronson and Gottesman's $O(n)$ row multiplication. The cut-free derivations of a literal *Q* from $\Gamma$ are exactly the subset-product certificates: subsets $T \subseteq \{1, \dots, |\Gamma|\}$ with $Q = \prod_{k \in T} \Gamma_k$.

Proof *search* — deciding $\Gamma \vdash Q$ given $\Gamma$ and *Q* — is the row reduction of stabilizer tableaux. Starting from *Q*, multiply by any commuting generator that strictly shrinks the Pauli support; iterate. If *Q* reduces to the identity, you have a subset-product certificate. If it reduces to $-I$, the literal is anti-derivable. This is the $O(n^2)$ step of Aaronson–Gottesman, read as entailment checking.

## Measurement is an effect

The only place stabilizer simulation interacts with non-deterministic data is measurement. Measuring a literal *q* against a maximal theory $\Gamma$ proceeds in two cases. If *q* commutes with every generator of $\Gamma$, entailment is decidable: either $\Gamma \vdash q$ (outcome $+$, theory unchanged) or $\Gamma \vdash -q$ (outcome $-$, theory unchanged). The outcome is forced.

If *q* anticommutes with at least one generator, the outcome is a coin flip. After the flip, the theory updates: pick any anticommuting generator $g_1$, replace it with $(-1)^r q$ where *r* is the outcome, and multiply every other anticommuting generator by $g_1$ to restore commutativity. The state of the simulator is fully captured by the new theory.

In Haskell, the coin flip is the only effect in the simulator. It is exposed as a free monad over a single operation:
```haskell
newtype MeasF k = FlipCoin (Bool -> k)
data Sim a = Pure a | Op (MeasF (Sim a))
```
Everything else — derivation normalisation, tableau search, theory update — is pure. A handler `runSim` interprets `FlipCoin` against a seedable LCG; you can swap in any other handler (deterministic, probabilistic, density-matrix) without touching the simulator. This is the Plotkin–Pretnar style of algebraic effects, applied to stabilizer simulation: the simulator is a syntactic constructor, the handler is the destructor, and the categorical semantics is exactly the one Heunen and Karvonen identified in 2015 for quantum measurement as the destructor side of a Frobenius monad.

We do not lean on the categorical reading anywhere in the proof. It is the right name for what the Haskell code is doing, and it locates this work inside the Edinburgh–Oxford categorical-QM program; the citation belongs in [`03-logical-lattice.md`](03-logical-lattice.md), where it is sharp.

## What's here and where

Syntax, rules, soundness, the tableau correspondence, and cut elimination as a total recursive function are all in [`../lean/PauliLogic/`](../lean/PauliLogic/). The Aaronson–Gottesman row-multiplication identification `tableau_step_eq_mul` is kernel-checked there. The Haskell library [`../haskell/src/PauliLogic.hs`](../haskell/src/PauliLogic.hs) realises everything as data types and pure functions, plus the measurement free monad and a seedable handler. The demo in `Main.hs` derives $XX$ from $\{XI, IX\}$, runs the certificate through cut elimination, and measures $Z_1$ on the Bell state ten times.

## What's new, what's borrowed

The symplectic representation, the row-multiplication rule, and the stabilizer tableau formalism are Aaronson and Gottesman (2004), with antecedents in Gottesman's thesis. The sequent-calculus presentation, the cut-elimination theorem with its identification as tableau reduction at linear cost, and the measurement-as-algebraic-effect realisation are what we add. The soundness theorem is stated and proved here.
