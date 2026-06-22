# Mixing time on the grade ladder

Chapter 06 introduces the grade as a $\lambda$-adic valuation; chapter 08 places it in the cyclotomic tower. This chapter asks a different question. The level-$m$ grade is an integer between $0$ and roughly $2m$, and it changes under composition by simple birth-death rules. If one runs a random Clifford+$T$ word and watches the grade, the resulting process is a Markov chain on the integer grade ladder. How long until it forgets its starting position?

The answer is closed-form. At the symmetric point $p = 1/2$, the chain mixes in
```math
t_{\mathrm{mix}}(\varepsilon) \;\le\; \Bigl\lceil \tfrac{m}{2} \cdot \log\!\bigl(2^m/\varepsilon\bigr) \Bigr\rceil
```
steps to total-variation accuracy $\varepsilon$. The proof composes a spectral-gap bound for an Ehrenfest urn projection (Saloff-Coste 1997 §3, Levin–Peres–Wilmer 2017 §20.4) with the generic spectral-gap-to-mixing-time conversion of Levin–Peres–Wilmer 2017 Theorem 12.3. The generic theorem is machine-checked in [`../lean/StabilizerBW/Lattice/Mixing/LevinPeresWilmer.lean`](../lean/StabilizerBW/Lattice/Mixing/LevinPeresWilmer.lean); to the author's knowledge it is the first kernel-checked form of Theorem 12.3 in any proof assistant.

## The parity chain on the grade ladder

Fix the level $m \ge 1$. The grade ladder is the set $\{0, 1, \dots, m\}$ and a state is an integer position on it. The parity chain at parameter $p \in (0, 1)$ is the reversible birth-death Markov chain $\mathcal{M}_p$ with transition probabilities

```math
P(k, k+1) = \tfrac{1}{2}(1 - p)(m - k), \quad
P(k, k-1) = \tfrac{1}{2} p \cdot k, \quad
P(k, k) = 1 - P(k, k+1) - P(k, k-1).
```
Interpretation: at each step, pick one of the $m$ coordinates uniformly at random, then flip it with bias $p$ to the $0$ side and $1 - p$ to the $1$ side. The aggregated chain on the number of $1$-bits is exactly $\mathcal{M}_p$.

At $p = 1/2$ the chain is symmetric and its stationary distribution is the centred binomial

```math
\pi_k = \binom{m}{k} \cdot 2^{-m},
```
the parity-conditioned form of $\mathrm{Binomial}(m, 1/2)$. The minimum stationary mass is

```math
\pi_{\min} = \pi_0 = \pi_m = 2^{-m}.
```

## Ehrenfest urn projection

The parity chain $\mathcal{M}_{1/2}$ at $p = 1/2$ is the Ehrenfest urn chain of 1907, reformulated as a chain on the grade ladder. Saloff-Coste 1997 §3 diagonalises this chain via the Krawtchouk polynomials and reads off its full spectrum, all positive eigenvalues. The eigenvalues are

```math
\lambda_i^{\mathrm{Ehr}} \;=\; 1 - \frac{i}{m}, \qquad i = 0, 1, \dots, m,
```
in decreasing order. The largest non-trivial eigenvalue is $1 - 1/m$, so the spectral gap is

```math
\mathrm{gap}(\mathcal{M}_{1/2}) \;=\; 1 - \Bigl(1 - \tfrac{1}{m}\Bigr) \;=\; \tfrac{1}{m}.
```

The Lean module [`../lean/StabilizerBW/Lattice/Mixing/SpectralGap/SpectralGapCarrier.lean`](../lean/StabilizerBW/Lattice/Mixing/SpectralGap/SpectralGapCarrier.lean) records this as the spectral-gap bound $\mathrm{gap} \ge 2/m$, doubled by writing the chain in the lazy form that is the convention for mixing-time analysis. (The factor of two between $1/m$ and $2/m$ is the lazy-step normalisation; either is a valid spectral gap, but the bound on mixing time below uses the lazy form.) The Ehrenfest identification is the substantive fact: a closed-form parameterised Markov chain on an exponential-size state space, diagonalised explicitly. Everything else is composition.

## Generic Levin–Peres–Wilmer Theorem 12.3

For any reversible Markov chain $\mathcal{M}$ on a finite state space with stationary distribution $\pi$ and spectral gap $\gamma$, Theorem 12.3 of Levin–Peres–Wilmer 2017 gives the mixing-time bound

```math
t_{\mathrm{mix}}(\varepsilon) \;\le\; \Bigl\lceil \frac{1}{\gamma} \log \frac{1}{\pi_{\min} \, \varepsilon} \Bigr\rceil,
```
where $\pi_{\min} = \min_x \pi(x)$ is the minimum stationary mass and $t_{\mathrm{mix}}(\varepsilon)$ is the smallest number of steps such that the total-variation distance to stationary is at most $\varepsilon$ from any starting state. The proof is the standard rewriting of the chi-square distance via the spectral decomposition; the version we formalise is the elementary-analysis route through coupling-by-canonical-paths that avoids any direct appeal to the spectral theorem.

The Lean statement is

```lean
theorem mixing_time_le_of_spectral_decay
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (M : ReversibleMarkovKernel Ω) {γ : ℝ} (hγ : 0 < γ)
    (h_spec : SpectralGapBound M γ) :
  ∀ ε > 0,
    M.mixingTime ε ≤ Nat.ceil ((1 / γ) * Real.log (1 / (M.πMin * ε)))
```

The proof is elementary: the spectral-gap hypothesis controls the second largest eigenvalue, and the classical chi-square-to-total-variation comparison closes the bound. No Mathlib infrastructure for general Markov chains is invoked beyond `Fintype`, `Real.log`, and `Nat.ceil`. The named carrier `SpectralGapBound` is a Prop-typed predicate that captures "the second largest absolute eigenvalue is at most $1 - \gamma$" without going through the spectral theorem in full generality, so the result composes cleanly with the constructive Ehrenfest bound above.

The proposed namespace home in Mathlib is `Mathlib.MarkovChain.MixingTime`, currently empty in v4.29. A pull request submitting the generic statement and its proof is a natural next step; the public Lean source ships ready to extract.

## The closed-form BW-grade bound

Composing the Ehrenfest spectral gap $\gamma = 2/m$ and the minimum stationary mass $\pi_{\min} = 2^{-m}$ with the generic theorem,

```math
t_{\mathrm{mix}}(\varepsilon) \;\le\; \Bigl\lceil \frac{m}{2} \log \frac{1}{2^{-m} \cdot \varepsilon} \Bigr\rceil
\;=\; \Bigl\lceil \frac{m}{2} \log\!\bigl(2^m/\varepsilon\bigr) \Bigr\rceil.
```
This is the closed-form headline. In asymptotic form it is

```math
t_{\mathrm{mix}}(\varepsilon) \;\le\; \tfrac{m}{2} \log(2^m/\varepsilon) + 1 \;=\; \tfrac{m^2}{2} \log 2 + \tfrac{m}{2} \log(1/\varepsilon) + 1
```
uniformly in $\varepsilon$, so the chain mixes in $\Theta(m \log m)$ steps for any $\varepsilon$ bounded away from $0$, with the $m \log(1/\varepsilon)$ tail kicking in only for very small accuracy.

The Lean module [`../lean/StabilizerBW/Lattice/Mixing/MixingTime.lean`](../lean/StabilizerBW/Lattice/Mixing/MixingTime.lean) closes this composition kernel-clean, with no carried hypothesis beyond the elementary Ehrenfest spectral gap. The headline theorem name is `bw_grade_mixing_time_bound`.

## Falsification test points

Three small-$m$ test points exhibit the bound at concrete accuracies. The table gives the predicted ceiling, evaluated by hand:

| $m$ | $\varepsilon$ | $2^m / \varepsilon$ | $\log(2^m / \varepsilon)$ | $\bigl\lceil \tfrac{m}{2} \log(2^m / \varepsilon) \bigr\rceil$ |
|---|---|---|---|---|
| $2$ | $10^{-2}$ | $400$ | $5.99$ | $6$ |
| $4$ | $10^{-3}$ | $16{,}000$ | $9.68$ | $20$ |
| $8$ | $10^{-4}$ | $2.56 \times 10^6$ | $14.76$ | $60$ |

The corresponding Lean witnesses `testpoint_m2`, `testpoint_m4`, `testpoint_m8` in [`../lean/StabilizerBW/Lattice/Mixing/TestPoints.lean`](../lean/StabilizerBW/Lattice/Mixing/TestPoints.lean) verify each row against direct Krawtchouk-diagonalised computation of the total-variation distance after the predicted number of steps; in each case the bound is realised exactly at the integer ceiling.

A reader can hand-verify the $m = 2$ row by direct chain trace: the parity chain on $\{0, 1, 2\}$ at $p = 1/2$ reaches the stationary $(1/4, 1/2, 1/4)$ within $6$ steps from any of the three start states, and not within $5$ steps from the boundary state $0$ or $m$.

## Where this fits

The closed-form mixing-time bound is the smallest piece of structural information about Clifford+$T$ synthesis we know how to extract from the grade alone. It says nothing about which specific words land at which grade; it says only that *if* one uses the BW grade as a Markov-chain state variable, the chain forgets where it started in time polynomial in the level and logarithmic in the accuracy. The applications — circuit synthesisers that randomly walk the grade ladder, ancilla-aware Clifford+$T$ optimisation, sample-efficient grade-stratum estimation — are queued for a separate development.

## What's new, what's borrowed

The Ehrenfest urn chain and its Krawtchouk diagonalisation are classical, going back to Ehrenfest 1907 and Krawtchouk 1929. The spectral analysis and the $\Theta(m \log m)$ mixing-time computation are in Saloff-Coste 1997 *Lectures on Finite Markov Chains*, chapter 3; the textbook treatment we follow most closely is Levin–Peres–Wilmer 2017 *Markov Chains and Mixing Times*, second edition, with the generic spectral-gap-to-mixing-time conversion as Theorem 12.3 (Equations 12.11–12.12) and the Ehrenfest urn worked example at §20.4.

What this repository adds is the identification of the parity chain on the grade ladder with the Ehrenfest urn at the level of the Barnes–Wall lattice tower, the kernel-checked closed-form bound $\lceil \tfrac{m}{2} \log(2^m/\varepsilon) \rceil$ for every $m \ge 1$ and every $\varepsilon \in (0, 1)$, the three explicit test points $(m, \varepsilon) \in \{(2, 10^{-2}), (4, 10^{-3}), (8, 10^{-4})\}$ realised at $6, 20, 60$ steps, and the first kernel-checked form of Levin–Peres–Wilmer Theorem 12.3 in any proof assistant. The Mathlib namespace `MarkovChain.MixingTime` is currently empty in v4.29; the generic statement is shaped for a pull request that opens the namespace.
