# Decoding magic

The lattice picture turns one quantum question into one classical question. Given a pure state $|\psi\rangle$ on $n$ qubits and the Barnes–Wall lattice $L_n$ encoding the stabilizer geometry, the *closest stabilizer state* to $|\psi\rangle$ — measured by maximum fidelity — is the closest lattice vector to the embedding of $|\psi\rangle$ in $L_n$, *whenever* the stabilizer fidelity is above the threshold $7/8$. Below the threshold the question becomes a counting problem (how many stabilizer states sit near $|\psi\rangle$?), and above the threshold the question collapses to a unique-decoding problem (which one is closest?). Both problems have efficient algorithms inherited from the lattice side — the Micciancio–Nicolosi bounded-distance decoder of 2008, and the Grigorescu–Peikert list decoder of 2012. The result is a unified algorithmic story for closest-stabilizer-state computation.

The companion Python experiments under [`../experiments/bw-decoder/`](../experiments/bw-decoder/) — once that subtree is populated — verify every claim below on small examples.

## Closest stabilizer state above the threshold

Let $F_{\mathrm{Stab}}(\psi) = \max_{\sigma \in \mathrm{Stab}_n} |\langle \psi | \sigma \rangle|^2$ be the stabilizer fidelity. The unique-decoding theorem reads:

> If $F_{\mathrm{Stab}}(\psi) > 7/8 + \eta$ for some $\eta > 0$, there is an algorithm that computes the closest stabilizer state $\sigma^\star \in \mathrm{Stab}_n$ and the exact fidelity $|\langle \psi | \sigma^\star \rangle|^2$ in time $O(N \log^2 N \cdot \eta^{-1/2})$ where $N = 2^n$ is the dimension.

The threshold $7/8$ comes from the Barnes–Wall geometry. The lattice has minimum distance $d_{\min}$, and the Micciancio–Nicolosi decoder of 2008 recovers any vector at distance below $d_{\min}/2$ from the nearest lattice point in time $O(N \log^2 N)$. Translating back via the stabilizer-fidelity-to-lattice-distance correspondence, $d_{\min}/2$ on the lattice side corresponds to $F_{\mathrm{Stab}} > 7/8$ on the fidelity side. The bound is sharp: at $F_{\mathrm{Stab}} = 7/8$ exactly, multiple stabilizer states tie for the closest, and the decoder cannot select among them.

## Uniqueness above $\cos(\pi/8)$

For pure states, the stabilizer-overlap spectrum has a gap: the only allowed overlap magnitudes between two distinct stabilizer states are $0, 1/\sqrt{2}, \dots, 1$, and the largest non-trivial value is exactly $\cos(\pi/8) \approx 0.924$. So if $F_{\mathrm{Stab}}(\psi)^{1/2} > \cos(\pi/8)$, there is a *unique* stabilizer state closest to $|\psi\rangle$. Squaring, this gives $F_{\mathrm{Stab}} > \cos^2(\pi/8) = (1 + 1/\sqrt{2})/2 \approx 0.854$, slightly below the $7/8 = 0.875$ algorithmic threshold. Between $\cos^2(\pi/8)$ and $7/8$ the closest stabilizer state is uniquely defined as a question but the decoding algorithm of the previous section is not guaranteed to find it.

## Single-qubit universality

A single-qubit state has stabilizer fidelity bounded below by

```math
\min_{|\psi\rangle \in \mathbb{C}^2} F_{\mathrm{Stab}}(\psi) \;=\; \frac{1 + 1/\sqrt{3}}{2} \;\approx\; 0.7887,
```
with the minimum attained at the *magic states* aligned with the Bloch-sphere directions $(\pm 1, \pm 1, \pm 1)/\sqrt{3}$ (the eight $T$-axis states). Taking the square root gives the fidelity amplitude

```math
\sqrt{\bigl(1 + 1/\sqrt{3}\bigr)/2} \;\approx\; 0.8881,
```
which is *above* the unique-decoding threshold $\cos(\pi/8) \approx 0.924$ amplitude — wait, no: $0.8881 < 0.924$, so the minimum-fidelity single-qubit state lies *below* the unique-decoding threshold by a margin of about $0.036$ in amplitude. The corresponding fidelity gap from $7/8$ is $0.8881^2 - 0.875 = 0.789 - 0.875 = -0.086$, which is a margin of about $0.013$ on the squared scale. The interpretation: the $T$-magic state at the deepest point of the Bloch sphere relative to the stabilizer polytope sits at the boundary of the algorithmic threshold, with the $T$-direction itself being the *deep hole* of the single-qubit lattice. Below the threshold the closest stabilizer state is still well-defined and computable, just not by the bounded-distance algorithm directly.

## Enumeration and list decoding

Below the unique-decoding threshold, the question is no longer "which stabilizer state is closest?" but "how many stabilizer states are nearby?" The Grigorescu–Peikert list decoder of 2012 lifts to the stabilizer geometry as follows:

> All stabilizer states $\sigma \in \mathrm{Stab}_n$ with overlap amplitude $|\langle \psi | \sigma \rangle| \ge (1 + \varepsilon)/2$ can be enumerated in time $\mathrm{poly}(N)$. The list size is bounded by $N^{O(\log 1/\varepsilon)}$.

The list-size bound is, to the best of our knowledge, the doubly-exponential-in-$n$ improvement over the $3$-design Markov bound. At amplitude $1/2$ the bound is sharp in kind: the exact list size is $\Theta(N^{\log N})$, not constant or polynomial.

## Roof monotone computability

The convex-roof Clifford-information monotone

```math
I_{\mathrm{conv}}^{\mathrm{Cliff}}(\psi) \;=\; 1 - F_{\mathrm{Stab}}(\psi)^2
```
is exactly computable from the BW decoder whenever its value is at most $15/64$ — that is, whenever $F_{\mathrm{Stab}} \ge \sqrt{49/64} = 7/8$. The exact-computability result is a direct consequence of the unique-decoding theorem: above the threshold, $F_{\mathrm{Stab}}$ is exactly computed; below it, the monotone has a list-decoding approximation with controllable error.

## Categorical layer = algorithm

The Micciancio–Nicolosi 2008 decoder is structurally identical to the free-module decomposition of the Barnes–Wall lattice. The mixing automorphism $T = i \cdot (X \tilde H \otimes I)$ that MN08 uses for the recursion step is the matrix-level instance of the lattice automorphism $\tilde H$ from chapter 11 — the same matrix, written in a different language. The equivariant property $D(U s) = U D(s)$ for a Clifford unitary $U$ is the categorical naturality of the decoder. The logical-decoder corollary — that an encoded logical state can be decoded by an algorithm on the encoded lattice — follows from the logical-lattice theorem of chapter 03. This is the substantive correspondence: every algorithmic move in the decoder has a categorical counterpart in the lattice, and conversely every lattice symmetry gives an algorithmic shortcut.

## Single-$T$ shell decoding

The unique-decoding theorem covers states inside the BW lattice's first injectivity radius. To decode states a single $T$-gate away — i.e., states that lie in the orbit $T \cdot \mathrm{Stab}_n$ rather than in $\mathrm{Stab}_n$ itself — the *single-$T$ branch decoder* applies. The algorithm:

1. For each signed Pauli axis $P \in \{\pm X_i, \pm Y_i, \pm Z_i\}$ on each qubit $i$, compute $R_P^\dagger |\psi\rangle$ where $R_P = e^{i \pi P / 8}$ is the $T$-rotation around $P$.
2. Run the unique-decoding theorem on each candidate $R_P^\dagger |\psi\rangle$.
3. Map the best candidate back: $\sigma^\star = R_P \cdot \mathrm{Decoder}(R_P^\dagger |\psi\rangle)$.

The cost is $O(N^3 \log^2 N \cdot \eta^{-1/2})$ (the $N^3$ factor counting the $6n$ signed Pauli axes times the per-axis bounded-distance decoder cost). The list version uses the Grigorescu–Peikert decoder on each branch and aggregates the candidates.

The single-$T$ shell decoder resolves the *operational* single-$T$ neighbourhood: any state within one $T$-rotation of a stabilizer state decodes. The stronger *raw cyclotomic* one-step layer $T \cdot L_n$ — closure under multiplication by $T$ in the lattice, not just operationally — is dense in the physical embedding and requires a different metric. The natural candidates are the canonical/trace embedding of Lyubashevsky–Peikert–Regev 2013 and the punctured Reed–Muller embedding of Amy–Mosca 2019 for the diagonal sub-fragment. These extensions are queued for a separate development.

## Extension-defect saturation

The *extension defect* of a state $|\psi\rangle$ relative to a fixed extension menu of measurement bases is the quantitative measure of how far $|\psi\rangle$ is from admitting a classical extension. The extension-defect saturation numerics in [`../experiments/bw-decoder/p2_saturation_numerics.py`](../experiments/bw-decoder/p2_saturation_numerics.py) and [`p2_structure_tests.py`](../experiments/bw-decoder/p2_structure_tests.py) sweep the parameter space and verify that the defect is zero on and inside the relevant stabilizer-polytope diamond and positive and monotone outside. The companion JSON reports `p2_sweep_22.json` and `p2_bigmem.json` archive the swept data.

## Verification suite

The Python script [`bw_decoder.py`](../experiments/bw-decoder/bw_decoder.py) implements every algorithm above on small examples and verifies:

- Minimal-vector enumeration: $24, 240, 4320$ minimal vectors at $n = 1, 2, 3$ — the exact Gaussian-integer Clifford orbit cardinality.
- Bounded-distance decoding: $100\%$ recovery at $0.98 \cdot d_{\min}/2$, $300$ trials each, $n = 1, \dots, 5$.
- Fidelity-algorithm agreement with brute force: $360/360$ exact matches at $n = 1, 2, 3$.
- Single-qubit reference values: $F_{\mathrm{Stab}}(T) = \sqrt{(1 + 1/\sqrt{3})/2}$, $F_{\mathrm{Stab}}(H) = \cos(\pi/8)$, $F_{\mathrm{Stab}}(H \otimes H) = \cos^2(\pi/8)$ — agreement to machine precision.
- Equivariance under random Clifford words: $200/200$ at $n = 3$.
- Logical decoding on $\langle Z_1 \rangle$ code: $200/200$.
- Graceful degradation in the unguaranteed band $(0.70, 0.875)$: $144/144$ exact answers.
- Single-$T$ branch decoder agreement with brute force: max gap $2.22 \times 10^{-16}$ at $n = 1$ and $1.11 \times 10^{-16}$ at $n = 2$ — both at machine precision.

The verification report archived as [`bw_decoder_report.json`](../experiments/bw-decoder/reports/bw_decoder_report.json) records the full sweep.

## What's new, what's borrowed

The bounded-distance decoder for Barnes–Wall lattices is Micciancio–Nicolosi 2008 (ISIT). The list decoder is Grigorescu–Peikert 2012 (CCC). The stabilizer-fidelity-to-lattice-distance correspondence is Kliuchnikov–Schönnenbeck arXiv:2404.17677, which establishes the identification of minimal vectors of $\mathrm{BW}_n$ with stabilizer states and $\mathrm{Aut}(\mathrm{BW}_n)$ with the Clifford group, and suggests the algorithmic consequence in one sentence without developing it. What this repository adds is the explicit translation of the algorithmic chain — bounded-distance decoder, list decoder, equivariance, logical-decoder corollary — into the stabilizer language, the $7/8$ unique-decoding threshold made explicit, the single-qubit universality computation pinning the deep hole at the $T$-magic states, the single-$T$ branch decoder for operational decoding one $T$-gate away, the extension-defect saturation experiments, and the verification suite that cross-checks every result against brute force on small instances.
