# Barnes–Wall decoder experiments

This directory contains the Python verification suite for the closest-stabilizer-state and one-$T$-shell decoders described in [`../../narrative/10-decoding.md`](../../narrative/10-decoding.md). The scripts implement every algorithm on small qubit counts and cross-check against brute-force enumeration. They are not part of the Lean development; they are a self-contained numerical sanity-check layer.

## What each script computes

| script | what it does |
|---|---|
| `bw_decoder.py` | Minimal-vector enumeration of $\mathrm{BW}_n$ at $n = 1, 2, 3$ via Clifford-orbit enumeration over $\mathbb{Z}[i]$; Micciancio–Nicolosi bounded-distance decoder; closest-stabilizer-state fidelity algorithm; equivariance and logical-decoder tests. Writes `reports/bw_decoder_report.json`. |
| `one_t_decoder.py` | Single-$T$ branch decoder. Branches over signed Pauli axes $P \in \{\pm X_i, \pm Y_i, \pm Z_i\}$, decodes $R_P^\dagger \psi$ as an ordinary stabilizer problem, maps the best candidate forward. Cross-checks against brute force at $n = 1, 2$. Writes `reports/one_t_decoder_report.json`. |
| `p2_saturation_numerics.py` | Extension-defect minimisation via the Hughston–Jozsa–Wootters parametrisation. Sweeps the parameter grid and verifies the defect is zero on the stabilizer-polytope diamond and positive outside. Writes `reports/p2_sweep_22.json`. |
| `p2_structure_tests.py` | Structural sanity checks of the extension-defect minimiser: dimension-4 attainment, monotonicity, convexity. Writes `reports/p2_bigmem.json`. |
| `quantitative_witness_check.py` | Numerical verification of the quantitative-rigidity witnesses underlying the $C(m) \cdot \varepsilon^{1/4}$ modulus. Writes `reports/quantitative_witness_check.json`. |

## Running the suite

The scripts depend only on `numpy` (already required for any reasonable scientific Python environment).

```bash
cd experiments/bw-decoder
python3 bw_decoder.py            # ~30 seconds at n=1,2,3
python3 one_t_decoder.py         # ~10 seconds at n=1,2
python3 p2_saturation_numerics.py  # ~2 minutes
python3 p2_structure_tests.py    # ~10 minutes (memory-heavy)
python3 quantitative_witness_check.py  # ~30 seconds
```

Each script prints a brief status line to stdout and writes a structured JSON report under `reports/`. The reports are committed to the repository as the verification record.

## Reading the reports

The JSON reports in `reports/` have the structure:

```json
{
  "spec": "what the script is testing",
  "results": {
    "test_name_1": { "pass": true, "details": {...} },
    "test_name_2": { "pass": true, "details": {...} }
  },
  "summary": { "passed": N, "failed": 0 }
}
```

A clean run produces zero failures. The `details` field of each test records the numerical evidence (sample size, max gap from expectation, exact equality where applicable). Sample-size and gap-magnitude conventions are documented in the script's docstring.

## Reproducibility notes

The scripts use `numpy`'s default random number generator (seeded explicitly in each script for reproducibility). The minimal-vector enumeration at $n = 3$ enumerates 4320 vectors — the Clifford orbit of $|0\rangle^{\otimes 3}$ at level 3 — and is the most memory-intensive call (around 100 MB peak). The `p2_structure_tests.py` script sweeps a $22 \times 22 \times 22$ parameter grid and uses peak memory around 8 GB; the corresponding `p2_bigmem.json` report archives the result so a rerun is not necessary unless the algorithm changes.

## Reference

The mathematical statements verified by these experiments are in [`../../narrative/10-decoding.md`](../../narrative/10-decoding.md), which cites Micciancio–Nicolosi 2008, Grigorescu–Peikert 2012, and Kliuchnikov–Schönnenbeck 2024 as the lattice-side sources. The Lean development is at [`../../lean/StabilizerBW/`](../../lean/StabilizerBW/), with the decoder modules under `Decoder*.lean`.
