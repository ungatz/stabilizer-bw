"""
One-T neighbourhood decoder experiments.

This file tests the reduction:

    closest one-T ray = branch over signed Pauli axes P,
                        decode R_P^* psi as a stabilizer problem,
                        map the stabilizer candidate forward by R_P.

The reduction is proved against the abstract Barnes-Wall BDD contract in the
companion Lean development; see ../../lean/StabilizerBW/Decoder*.lean.  The
experiments here only sanity-check the phase/sign conventions in small dimensions
where brute force over the one-T shell is feasible.
"""

import itertools
import json
import math

import numpy as np

import bw_decoder as bw


I2 = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)
PAULI_LETTERS = (I2, X, Y, Z)


def kron_all(mats):
    out = np.array([[1]], dtype=complex)
    for mat in mats:
        out = np.kron(out, mat)
    return out


def signed_paulis(n):
    """Signed non-identity Hermitian Pauli matrices on n qubits."""
    out = []
    for word in itertools.product(range(4), repeat=n):
        if all(letter == 0 for letter in word):
            continue
        p = kron_all(PAULI_LETTERS[letter] for letter in word)
        out.append(p)
        out.append(-p)
    return out


def one_t_rotation(p, adjoint=False):
    """R_P = exp(-i pi P/8), with optional adjoint."""
    sign = 1 if adjoint else -1
    return math.cos(math.pi / 8) * np.eye(p.shape[0]) + sign * 1j * math.sin(math.pi / 8) * p


def random_state(dim, rng):
    vec = rng.normal(size=dim) + 1j * rng.normal(size=dim)
    return vec / np.linalg.norm(vec)


def normalized_stabilizer_rays(n):
    scale = 2 ** (n / 2)
    return [ray / scale for ray in bw.ray_classes(bw.minimal_vectors(n))]


def one_t_candidates(n):
    rays = normalized_stabilizer_rays(n)
    candidates = []
    for p in signed_paulis(n):
        rot = one_t_rotation(p)
        candidates.extend(rot @ ray for ray in rays)
    return candidates


def brute_one_t_fidelity(psi, candidates):
    return max(abs(np.vdot(candidate, psi)) for candidate in candidates)


def branch_one_t_fidelity(psi, paulis, grid=128):
    best = 0.0
    for p in paulis:
        pulled_back = one_t_rotation(p, adjoint=True) @ psi
        fidelity, _ = bw.fidelity_via_decoder(pulled_back, grid=grid)
        best = max(best, fidelity)
    return best


def run_smoke(seed=13, trials=30):
    rng = np.random.default_rng(seed)
    report = {}
    for n in (1, 2):
        paulis = signed_paulis(n)
        candidates = one_t_candidates(n)
        promised = 0
        exact = 0
        max_gap = 0.0
        for _ in range(trials):
            planted = candidates[int(rng.integers(0, len(candidates)))]
            psi = planted + 0.12 * random_state(2**n, rng)
            psi = psi / np.linalg.norm(psi)
            brute = brute_one_t_fidelity(psi, candidates)
            if brute <= 7 / 8 + 0.005:
                continue
            promised += 1
            branch = branch_one_t_fidelity(psi, paulis)
            gap = abs(brute - branch)
            max_gap = max(max_gap, gap)
            exact += int(gap < 1e-9)
        report[n] = {
            "signed_paulis": len(paulis),
            "raw_candidates": len(candidates),
            "promised_instances": promised,
            "exact_agreement": exact,
            "max_gap": max_gap,
        }
        assert promised == exact
    return report


if __name__ == "__main__":
    result = run_smoke()
    print(json.dumps(result, indent=2, default=float))
    with open("one_t_decoder_report.json", "w") as f:
        json.dump(result, f, indent=2, default=float)
