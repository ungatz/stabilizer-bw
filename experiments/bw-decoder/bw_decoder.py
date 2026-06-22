"""
Barnes-Wall decoding for stabilizer geometry: verification suite.

Implements:
  * Exact enumeration of minimal vectors of BW_n (= scaled stabilizer states,
    Kliuchnikov-Schoennenbeck arXiv:2404.17677) for n = 1,2,3 via Clifford orbit
    over Gaussian integers.
  * The Micciancio-Nicolosi (ISIT 2008) parallel bounded-distance decoder
    (4-candidate recursion), correct up to squared radius d^2_min/4 = N/4.
  * The closest-stabilizer-state / stabilizer-fidelity algorithm (phase grid +
    BDD), with brute-force cross-checks.
  * Clifford-equivariance tests, logical (code-sublattice) decoding tests,
    and fidelity-counting experiments.

Lattice convention (MN08): BW_n = row span over Z[i] of [[1,1],[0,phi]]^{tensor n},
phi = 1+i;  d^2_min = N = 2^n.  Minimal vectors = i^k phi^n C|0...0> (K-S).
"""

import numpy as np
import itertools, json, math, random
from collections import deque

PHI = 1 + 1j

# ---------------------------------------------------------------------------
# 1. Exact minimal-vector enumeration via Clifford orbit (Gaussian integers)
# ---------------------------------------------------------------------------

def gauss_tuple(vec):
    """Exact representation: tuple of (re, im) integer pairs."""
    return tuple((int(round(z.real)), int(round(z.imag))) for z in vec)

def apply_S(v, q, n):
    """S = diag(1, i) on qubit q (0 = most significant). Exact."""
    out = list(v)
    for idx in range(2 ** n):
        if (idx >> (n - 1 - q)) & 1:
            re, im = out[idx]
            out[idx] = (-im, re)          # multiply by i
    return tuple(out)

def apply_H(v, q, n):
    """Htilde = ((1-i)/2) [[1,1],[1,-1]] on qubit q. Exact on lattice orbit."""
    out = [None] * (2 ** n)
    bit = 1 << (n - 1 - q)
    for idx in range(2 ** n):
        if idx & bit:
            continue
        a, b = v[idx], v[idx | bit]
        for tgt, (cr, ci) in ((idx, (a[0] + b[0], a[1] + b[1])),
                              (idx | bit, (a[0] - b[0], a[1] - b[1]))):
            # (1-i)(cr + i ci)/2 = ((cr+ci) + i(ci-cr))/2
            rr, ii = cr + ci, ci - cr
            assert rr % 2 == 0 and ii % 2 == 0, "left Gaussian integers!"
            out[tgt] = (rr // 2, ii // 2)
    return tuple(out)

def apply_CNOT(v, c, t, n):
    out = list(v)
    cb, tb = 1 << (n - 1 - c), 1 << (n - 1 - t)
    for idx in range(2 ** n):
        if (idx & cb) and not (idx & tb):
            j = idx | tb
            out[idx], out[j] = v[j], v[idx]
    return tuple(out)

def minimal_vectors(n):
    """BFS orbit of phi^n |0...0> under {S_q, H_q, CNOT_ct}. Exact."""
    start = [(0, 0)] * (2 ** n)
    z = complex(PHI ** n)
    start[0] = (int(round(z.real)), int(round(z.imag)))
    start = tuple(start)
    gens = []
    for q in range(n):
        gens.append(lambda v, q=q: apply_S(v, q, n))
        gens.append(lambda v, q=q: apply_H(v, q, n))
    for c in range(n):
        for t in range(n):
            if c != t:
                gens.append(lambda v, c=c, t=t: apply_CNOT(v, c, t, n))
    seen, queue = {start}, deque([start])
    while queue:
        v = queue.popleft()
        for g in gens:
            w = g(v)
            if w not in seen:
                seen.add(w)
                queue.append(w)
    return seen

def to_complex(v):
    return np.array([complex(re, im) for re, im in v])

# ---------------------------------------------------------------------------
# 2. Micciancio-Nicolosi BDD (parallel 4-candidate recursion)
# ---------------------------------------------------------------------------

def round_gauss(s):
    return np.round(s.real) + 1j * np.round(s.imag)

def bdd(s):
    """MN08 Algorithm 1 (p = N^2). Correct if dist^2(s, BW_n) < N/4."""
    if len(s) == 1:
        return round_gauss(s)
    h = len(s) // 2
    s0, s1 = s[:h], s[h:]
    sm, sp = (PHI / 2) * (s0 - s1), (PHI / 2) * (s0 + s1)
    z0, z1, zm, zp = bdd(s0), bdd(s1), bdd(sm), bdd(sp)
    w = 1 - 1j                       # 2/phi
    cands = (np.concatenate([z0, z0 - w * zm]),
             np.concatenate([z0, w * zp - z0]),
             np.concatenate([w * zm + z1, z1]),
             np.concatenate([w * zp - z1, z1]))
    return min(cands, key=lambda c: np.linalg.norm(s - c) ** 2)

# ---------------------------------------------------------------------------
# 3. Closest stabilizer state / stabilizer fidelity via BDD + phase grid
# ---------------------------------------------------------------------------

def fidelity_via_decoder(psi, grid=64):
    """Return (best fidelity found, best stabilizer ray as scaled vector)."""
    n = int(math.log2(len(psi)))
    scale = 2 ** (n / 2)
    s = scale * psi
    best_f, best_v = 0.0, None
    for g in range(grid):
        theta = (math.pi / 2) * g / grid
        z = bdd(np.exp(1j * theta) * s)
        nz = np.linalg.norm(z) ** 2
        if abs(nz - 2 ** n) < 1e-6:          # minimal vector => stabilizer ray
            f = abs(np.vdot(z, psi)) / scale
            if f > best_f:
                best_f, best_v = f, z
    return best_f, best_v

def fidelity_brute(psi, rays):
    n = int(math.log2(len(psi)))
    scale = 2 ** (n / 2)
    fs = [abs(np.vdot(r, psi)) / scale for r in rays]
    return max(fs), fs

# ---------------------------------------------------------------------------
# 4. Verification experiments
# ---------------------------------------------------------------------------

def ray_classes(vectors):
    """Group minimal vectors into unit classes (rays) {v, iv, -v, -iv}."""
    seen, reps = set(), []
    for v in vectors:
        if v in seen:
            continue
        cur, arr = v, to_complex(v)
        for k in range(4):
            seen.add(gauss_tuple(arr * (1j ** k)))
        reps.append(arr)
    return reps

def random_state(N, rng):
    v = rng.normal(size=N) + 1j * rng.normal(size=N)
    return v / np.linalg.norm(v)

def run_all():
    rng = np.random.default_rng(7)
    report = {}

    # --- minimal vector counts (K-S correspondence; kissing numbers) -------
    mv = {n: minimal_vectors(n) for n in (1, 2, 3)}
    rays = {n: ray_classes(mv[n]) for n in (1, 2, 3)}
    report['minimal_vector_counts'] = {n: len(mv[n]) for n in mv}      # 24,240,4320
    report['ray_counts'] = {n: len(rays[n]) for n in rays}             # 6,60,1080
    for n in (1, 2, 3):
        assert all(abs(np.linalg.norm(r) ** 2 - 2 ** n) < 1e-9 for r in rays[n])

    # --- BDD radius test: planted stabilizer + noise ------------------------
    bdd_res = {}
    for n in (1, 2, 3, 4, 5):
        N = 2 ** n
        rays_n = rays.get(n)
        ok_in, ok_out = 0, 0
        T = 300
        for _ in range(T):
            if rays_n is not None:
                z = random.choice(rays_n)
            else:  # plant a random Clifford-orbit vector via decoded random pt
                z = bdd(rng.normal(size=N) * 3 + 1j * rng.normal(size=N) * 3)
            e = rng.normal(size=N) + 1j * rng.normal(size=N)
            e = e / np.linalg.norm(e)
            r_in = math.sqrt(N / 4) * 0.98          # just inside radius
            out = bdd(z + r_in * e)
            ok_in += int(np.allclose(out, z, atol=1e-7))
        bdd_res[n] = {'inside_radius_recovery_rate': ok_in / T}
        assert ok_in == T, f"BDD failed inside unique radius at n={n}"
    report['bdd_radius_test'] = bdd_res

    # --- Theorem A: fidelity algorithm vs brute force -----------------------
    fid_res = {}
    for n in (1, 2, 3):
        N, rays_n = 2 ** n, rays[n]
        agree, total = 0, 0
        worst_gap = 0.0
        for _ in range(120):
            # states in the BDD regime: stabilizer + small superposition
            z = random.choice(rays_n) / 2 ** (n / 2)
            psi = z + 0.25 * random_state(N, rng)
            psi /= np.linalg.norm(psi)
            fb, _ = fidelity_brute(psi, rays_n)
            fd, _ = fidelity_via_decoder(psi)
            if fb > 7 / 8 + 0.01:
                total += 1
                agree += int(abs(fb - fd) < 1e-9)
                worst_gap = max(worst_gap, abs(fb - fd))
        fid_res[n] = {'promised_instances': total, 'exact_agreement': agree,
                      'worst_gap': worst_gap}
        assert agree == total
    report['fidelity_algorithm_vs_bruteforce'] = fid_res

    # --- named states --------------------------------------------------------
    T_state = np.array([math.cos(0.5 * math.acos(1 / math.sqrt(3))),
                        np.exp(1j * math.pi / 4) * math.sin(0.5 * math.acos(1 / math.sqrt(3)))])
    H_state = np.array([math.cos(math.pi / 8), math.sin(math.pi / 8)])
    named = {}
    for name, st in (('T', T_state), ('H', H_state)):
        fb, _ = fidelity_brute(st, rays[1])
        fd, _ = fidelity_via_decoder(st, grid=256)
        named[name] = {'brute': fb, 'decoder': fd}
    named['T_theory'] = math.sqrt((1 + 1 / math.sqrt(3)) / 2)
    named['H_theory'] = math.cos(math.pi / 8)
    HH = np.kron(H_state, H_state)
    fb_HH, _ = fidelity_brute(HH, rays[2])
    fd_HH, _ = fidelity_via_decoder(HH, grid=256)
    named['HH'] = {'brute': fb_HH, 'decoder': fd_HH,
                   'theory_cos2': math.cos(math.pi / 8) ** 2}
    report['named_states'] = named

    # --- n=1 universality: worst-case fidelity over the sphere --------------
    worst = 1.0
    for _ in range(20000):
        psi = random_state(2, rng)
        fb, _ = fidelity_brute(psi, rays[1])
        worst = min(worst, fb)
    report['n1_worst_fidelity_sampled'] = worst
    report['n1_worst_fidelity_theory'] = math.sqrt((1 + 1 / math.sqrt(3)) / 2)
    report['n1_universality_holds'] = worst > 7 / 8

    # --- equivariance test ----------------------------------------------------
    def rand_clifford_word(n, length, rng):
        ops = []
        for _ in range(length):
            k = rng.integers(0, 3)
            if k == 0:
                ops.append(('S', int(rng.integers(0, n))))
            elif k == 1:
                ops.append(('H', int(rng.integers(0, n))))
            else:
                c = int(rng.integers(0, n)); t = int(rng.integers(0, n))
                if c == t:
                    t = (t + 1) % n
                ops.append(('CX', c, t))
        return ops

    def apply_word_c(vec, word, n):
        v = gauss_scale_free(vec)
        for op in word:
            if op[0] == 'S':
                v = S_mat(op[1], n) @ v
            elif op[0] == 'H':
                v = H_mat(op[1], n) @ v
            else:
                v = CX_mat(op[1], op[2], n) @ v
        return v

    import functools
    @functools.lru_cache(maxsize=None)
    def S_mat(q, n):
        m = np.diag([1j if (i >> (n - 1 - q)) & 1 else 1 for i in range(2 ** n)])
        return m.astype(complex)
    @functools.lru_cache(maxsize=None)
    def H_mat(q, n):
        h = ((1 - 1j) / 2) * np.array([[1, 1], [1, -1]])
        mats = [h if k == q else np.eye(2) for k in range(n)]
        m = mats[0]
        for x in mats[1:]:
            m = np.kron(m, x)
        return m
    @functools.lru_cache(maxsize=None)
    def CX_mat(c, t, n):
        m = np.zeros((2 ** n, 2 ** n), dtype=complex)
        for i in range(2 ** n):
            j = i ^ (1 << (n - 1 - t)) if (i >> (n - 1 - c)) & 1 else i
            m[j, i] = 1
        return m
    def gauss_scale_free(v):
        return v

    eq_ok, eq_T = 0, 200
    for _ in range(eq_T):
        n = 3
        N = 2 ** n
        z = random.choice(rays[3])
        e = rng.normal(size=N) + 1j * rng.normal(size=N)
        e *= (math.sqrt(N / 4) * 0.9) / np.linalg.norm(e)
        x = z + e
        word = rand_clifford_word(n, 6, rng)
        U = np.eye(N, dtype=complex)
        for op in word:
            U = (S_mat(op[1], n) if op[0] == 'S' else
                 H_mat(op[1], n) if op[0] == 'H' else
                 CX_mat(op[1], op[2], n)) @ U
        lhs, rhs = bdd(U @ x), U @ bdd(x)
        eq_ok += int(np.allclose(lhs, rhs, atol=1e-7))
    report['equivariance'] = {'trials': eq_T, 'passed': eq_ok}
    assert eq_ok == eq_T

    # --- logical decoding: BW_2^{<Z1>} = phi |0> (x) BW_1 ---------------------
    # decode within the code sublattice by decoding the inner BW_1 factor
    log_ok, log_T = 0, 200
    for _ in range(log_T):
        a = random.choice(rays[1])                       # inner BW_1 minimal vec
        zcode = np.concatenate([PHI * a, np.zeros(2)])   # phi|0> (x) a
        e = rng.normal(size=4) + 1j * rng.normal(size=4)
        # BDD radius of the scaled inner lattice: d^2 = 2*2 = 4 -> radius 1
        e *= 0.95 / np.linalg.norm(e)
        x = zcode + e
        # logical decode: strip phi|0> factor, decode inner target in BW_1
        inner = x[:2] / PHI
        a_hat = bdd(inner)
        log_ok += int(np.allclose(PHI * a_hat, zcode[:2], atol=1e-7))
    report['logical_decoding'] = {'trials': log_T, 'passed': log_ok}

    # --- Theorem B experiment: fidelity counting -------------------------------
    counting = {}
    for n in (2, 3):
        rays_n = rays[n]
        rows = []
        for trial in range(40):
            psi = random_state(2 ** n, rng)
            _, fs = fidelity_brute(psi, rays_n)
            fs = np.array(fs)
            rows.append([int((fs >= tau).sum())
                         for tau in (0.5, 0.55, 0.6, 0.7, 0.8, 0.9)])
        counting[n] = {
            'thresholds': [0.5, 0.55, 0.6, 0.7, 0.8, 0.9],
            'max_counts': np.array(rows).max(axis=0).tolist(),
            'total_states': len(rays_n)}
        # stabilizer input: overlap spectrum
        z = random.choice(rays_n) / 2 ** (n / 2)
        _, fs = fidelity_brute(z, rays_n)
        spec = sorted(set(round(f, 6) for f in fs), reverse=True)
        counting[str(n) + '_stab_overlap_spectrum'] = spec[:6]
    report['fidelity_counting'] = counting

    # --- threshold sharpness: behavior just below 7/8 -------------------------
    below = {'tested': 0, 'still_correct': 0}
    for _ in range(600):
        n, N = 2, 4
        z = random.choice(rays[2]) / 2 ** (n / 2)
        amp = rng.uniform(0.45, 1.0)
        psi = z + amp * random_state(N, rng)
        psi /= np.linalg.norm(psi)
        fb, _ = fidelity_brute(psi, rays[2])
        if 0.70 < fb < 7 / 8:
            fd, _ = fidelity_via_decoder(psi)
            below['tested'] += 1
            below['still_correct'] += int(abs(fb - fd) < 1e-9)
    report['below_threshold_heuristic'] = below

    return report


if __name__ == '__main__':
    rep = run_all()
    print(json.dumps(rep, indent=2, default=str))
    with open('bw_decoder_report.json', 'w') as f:
        json.dump(rep, f, indent=2, default=str)
