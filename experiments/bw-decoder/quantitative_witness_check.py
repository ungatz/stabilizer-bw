"""Numerical check of the quantitative CHSH witness theorem:
   for 2-qubit pure psi with Pauli-menu CHSH score S > 2:
       I_conv(psi) = 1 - F_STAB^2  >=  (S - 2)^2 / 32.
Proof chain being tested: S - 2 <= 4*sqrt2*T(psi, Stab2) and T <= sqrt(I_conv)."""
import numpy as np, itertools, json
from bw_decoder import minimal_vectors, ray_classes

I2 = np.eye(2)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]])
Z = np.diag([1., -1.]).astype(complex)

R = [r / 2.0 for r in ray_classes(minimal_vectors(2))]   # 60 unit rays
assert len(R) == 60, len(R)

Ws = []
for A0, A1 in itertools.permutations([X, Y, Z], 2):
    for B0, B1 in itertools.permutations([X, Y, Z], 2):
        for s0 in (1, -1):
            for s1 in (1, -1):
                Ws.append(np.kron(s0 * A0, B0 + B1) + np.kron(s1 * A1, B0 - B1))

rng = np.random.default_rng(2)
viol, worst, maxS = 0, np.inf, 0.0
for trial in range(600):
    v = rng.normal(size=4) + 1j * rng.normal(size=4)
    v /= np.linalg.norm(v)
    S = max((v.conj() @ W @ v).real for W in Ws)
    maxS = max(maxS, S)
    if S > 2 + 1e-9:
        F2 = max(abs(np.vdot(r, v)) ** 2 for r in R)
        Ic = 1 - F2
        ratio = Ic / ((S - 2) ** 2 / 32)
        viol += 1
        worst = min(worst, ratio)

out = {"violating": viol, "total": 600,
       "worst_ratio_Iconv_over_bound": round(float(worst), 4),
       "max_Pauli_CHSH_sampled": round(float(maxS), 4)}
print(json.dumps(out, indent=1))
json.dump(out, open("quantitative_witness_check.json", "w"), indent=1)
