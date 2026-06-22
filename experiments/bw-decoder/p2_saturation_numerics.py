"""
Numerical evidence for bridge predicate P2 (saturation analysis) of the
qubit (Z,X) squashed-extension converse (Conjecture 15.40 route, Step 2).

Quantity: the extension defect (purification identity, April report / Ch. 15)
    q(rho_AC) = H(X|C)_psi + H(Z|E)_psi - 1,
where psi_ACE purifies rho_AC, Z is measured on A with memory E, X with C.
P2 claims: inf over extensions q = 0  ==>  rho_A in the BB84 diamond F_{Z,X}
(|x| + |z| <= 1, y = 0).  We test the contrapositive quantitatively: for
marginals OUTSIDE the diamond, the numerical infimum of q over qubit- and
qutrit-memory extensions stays bounded away from zero, and grows with the
diamond violation |x|+|z|-1.

Parametrization: rho_A fixed; purify into A A'; extension rho_AC obtained by
isometry W: A' -> C tensor E_part... Simpler: psi_ACE = (I_A (x) W)|phi_rhoA>,
W an isometry from A' (dim 2) into C (x) E (dim dC * dE >= 2).
Then rho_AC = Tr_E, and Z-side memory is E = purifying rest.

H(X|C) = H(rho_{X,C}) - H(rho_C) with rho_{X,C} = sum_x (|x><x| (x) Tr_AE[(P_x (x) I) psi]).
"""

import numpy as np
from scipy.optimize import minimize
from scipy.linalg import logm

np.random.seed(11)

I2 = np.eye(2)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Z = np.diag([1.0, -1.0]).astype(complex)
ket = {0: np.array([1, 0], dtype=complex), 1: np.array([0, 1], dtype=complex)}
xbasis = [np.array([1, 1], dtype=complex) / np.sqrt(2),
          np.array([1, -1], dtype=complex) / np.sqrt(2)]
zbasis = [ket[0], ket[1]]


def vN(rho):
    ev = np.linalg.eigvalsh(rho)
    ev = ev[ev > 1e-12]
    return float(-(ev * np.log2(ev)).sum())


def defect(rho_A, W, dC, dE):
    """q = H(X|C) + H(Z|E) - 1 for psi_ACE = (I (x) W)|phi>."""
    ev, U = np.linalg.eigh(rho_A)
    ev = np.clip(ev, 0, None)
    # |phi> = sum_k sqrt(ev_k) |u_k>_A |k>_A'
    phi = np.zeros((2, 2), dtype=complex)
    for k in range(2):
        phi[:, k] = np.sqrt(ev[k]) * U[:, k]
    # psi_{a, c, e} = sum_k phi[a,k] W[(c,e), k]
    Wm = W.reshape(dC * dE, 2)
    psi = np.tensordot(phi, Wm.T, axes=([1], [0]))     # (a, ce)
    psi = psi.reshape(2, dC, dE)

    def cond_ent(basis, mem_axis):
        # measure A in `basis`; memory = axis mem_axis (1=C, 2=E); trace other
        ps, rhos = [], []
        for b in basis:
            amp = np.tensordot(b.conj(), psi, axes=([0], [0]))  # (c, e)
            if mem_axis == 1:
                r = amp @ amp.conj().T            # on C
            else:
                r = amp.T @ amp.conj()            # on E  -- careful below
            ps.append(float(np.trace(r).real))
            rhos.append(r)
        # H(meas, M) - H(M):
        rho_M = sum(rhos)
        Hjoint = 0.0
        for p, r in zip(ps, rhos):
            if p > 1e-12:
                Hjoint += p * vN(r / p) - p * np.log2(p)
        return Hjoint - vN(rho_M)

    HX_C = cond_ent(xbasis, 1)
    HZ_E = cond_ent(zbasis, 2)
    return HX_C + HZ_E - 1.0


def min_defect(rho_A, dC=2, dE=2, restarts=8):
    best = np.inf
    npar = dC * dE * 2
    for _ in range(restarts):
        x0 = np.random.randn(2 * npar)

        def obj(x):
            M = (x[:npar] + 1j * x[npar:]).reshape(dC * dE, 2)
            # closest isometry via QR/polar
            q, r = np.linalg.qr(M)
            Wm = q[:, :2] @ np.diag(np.sign(np.diag(r))[:2] + (np.diag(r)[:2] == 0))
            return defect(rho_A, Wm, dC, dE)

        res = minimize(obj, x0, method='Nelder-Mead',
                       options={'maxiter': 4000, 'fatol': 1e-10, 'xatol': 1e-8})
        best = min(best, res.fun)
    return best


def bloch(x, y, z):
    Y = np.array([[0, -1j], [1j, 0]])
    return 0.5 * (I2 + x * X + y * Y + z * Z)


if __name__ == '__main__':
    rows = []
    # along the diagonal direction x = z = s/sqrt(2): |x|+|z| = s*sqrt(2)
    for s in (0.55, 0.65, 0.7071, 0.75, 0.80, 0.85, 0.90):
        v = s / np.sqrt(2)
        rho = bloch(v, 0.0, v)
        q22 = min_defect(rho, 2, 2)
        q33 = min_defect(rho, 3, 3, restarts=5)
        viol = 2 * v - 1
        rows.append((s, 2 * v, viol, q22, q33))
        print(f"s={s:.4f}  |x|+|z|={2*v:.4f}  violation={viol:+.4f}  "
              f"min q (2x2 mem)={q22:.5f}  (3x3 mem)={q33:.5f}", flush=True)
    # inside-diamond sanity: defect should reach ~0
    np.save('p2_rows.npy', np.array(rows))
