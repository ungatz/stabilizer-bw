"""
Tests of the new structural analysis of q = 0 saturators (P2 attack).

q(rho_AM) = H(Dz rho) + H(Dx rho) - H(rho) - H(Dcap rho)   [Thm reconciliation]

New theory being tested:
 (T1) {b, c} = 0 for near-saturators, where log rho = I(x)a + Z(x)b + X(x)c
      (b, c = Pauli components of log rho as memory operators).
 (T2) Bell-sector rigidity: rho = exp(I(x)a + beta Z(x)Z_M + gamma X(x)X_M)
      saturates iff a is scalar (a ~ I_M), i.e. q > 0 whenever a has
      nontrivial X_M/Y_M/Z_M components (for beta, gamma != 0).
 (T3) Claim Y: marginals with y != 0 have inf q > 0.
"""
import numpy as np
from scipy.linalg import expm, logm
from scipy.optimize import minimize

np.random.seed(3)
I2 = np.eye(2); X = np.array([[0,1],[1,0]],dtype=complex)
Y = np.array([[0,-1j],[1j,0]]); Z = np.diag([1.,-1.]).astype(complex)
Hh = (X+Z)/np.sqrt(2)

def kron(*ms):
    out = ms[0]
    for m in ms[1:]: out = np.kron(out, m)
    return out

def vN(r):
    ev = np.linalg.eigvalsh(r); ev = ev[ev>1e-14]
    return float(-(ev*np.log2(ev)).sum())

def dephase_blocks(rho, basis_vectors, dM):
    """Pinch A in given basis: sum_k (Pk (x) I) rho (Pk (x) I)."""
    out = np.zeros_like(rho)
    for v in basis_vectors:
        P = np.outer(v, v.conj())
        PI = np.kron(P, np.eye(dM))
        out += PI @ rho @ PI
    return out

zb = [np.array([1,0],dtype=complex), np.array([0,1],dtype=complex)]
xb = [np.array([1,1],dtype=complex)/np.sqrt(2), np.array([1,-1],dtype=complex)/np.sqrt(2)]

def q_defect(rho, dM):
    Dz = dephase_blocks(rho, zb, dM)
    Dx = dephase_blocks(rho, xb, dM)
    rM = np.trace(rho.reshape(2,dM,2,dM), axis1=0, axis2=2)
    Dcap = np.kron(I2/2, rM)
    return vN(Dz) + vN(Dx) - vN(rho) - vN(Dcap)

def pauli_components_logrho(rho, dM):
    L = logm(rho)
    L = (L + L.conj().T)/2
    Lr = L.reshape(2,dM,2,dM)
    comp = {}
    for name, Pa in (('I',I2),('Z',Z),('X',X),('Y',Y)):
        # m = (1/2) Tr_A[(Pa^dag (x) I) L]
        m = np.einsum('ab,bjak->jk', Pa.conj().T, Lr)/2
        comp[name] = m
    return comp

# ---------------- T2: Bell-sector rigidity, dM = 2 ----------------
def bell_state(beta, gamma, avec):
    a = avec[0]*I2 + avec[1]*X + avec[2]*Y + avec[3]*Z
    H = kron(I2, a) + beta*kron(Z, Z) + gamma*kron(X, X)
    r = expm(H); return r/np.trace(r).real

print("== T2: Bell-sector rigidity (q vs nontrivial a), beta=0.7 gamma=0.4")
for avec, lbl in [((0,0,0,0),'a=0 (scalar)'), ((0.3,0,0,0),'a=0.3 I (scalar)'),
                  ((0,0.25,0,0),'a_x=0.25'), ((0,0,0.25,0),'a_y=0.25'),
                  ((0,0,0,0.25),'a_z=0.25'), ((0,0.1,0.1,0.1),'a=0.1(x+y+z)')]:
    r = bell_state(0.7, 0.4, avec)
    print(f"  {lbl:18s} q = {q_defect(r,2):.8f}")

# scaling: q vs ||a_perp||^2 ?
print("  scaling (a_z = eps):", end=" ")
for eps in (0.2, 0.1, 0.05, 0.025):
    r = bell_state(0.7, 0.4, (0,0,0,eps))
    print(f"q({eps})={q_defect(r,2):.2e}", end="  ")
print()

# ---------------- T1: {b,c} -> 0 along minimizing sequences ----------------
print("== T1: anticommutator {b,c} for near-saturating extensions (dM=2)")
def rand_herm(d, rng, s=1.0):
    M = rng.normal(size=(d,d))*s + 1j*rng.normal(size=(d,d))*s
    return (M+M.conj().T)/2

rng = np.random.default_rng(5)
def min_q_logform(dM, iters=3, pin=None, seed_state=None):
    """Minimize q over rho = exp(H), H arbitrary Hermitian on 2*dM (full family),
       optionally pinning the A-marginal via penalty."""
    d = 2*dM
    best = (np.inf, None)
    for _ in range(iters):
        x0 = rng.normal(size=d*d)
        def make(x):
            M = np.zeros((d,d),dtype=complex); idx=0
            for i in range(d):
                M[i,i] = x[idx]; idx+=1
            for i in range(d):
                for j in range(i+1,d):
                    M[i,j] = x[idx] + 1j*x[idx+1]; M[j,i] = x[idx]-1j*x[idx+1]; idx+=2
            r = expm(M[:d,:d] if False else (M+M.conj().T)/2)
            return r/np.trace(r).real
        def obj(x):
            r = make(x)
            val = q_defect(r, dM)
            if pin is not None:
                rA = np.trace(r.reshape(2,dM,2,dM), axis1=1, axis2=3)
                tgt = 0.5*(I2 + pin[0]*X + pin[1]*Y + pin[2]*Z)
                val += 30*np.linalg.norm(rA - tgt)**2
            return val
        res = minimize(obj, x0, method='L-BFGS-B', options={'maxiter':400})
        if res.fun < best[0]: best = (res.fun, make(res.x))
    return best

for trial in range(3):
    qv, r = min_q_logform(2, iters=2)
    comp = pauli_components_logrho(r, 2)
    b, c = comp['Z'], comp['X']
    ac = b@c + c@b
    print(f"  q={qv:.2e}  ||{{b,c}}||={np.linalg.norm(ac):.3e}  ||b||={np.linalg.norm(b):.2f} ||c||={np.linalg.norm(c):.2f}  ||Y-comp logrho||={np.linalg.norm(comp['Y']):.2e}")

# ---------------- T3: y != 0 marginals ----------------
print("== T3: pinned marginals with y != 0 (penalty method, dM=2): inf q")
for pin in [(0.0,0.3,0.0), (0.3,0.3,0.3), (0.0,0.15,0.4), (0.2,0.0,0.2)]:
    qv, r = min_q_logform(2, iters=3, pin=pin)
    rA = np.trace(r.reshape(2,2,2,2), axis1=1, axis2=3)
    got = [np.trace(rA@P).real for P in (X,Y,Z)]
    print(f"  pin (x,y,z)={pin}: min[q + pen] = {qv:.5f}, achieved marginal ~ ({got[0]:.3f},{got[1]:.3f},{got[2]:.3f})")
