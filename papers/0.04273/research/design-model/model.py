"""Approximate margin model for the unit-distance construction.

Not a certificate: floating point, used only to compare designs.
"""
import numpy as np
from scipy.special import k0, k1
from scipy.optimize import minimize_scalar, minimize, brentq

LOG2, LOGPI = np.log(2), np.log(np.pi)


def p_of(delta):
    return 2 / (1 + delta)


# ---------- archimedean functionals (Gaussian profiles) ----------
def JC_gauss(delta):
    p = p_of(delta)
    return np.log(p / 2) - delta * LOGPI + delta * np.log(2 * p * delta) - delta


def JD_gauss(delta):
    # complex pair: 2 log(p/2) - 2 delta log pi + max_z [2 delta log(p z) + log K0(z)]
    p = p_of(delta)
    f = lambda lz: -(2 * delta * np.log(p * np.exp(lz)) + np.log(k0(np.exp(lz))))
    r = minimize_scalar(f, bounds=(-60, 5), method="bounded", options={"xatol": 1e-12})
    return 2 * np.log(p / 2) - 2 * delta * LOGPI - r.fun


def JR_gauss(delta):
    # split real pair on R^2: log(p/2) - delta log pi + max_z [delta log(p z) + log K0(z)]
    p = p_of(delta)
    f = lambda lz: -(delta * np.log(p * np.exp(lz)) + np.log(k0(np.exp(lz))))
    r = minimize_scalar(f, bounds=(-80, 5), method="bounded", options={"xatol": 1e-12})
    return np.log(p / 2) - delta * LOGPI - r.fun


def arch_per_degree(delta, fr_sr=0.0, fr_nr=None, fr_cx=None, JD=None, JR=None, JC=None):
    """Archimedean contribution per degree of F.
    fr_* are fractions of the degree d: split-real b_s/d, nonsplit-real b_n/d, complex 2c/d."""
    JD = JD_gauss(delta) if JD is None else JD
    JR = JR_gauss(delta) if JR is None else JR
    JC = JC_gauss(delta) if JC is None else JC
    SR = LOG2 + JR
    NR = (1 - delta) * LOG2 + LOGPI + JC
    CX = (1 - delta) * LOG2 + (LOGPI + JD) / 2
    return fr_sr * SR + fr_nr * NR + fr_cx * CX


# ---------- finite local functional with symmetric six-shell product weights ----------
def local_logF(delta, Q, k, x=None, nshell=6):
    """log F_{delta} for one prime with residue size Q, exponent k, weights (1,x1..)."""
    p = p_of(delta)
    if x is None:
        x = np.zeros(nshell - 1)
    w = np.concatenate([[1.0], x])
    n = len(w)
    m = np.array([1.0] + [Q**i - Q**(i - 1) for i in range(1, n)])
    D = np.zeros((n, n))
    for i in range(n):
        for r in range(n):
            if i != r:
                D[i, r] = m[min(i, r)]
            elif i == 0:
                D[i, r] = 0.0
            else:
                D[i, r] = i * m[i] - Q**(i - 1)
    A = np.sum(m * w**p)
    B = np.sum(m * w**2)
    R = w @ D @ w
    return -delta * k * np.log(Q) + np.log((k + 1) * B**2 + 2 * B * R) - 2 * (1 + delta) * np.log(A)


def best_local(delta, Q, kmax=60, shells=True):
    best = (-np.inf, None, None)
    for k in range(0, kmax + 1):
        v0 = local_logF(delta, Q, k)
        if shells:
            # optimise log-weights
            def f(lx):
                return -local_logF(delta, Q, k, np.exp(lx))
            x0 = np.log(np.array([1.0 / Q**(0.9 * i) for i in range(1, 6)]))
            r = minimize(f, x0, method="Nelder-Mead", options={"xatol": 1e-10, "fatol": 1e-14, "maxiter": 20000})
            v = max(v0, -r.fun)
        else:
            v = v0
        if v > best[0]:
            best = (v, k, None)
    return best


def prime_term(delta, q, e, f, shells=True, with_C=True):
    """Contribution per degree of F of rational prime q with local indices (e,f),
    all F-primes above q split in K/F: [logF + log(1-1/Q)]/(ef)."""
    Q = float(q)**f
    v, k, _ = best_local(delta, Q, shells=shells)
    c = np.log(1 - 1 / Q) if with_C else 0.0
    return (v + c) / (e * f), k


if __name__ == "__main__":
    d = 83647 / 2000000
    p = p_of(d)
    print("delta", d, "p", p)
    print("JC gauss", JC_gauss(d), " JD gauss", JD_gauss(d), " JR gauss", JR_gauss(d))
    JDstar = 0.6492390240 + LOGPI + 2 * JC_gauss(d)
    print("JD* from certificate slope", JDstar)
    th = 4095 / 8192
    ell = 2.25 * LOG2 + 0.5 * np.log(15015)
    data = {2: (8, 4, 7), 3: (2, 2, 9), 5: (2, 2, 6), 7: (2, 4, 2), 11: (2, 4, 2), 13: (2, 4, 1),
            17: (1, 4, 1), 19: (1, 4, 1), 23: (1, 4, 1), 29: (1, 4, 1), 31: (1, 4, 1)}
    fin = 0
    finhard = 0
    for q, (e, f, k) in data.items():
        Q = float(q)**f
        vh = local_logF(d, Q, k)
        vs, ks, _ = best_local(d, Q)
        fin += vs / (e * f)
        finhard += vh / (e * f)
        print(q, e, f, "k", k, "hard", vh / (e * f), "shell", vs / (e * f), "kbest", ks)
    print("finite hard", finhard, " shells", fin, " (certificate 1.03356692250399)")
    C = 0.042161819
    M = fin - (0.5 - d) * ell - C + (1 - d) * LOG2 + (1 - th) * LOGPI + (1 - 2 * th) * JC_gauss(d) + th * JDstar
    print("margin (model, certificate JD*)", M)
    Mg = fin - (0.5 - d) * ell - C + (1 - d) * LOG2 + (1 - th) * LOGPI + (1 - 2 * th) * JC_gauss(d) + th * JD_gauss(d)
    print("margin (model, gaussian JD)", Mg)
    for fr in [(0, 1, 0), (0, 0, 1), (1, 0, 0)]:
        print("arch per degree fr_sr,nr,cx=", fr, arch_per_degree(d, *fr, JD=JDstar))
