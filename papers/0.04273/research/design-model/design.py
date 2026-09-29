"""Design optimizer: Golod-Shafarevich block costs vs margin.

Model (not a proof):
  P(t) = 1 - d t + sum(blocks) - s_D(t) + rho_r * (t - c1(t))
  margin(delta) = sum selected prime terms - (1/2-delta) ell - C_slack + arch
Generators d = 2 (for -1 and 2) + |T| (odd ramified primes).
"""
import functools
import itertools
import numpy as np
from model import best_local, JD_gauss, JR_gauss, JC_gauss, LOG2, LOGPI, p_of

C_SLACK = 0.042161819 - 0.0417395026096140600456
JD_IMPROVE = 1.3796353243188504 - JD_gauss(83647 / 2000000)  # profile gain over Gaussian


def c1(t):
    return t * t / (1 + t)


def PD(t):
    return (1 + t)**3 * (1 + t * t)**2


def dyadic(t):
    dD = 3 * t - 1 + 1 / PD(t)
    sD = t * t * (1 - t**7 / PD(t))
    return dD - sD


def block(t, e, f):
    """Cost of local block with inertia C_e (e in 1,2) and Frobenius order f, both generators present."""
    if e == 1:
        # unramified cyclic C_f, one generator
        P = 1.0
        g = 1
        while g < f:
            P *= (1 + t**g)
            g *= 2
        return t - 1 + 1 / P
    # e == 2: C_2 x C_f  (two generators); f=1 would need killing a degree-one Frobenius
    P = (1 + t)
    g = 1
    while g < f:
        P *= (1 + t**g)
        g *= 2
    return 2 * t - 1 + 1 / P


def uncapped(t):
    # inertia C_2, Frobenius free: local image C_2 x Z_2, P=(1+t)/(1-t); cost 2t-1+(1-t)/(1+t)
    return 2 * t * t / (1 + t)


@functools.lru_cache(maxsize=None)
def pterm(delta_key, q, e, f):
    delta = delta_key / 1e9
    Q = float(q)**f
    v, k, _ = best_local(delta, Q, kmax=40, shells=False)
    return (v + np.log(1 - 1 / Q)) / (e * f), k


def pt(delta, q, e, f):
    return pterm(int(round(delta * 1e9)), q, e, f)[0]


def arch(delta, rho_r, theta=4095 / 8192, JR_improve=0.0):
    JD = JD_gauss(delta) + JD_IMPROVE
    JR = JR_gauss(delta) + JR_improve
    JC = JC_gauss(delta)
    SR = LOG2 + JR
    NR = (1 - delta) * LOG2 + LOGPI + JC
    CX = (1 - delta) * LOG2 + (LOGPI + JD) / 2
    mixed = (1 - 2 * theta) * NR + 2 * theta * CX
    return rho_r * SR + (1 - rho_r) * mixed


PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]


def evaluate(delta, t, T, unram, rho_r, JR_improve=0.0):
    """T: dict odd ramified prime -> type ('U' or f in {2,4,8}); unram: dict prime -> f."""
    d = 2 + len(T)
    P = 1 - d * t + dyadic(t) + c1(t) + rho_r * (t - c1(t))
    ell = 2.25 * LOG2
    M = 0.0
    # dyadic prime contribution (e=8,f=4)
    M += pt(delta, 2, 8, 4)
    for q, ty in T.items():
        ell += 0.5 * np.log(q)
        if ty == 'U':
            P += uncapped(t)
        else:
            P += block(t, 2, ty)
            M += pt(delta, q, 2, ty)
    for q, f in unram.items():
        P += block(t, 1, f)
        M += pt(delta, q, 1, f)
    M += -(0.5 - delta) * ell - C_SLACK + arch(delta, rho_r, JR_improve=JR_improve)
    return P, M


if __name__ == "__main__":
    d0 = 83647 / 2000000
    T0 = {3: 2, 5: 2, 7: 4, 11: 4, 13: 4}
    U0 = {17: 4, 19: 4, 23: 4, 29: 4, 31: 4}
    P, M = evaluate(d0, 11 / 34, T0, U0, 0.0)
    print("current design: P(11/34) =", P, " margin(hard windows) =", M)
    # slope
    h = 1e-4
    _, M1 = evaluate(d0 + h, 11 / 34, T0, U0, 0.0)
    print("dM/ddelta ~", (M1 - M) / h)
    print("arch SR-CX at d0:", arch(d0, 1) - arch(d0, 0))
