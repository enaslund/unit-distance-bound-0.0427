#!/usr/bin/env python3
"""Dirichlet coefficients of the 64 twisted dihedral L-functions of one D4 field (data: ddata_orb<o>.json).

L_w = zeta(K_w)/zeta(Bc), Bc = B(sqrt c), K_w = Bc(sqrt gamma_w), gamma_w = gamma0 alpha^w, gamma0 = g0 + g1 sqrt c.
Euler factors: p = 2, 3, 5 and 7 <= p <= 1000 exported from PARI (exact prime decompositions); for p > 1000
only primes split in B contribute below N (an inert p has norm p^2 > 10^6 > N), and at the degree-one prime
(p, sqrt241 - r), with G_i = g_i(r) alpha^w(r) mod p:
  c(r) a nonzero square:  two primes of Bc of norm p,   chi = (G0 +- G1 sqrt c(r) | p);
  c(r) a nonsquare:       one prime of norm p^2,        chi = (G0^2 - c(r) G1^2 | p).
"""
import json
import sys
from math import isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent.parent / "0.04273/certificates"))
from census241 import legendre, sqrtmod, KB  # noqa: E402

PSMALL = 1000


def load(orbit):
    return json.loads((HERE / f"ddata_orb{orbit}.json").read_text())


def belt(e, r, p):
    a, b, d = e
    return (a + b * r) * pow(d, -1, p) % p


def alpha_w(w, r, p):
    v = 1
    for k, bit in enumerate(w):
        if bit:
            aa, bb, den = KB[k]
            v = v * ((aa + bb * r) * pow(den, -1, p)) % p
    return v


def spf_sieve(n):
    spf = list(range(n + 1))
    for i in range(2, isqrt(n) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def series_inverse(P, kmax):
    c = [1] + [0] * kmax
    for k in range(1, kmax + 1):
        c[k] = -sum(P[j] * c[k - j] for j in range(1, min(k, len(P) - 1) + 1))
    return c


def polymul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def local_poly(data, tw, p):
    """denominator polynomial P(X) of the local factor 1/P(p^-s); None if p is inert in B and p > PSMALL"""
    if p in (2, 3, 5):
        return tw["bad"][str(p)]
    if p <= PSMALL:
        return tw["small"][str(p)]
    if legendre(241, p) != 1:
        return None
    r = sqrtmod(241, p)
    P = [1]
    for rr in (r, p - r):
        cr = belt(data["c"], rr, p)
        aw = alpha_w(tw["w"], rr, p)
        G0 = belt(data["g0"], rr, p) * aw % p
        G1 = belt(data["g1"], rr, p) * aw % p
        lc = legendre(cr, p)
        assert lc != 0
        if lc == 1:
            sc = sqrtmod(cr, p)
            for sg in (1, -1):
                chi = legendre((G0 + sg * G1 * sc) % p, p)
                assert chi != 0
                P = polymul(P, [1, -chi])
        else:
            chi = legendre((G0 * G0 - cr * G1 * G1) % p, p)
            assert chi != 0
            P = polymul(P, [1, 0, -chi])
    return P


def coefficients(data, tw, spf=None, M=None):
    """(Q, N, [a_0, ..., a_N]) with N = floor(4 sqrt Q) + 1 (the AFE length), or N = M if given"""
    Q = tw["Q"]
    N = isqrt(16 * Q) + 1 if M is None else M
    assert N < PSMALL**2
    if spf is None or len(spf) <= N:
        spf = spf_sieve(N)
    a = [0] * (N + 1)
    a[1] = 1
    local = {}
    for n in range(2, N + 1):
        p = spf[n]
        m, k = n, 0
        while m % p == 0:
            m //= p
            k += 1
        if p not in local:
            P = local_poly(data, tw, p)
            if P is None:
                assert p * p > N
                local[p] = [1, 0]
            else:
                kmax = 1
                while p ** (kmax + 1) <= N:
                    kmax += 1
                local[p] = series_inverse(P, kmax)
        loc = local[p]
        a[n] = (loc[k] if k < len(loc) else 0) * a[m]
    return Q, N, a
