#!/usr/bin/env python3
"""Adaptive census gain for the 41-cap tower over B = Q(sqrt 241).

For a prime p of B outside S = {primes above 2,3,5} and the capped primes (both
primes above 29, the prime P41[1] above 41), with N = Np <= X, let f0 be the
residue degree used for p in Y_* (ceiling41.py): f0 = 1 if the Frobenius vector
v is 0; f0 = 4 if v is not in Sigma_2 and N <= 10^6 (the census set P_4);
f0 = 2 otherwise.  For a field K of the family let f = f_K(p) in {f0, 2 f0, ...}
and rho in [0,1] the proportion of primes of K above p fixed by iota_1.  Then
(adaptive ceiling and transfer, see ../README.md) the margin increases by at least
    R(f) + rho I(f) + (1 - rho) S(f),
    R(f) = g_sigma(N^f0)/(2 f0) - g_sigma(N^f)/(2 f)      (smaller zeta_K(sigma))
    I(f) = artanh(N^(-f/2))/f   (f even; else rho = 0)    (inert places of F in K)
    S(f) = max(0, max_k [log(k+1) - delta k f log N])/(2 f)  (unweighted shell
           profiles with parameters (N^f, k) at the places of F above p split in K).
G(p) is the minimum over f and rho in {0,1} (the expression is affine in rho, and
once S(f) = 0 larger f only increase R).  Output: a certified lower bound for
sum_p G(p), with outward-rounded Arb balls.
"""
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
Q241 = HERE.parent.parent / "0.04273/certificates"
sys.path.insert(0, str(Q241))
import env241  # noqa: E402,F401
from flint import arb, ctx  # noqa: E402
from census241 import legendre, sqrtmod, KB, NORMS  # noqa: E402

ctx.prec = 160
SQINR = [int(x) for x in (Q241 / "sqinR.txt").read_text().split()]
CAPPED41 = 28          # P41[1], vector [0,0,1,1,1,0,0,0] (check41.py)
CENSUS_X = 10**6       # census range of P_4 in ceiling41.py (census_saving_and_R(s, X=10**6))
KMAX = 60


def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return s


def code_at(p, rr):
    c = 0
    for i, (aa, b, den) in enumerate(KB):
        if legendre(((aa + b * rr) * pow(den, -1, p)) % p, p) == -1:
            c |= 1 << i
    return c


def places(X, with_root=False):
    """Free primes of B with norm <= X: (N, code), or (N, code, r) with r = sqrt 241 mod p at a
    degree-one prime (p, sqrt241 - r) and r = None at the other primes (inert p, and p = 241)."""
    s = sieve(X)
    for p in range(7, X + 1):
        if not s[p] or p == 29:
            continue
        if p == 241:
            c = sum((1 << i) for i, (aa, b, den) in enumerate(KB)
                    if legendre((aa * pow(den, -1, p)) % p, p) == -1)
            yield (p, c, None) if with_root else (p, c)
        elif legendre(241, p) == 1:
            r = sqrtmod(241, p)
            for rr in (r, p - r):
                c = code_at(p, rr)
                if p == 41 and c == CAPPED41:
                    continue
                yield (p, c, rr) if with_root else (p, c)
        elif p * p <= X:
            c = sum((1 << i) for i, nm in enumerate(NORMS) if legendre(nm, p) == -1)
            yield (p * p, c, None) if with_root else (p * p, c)


def f0_of(N, c):
    if c == 0:
        return 1
    if not SQINR[c] and N <= CENSUS_X:
        return 4
    return 2


def g(q, s):
    return -(1 - arb(q) ** (-s)).log()


def gain(N, f0, delta, s, logN):
    """Certified lower bound (a float-free arb lower endpoint) for G(p)."""
    base = g(N**f0, s) / (2 * f0)
    best = None
    f = f0
    while True:
        R = base - g(N**f, s) / (2 * f)
        logQ = f * logN
        shell = None
        for k in range(1, KMAX + 1):
            v = (arb(k + 1).log() - delta * k * logQ).lower()
            shell = v if shell is None or v > shell else shell
        Sl = max(arb(0).lower(), shell) / (2 * f)
        cands = [(R + Sl).lower()]
        if f % 2 == 0:
            cands.append((R + (arb(N) ** (-arb(f) / 2)).atanh() / f).lower())
        m = min(cands)
        best = m if best is None or m < best else best
        if shell <= 0:      # S(f) = 0: larger f only increase R
            break
        f *= 2
    return best


def main(delta_q, sigma_q, X):
    delta = arb(delta_q.numerator) / delta_q.denominator
    s = arb(sigma_q.numerator) / sigma_q.denominator
    total = arb(0)
    by = {1: arb(0), 2: arb(0), 4: arb(0)}
    cnt = {1: 0, 2: 0, 4: 0}
    largest_N_with_gain = 0
    for N, c in places(X):
        f0 = f0_of(N, c)
        G = gain(N, f0, delta, s, arb(N).log())
        if G > 0:
            total += G
            by[f0] += G
            cnt[f0] += 1
            largest_N_with_gain = max(largest_N_with_gain, N)
    out = {"delta": str(delta_q), "sigma": str(sigma_q), "X": X,
           "gain_lower": str(total.lower()), "counts": cnt,
           "by_f0": {k: str(v.lower()) for k, v in by.items()},
           "largest_N_with_gain": largest_N_with_gain}
    print(json.dumps(out, indent=1))
    return total


if __name__ == "__main__":
    main(Q(sys.argv[1]), Q(sys.argv[2]) if len(sys.argv) > 2 else Q(301, 300),
         int(float(sys.argv[3])) if len(sys.argv) > 3 else 12 * 10**6)
