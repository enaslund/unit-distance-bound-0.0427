"""Frobenius census for the tower over B=Q(sqrt 241): lower bounds for residue degrees.

For each prime P of B (not above 2,3,5,7,29) with norm <= X:
  v = degree-one Frobenius vector (Legendre symbols of the Kummer basis);
  f_rel >= 1 if v == 0, >= 2 if v != 0, >= 4 if S(v) is not in the quadratic relation span.
Contribution bound to lim (1/[K:Q]) log zeta_K(1):  a_1(N^f)/(2 f)  with f = f_min (relative, N=norm of P).
"""
import sys
import math
import numpy as np
from lie241 import S, rels, names, f2rank

D = 241
# Kummer basis as (a, b, den): alpha = (a + b sqrt D)/den
KB = [(-1, 0, 1), (-71011068, 4574225, 1), (-6101, -393, 2), (6101, -393, 2), (31, -2, 1), (31, 2, 1), (326, -21, 1), (326, 21, 1)]
NORMS = [1, -1, -2, -2, -3, -3, -5, -5]
SELECTED = {2, 3, 5, 7, 29}

# which v in F2^8 have S(v) in the relation span R2
Q = [m for m, nm in zip(rels, names) if nm != "demuskin1"]
Qm = np.array([m.flatten() for m in Q], dtype=np.uint8)
r0 = f2rank(Qm)
sq_in_R = {}
for code in range(256):
    v = np.array([(code >> i) & 1 for i in range(8)], dtype=np.uint8)
    sq_in_R[code] = f2rank(np.vstack([Qm, S(v).flatten()])) == r0


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def sqrtmod(a, p):
    # Tonelli-Shanks
    a %= p
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while legendre(z, p) != -1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, tt = 0, t
        while tt != 1:
            tt = tt * tt % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r


def a1(q):
    return -math.log1p(-1.0 / q)


def census(X):
    tot = 0.0
    stats = {"v0": 0, "f2": 0, "f4": 0}
    contrib = {"v0": 0.0, "f2": 0.0, "f4": 0.0}
    for p in primes_upto(X):
        if p in SELECTED:
            continue
        if p == D:
            places = [(p, [(a * pow(den, -1, p)) % p for (a, b, den) in KB])]
        elif legendre(D, p) == 1:
            r = sqrtmod(D, p)
            places = []
            for rr in (r, p - r):
                places.append((p, [((a + b * rr) * pow(den, -1, p)) % p for (a, b, den) in KB]))
        else:
            if p * p > X:
                continue
            places = [(p * p, None)]
        for N, res in places:
            if res is None:
                code = sum((1 << i) for i, nm in enumerate(NORMS) if legendre(nm, p) == -1)
            else:
                code = sum((1 << i) for i, a in enumerate(res) if legendre(a, p) == -1)
            if code == 0:
                f, key = 1, "v0"
            elif sq_in_R[code]:
                f, key = 2, "f2"
            else:
                f, key = 4, "f4"
            c = a1(N**f) / (2 * f)
            tot += c
            stats[key] += 1
            contrib[key] += c
    return tot, stats, contrib


if __name__ == "__main__":
    X = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**6
    print("vectors v with S(v) in R2:", sum(sq_in_R.values()), "of 256")
    tot, st, co = census(X)
    print("X =", X, " middle-term bound =", tot)
    print(" counts", st, " contributions", {k: round(v, 6) for k, v in co.items()})
    ell = 2.25 * math.log(2) + 0.5 * math.log(15) + 0.5 * math.log(241)
    Bb = (ell - 0.5772156649 - math.log(4 * math.pi)) / 2
    def w(q):
        return 2 * math.log(q) * sum(1 / (q**m + 1) for m in range(1, 8))
    sel = 0.25 * w(9) + 0.25 * w(25) + w(16) / 32 + 0.25 * w(29**4) + w(7**8) / 8
    Brem = Bb - sel
    rX = a1(X) / w(X)
    print("B =", Bb, " selected budget =", sel, " B_rem =", Brem, " r(X) =", rX, " tail =", rX * Brem)
    print("total hidden-mass bound C - B_sel <=", tot + rX * Brem)
