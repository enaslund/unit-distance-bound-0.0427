#!/usr/bin/env python3
"""Total certified gain of the adaptive census over the 41-cap ceiling (README Sections 5-8).

Two parts, both certified lower bounds with Arb balls:

1. Primes of B of norm N <= XA (the free primes of ceiling41.py; adaptive41.py enumerates them).
   A degree-one prime with Frobenius vector 0 is tested with the fifteen D4 fields of
   d4fields15.json (Lemma 2): if one beta_i is a nonsquare at it, its floor becomes f0 = 2, and it
   contributes the census correction T(N) = g_sigma(N)/2 - g_sigma(N^2)/4 plus the adaptive G(p)
   computed with f0 = 2; otherwise it contributes G(p) with the floor of ceiling41.py.
2. Degree-one primes with vector 0 and XA < N <= XC that census_d3.c detects (binned counts in
   <prefix>.bins; each bin j holds primes below XA (1 + 2^-16)^(j+1), and T is decreasing, so the
   bound uses T at XA (1 + 2^-16)^(j+2) to absorb a floating-point misassignment by one bin).

Usage: census_gain.py DELTA SIGMA XA PREFIX [PREFIX ...]   (the census files must tile (XA, XC])
"""
import gzip
import json
import re
import sys
from fractions import Fraction as Q
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import adaptive41 as A  # noqa: E402  (imports env241, flint, census241)
from adaptive41 import arb, g, gain, f0_of  # noqa: E402
from census241 import legendre, sqrtmod, KB  # noqa: E402

FIELDS = json.loads((HERE / "d4fields15.json").read_text())
for f in FIELDS:
    f["r1"] = [int(c) for c in f["rows"][0]]
    f["r2"] = [int(c) for c in f["rows"][1]]
    f["co"] = [Q(c) for c in f["coords"]]


def d4_detects(p, rr):
    """True if some beta_i is a nonsquare at the degree-one prime (p, sqrt241 - rr) of vector 0."""
    al = [((aa + b * rr) * pow(den, -1, p)) % p for (aa, b, den) in KB]
    q = [sqrtmod(a, p) for a in al]
    assert all(x * x % p == a for x, a in zip(q, al))
    for f in FIELDS:
        sa = sb = 1
        for k in range(8):
            if f["r1"][k]:
                sa = sa * q[k] % p
            if f["r2"][k]:
                sb = sb * q[k] % p
        bas = [1, rr, sa, rr * sa, sb, rr * sb, sa * sb, rr * sa * sb]
        val = sum((c.numerator % p) * pow(c.denominator, -1, p) * b for c, b in zip(f["co"], bas)) % p
        if legendre(val, p) == -1:
            return True
    return False


def T(N, s):
    return g(N, s) / 2 - g(N * N, s) / 4


def small_part(delta, s, XA):
    """Primes of norm <= XA: (lower bound, counts)."""
    total = arb(0)
    cnt = {"detected_v0": 0, "undetected_v0": 0, "adaptive_terms": 0}
    for N, c, rr in A.places(XA, with_root=True):
        f0 = f0_of(N, c)
        extra = arb(0)
        if f0 == 1 and rr is not None and d4_detects(N, rr):
            f0 = 2
            extra = T(N, s)
            cnt["detected_v0"] += 1
        elif f0 == 1:
            cnt["undetected_v0"] += 1
        G = gain(N, f0, delta, s, arb(N).log())
        if G > 0:
            cnt["adaptive_terms"] += 1
        total += extra + max(G, 0)
    return total, cnt


def bins_part(prefix, s):
    summ = Path(prefix + ".txt").read_text().splitlines()[-1]
    m = re.search(r"XLO (\d+) XHI (\d+) H 2\^-16 NB (\d+) candidates (\d+) v0 (\d+) detected (\d+) zero (\d+)", summ)
    XLO, XHI, NB = int(m.group(1)), int(m.group(2)), int(m.group(3))
    if Path(prefix + ".bins").exists():
        counts = np.fromfile(prefix + ".bins", dtype=np.uint64)
    else:
        with gzip.open(prefix + ".bins.gz", "rb") as fh:
            counts = np.frombuffer(fh.read(), dtype=np.uint64)
    assert len(counts) == NB and int(counts.sum()) == int(m.group(6))
    lh = (1 + arb(1) / 65536).log()
    tot = arb(0)
    for j in np.nonzero(counts)[0]:
        U = arb(XLO) * ((int(j) + 2) * lh).exp()
        if int(j) == NB - 1:
            U = arb(max(int(U.upper()) + 1, XHI))
        tot += int(counts[j]) * arb(T(U, s).lower())
    return tot, {"XLO": XLO, "XHI": XHI, "v0": int(m.group(5)), "detected": int(m.group(6)), "zero": int(m.group(7))}


def main(delta_q, sigma_q, XA, prefixes):
    delta = arb(delta_q.numerator) / delta_q.denominator
    s = arb(sigma_q.numerator) / sigma_q.denominator
    small, cnt = small_part(delta, s, XA)
    out = {"delta": str(delta_q), "sigma": str(sigma_q), "XA": XA, "small_part_lower": str(small.lower()),
           "small_counts": cnt, "census": []}
    total = small
    edge = XA
    for pre in prefixes:
        b, info = bins_part(pre, s)
        assert info["XLO"] == edge, (info["XLO"], edge)   # the census ranges tile (XA, XC]
        edge = info["XHI"]
        total += b
        info["sum_T_lower"] = str(b.lower())
        out["census"].append(info)
    out["XC"] = edge
    out["gain_lower"] = str(total.lower())
    print(json.dumps(out, indent=1))
    return total


if __name__ == "__main__":
    main(Q(sys.argv[1]), Q(sys.argv[2]), int(float(sys.argv[3])), sys.argv[4:])
