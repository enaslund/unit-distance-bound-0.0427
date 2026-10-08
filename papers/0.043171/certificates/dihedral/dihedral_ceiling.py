#!/usr/bin/env python3
"""Analytic ceiling with the Kummer field E replaced by E_W = E M_10 M_23 (README Section 9), with the D4 census
and the adaptive dichotomy relative to E_W.  All quantities are Arb balls; the output is an upper bound.

  C_W   = Y_W - Delta_sel - Delta_P4 + eps (kappa_oo + R)
  Y_W   = (1/[E_W:Q]) log zeta_{E_W}(sigma) = Y_E/4 + (1/1024) sum_{o in 10,23,24} sum_w log L_{o,w}(sigma)
  Delta_sel: E_W-term minus K-term at the selected primes (the dyadic E_W-term from the exact Euler factors
             of the 192 L-functions at 2; at t1, t2, P41[1] the residue degree f_W = lcm(2, f_D4));
  Delta_P4:  census primes of P_4 with f_W = 2;
  gain  = sum over vector-0 primes with Frobenius in ker W detected by the census of T(N)
          (norms <= XA here, binsBW of census_d3k.c above) + adaptive G_p with floors relative to E_W.
Usage: dihedral_ceiling.py DELTA SIGMA YE_JSON PREFIX [PREFIX ...]   (census prefixes tiling (XA, XC];
       YE_JSON: output of afe241.py at SIGMA; the L-values are read from dafe_orb<o>[_p_q].json)
"""
import json
import math
import re
import sys
from fractions import Fraction as Q
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
CERT = HERE.parent
P241 = CERT.parent.parent / "0.04273/certificates"
P41 = CERT.parent.parent / "0.042901/certificates"
sys.path.insert(0, str(P241))
sys.path.insert(0, str(CERT))
import env241  # noqa: F401,E402
from flint import arb, ctx  # noqa: E402
from interval241 import logderiv_tail_bound  # noqa: E402
import adaptive41 as A  # noqa: E402
import rootcheck as RC  # noqa: E402
import contextlib  # noqa: E402
import io  # noqa: E402
with contextlib.redirect_stdout(io.StringIO()):
    from lie241 import V as LV  # noqa: E402

ctx.prec = 200
ORBITS = (10, 23, 24)
XA = 12 * 10**6


def g(q, s):
    return -(1 - arb(q) ** (-s)).log()


def T(N, s):
    return g(N, s) / 2 - g(N * N, s) / 4


def phi1(code, f):
    v = [(code >> k) & 1 for k in range(8)]
    r1 = [int(c) for c in f["rows"][0]]
    r2 = [int(c) for c in f["rows"][1]]
    return [sum(a * b for a, b in zip(r1, v)) % 2, sum(a * b for a, b in zip(r2, v)) % 2]


def main(delta_q, SIGMA, ye_path, prefixes, lv_dir=None):
    lvd = Path(lv_dir) if lv_dir else HERE                 # directory of the dafe L-value files
    s = arb(SIGMA.numerator) / SIGMA.denominator
    eps = s - 1
    allf = json.loads((HERE / "d4all27.json").read_text())["fields"]
    fams = [allf[o] for o in ORBITS]
    masks = json.loads((HERE / "wmasks.json").read_text())
    mW = [masks["10"], masks["23"]]
    ye = json.loads(Path(ye_path).read_text())
    assert ye["sigma"] == str(SIGMA)
    Y_E = arb(ye["normalized_log_zeta_EB"][0]).union(arb(ye["normalized_log_zeta_EB"][1]))
    sumlog = arb(0)
    tot2 = arb(0)
    tot35 = {3: arb(0), 5: arb(0)}
    for o in ORBITS:
        suffix = "" if SIGMA == Q(301, 300) else f"_{SIGMA.numerator}_{SIGMA.denominator}"
        rows = json.loads((lvd / f"dafe_orb{o}{suffix}.json").read_text())
        assert sorted(r["k"] for r in rows) == list(range(64))
        assert all(r.get("sigma", str(SIGMA)) == str(SIGMA) for r in rows)
        for r in rows:
            L = arb(r["L"][0]).union(arb(r["L"][1]))
            assert L > 0
            sumlog += L.log()
        data = json.loads((HERE / f"ddata_orb{o}.json").read_text())
        x = arb(2) ** (-s)
        for tw in data["twists"]:
            tot2 += -(sum((c * x ** j for j, c in enumerate(tw["bad"]["2"])), arb(0))).log()
            for p in (3, 5):
                xp = arb(p) ** (-s)
                tot35[p] += -(sum((c * xp ** j for j, c in enumerate(tw["bad"][str(p)])), arb(0))).log()
    # [E_W:Q] = 2048; log zeta_{E_W} = log zeta_E + 2 sum log L (each 2-dimensional irreducible twice)
    Y_W = Y_E / 4 + sumlog / 1024
    E2 = 2 * g(4, s) / 16                      # the two dyadic primes, type (4,2) in E/B
    W2 = E2 / 4 + tot2 / 1024                  # their E_W-terms, from the exact Euler factors at 2
    K2 = 2 * g(16, s) / 64                     # their K-terms, type (8,4)
    sel = W2 - K2
    # consistency of the bad Euler factors: above 3 and 5 the types in E, E_W and K coincide, so the E_W-terms
    # computed from the 192 local factors must equal the E-terms 2 g(p^2)/8
    for p in (3, 5):
        Ep = 2 * g(p**2, s) / 8
        Wp = Ep / 4 + tot35[p] / 1024
        assert abs(Wp - Ep) < arb(10) ** -40, (p, Wp, Ep)

    def fW(code):                               # residue degree in E_W/B of an unramified prime of nonzero vector
        return 4 if any(phi1(code, f) == f["rho"] for f in fams) else 2
    for name in ("f291", "f292"):
        if fW(sum(int(b) << k for k, b in enumerate(LV[name]))) == 2:
            sel += g(29**2, s) / 4 - g(29**4, s) / 8
    if fW(A.CAPPED41) == 2:
        sel += g(41**2, s) / 4 - g(41**4, s) / 8
    sav = arb(0)
    Rsum = arb(0)
    for N, c in A.places(A.CENSUS_X):
        if c == 0:
            f0 = 1
        elif A.SQINR[c]:
            f0 = 2
        else:
            f0 = 4
            if fW(c) == 2:
                sav += g(N**2, s) / 4 - g(N**4, s) / 8
        Rsum += arb(N).log() / (2 * (arb(N) ** (2 * f0) - 1))
    X = A.CENSUS_X
    # sum_{n>X} log n/(n^2-1) <= (log X + 1)/(X (1 - X^-2)), every operation in Arb
    # (interval241 of the 1.04273 certificates, as repaired on October 2, 2026)
    Rsum += logderiv_tail_bound(int(X))
    ell = arb(9) / 4 * arb(2).log() + (arb(3).log() + arb(5).log() + arb(241).log()) / 2
    Bhalf = (ell - arb.const_euler() - (4 * arb.pi()).log()) / 4
    R_sel = (2 * arb(2).log() / (2 * 8 * (arb(2) ** (2 * 4) - 1))
             + 2 * arb(3).log() / (2 * 2 * (arb(3) ** (2 * 2) - 1))
             + 2 * arb(5).log() / (2 * 2 * (arb(5) ** (2 * 2) - 1))
             + 2 * arb(29).log() / (2 * (arb(29) ** 8 - 1))
             + 1 * arb(41).log() / (2 * (arb(41) ** 8 - 1)))
    R = R_sel + Rsum
    C_W = Y_W - sel - sav + eps * (Bhalf + R)
    # small norms: census relative to E_W, and the adaptive dichotomy
    delta = arb(delta_q.numerator) / delta_q.denominator
    small = arb(0)
    small_census = arb(0)
    small_adaptive = arb(0)
    qmin = None
    cnt = {"v0_Frobenius_off_kerW": 0, "v0_census": 0, "v0_undetected": 0, "adaptive_terms": 0}
    inert = json.loads((HERE / "inertv0.json").read_text())
    for N, c, rr in A.places(XA, with_root=True):
        f0 = A.f0_of(N, c)
        extra = arb(0)
        if c == 0:
            if rr is not None:
                b = RC.bits(N, rr)
                pat = sum(1 << i for i, x in enumerate(b) if x == -1)
                if any(bin(pat & m).count("1") % 2 for m in mW):
                    f0 = 2
                    cnt["v0_Frobenius_off_kerW"] += 1
                elif pat:
                    f0 = 2
                    extra = T(N, s)
                    cnt["v0_census"] += 1
                else:
                    cnt["v0_undetected"] += 1
            else:
                # vector-0 prime inert over Q (norm p^2): its residue degree in E_W comes from the center bits of
                # inertv0.json (Euler factors of the twist-0 L-functions at p); off ker W it is 2, already in Y_W
                bits = inert[str(int(round(N ** 0.5)))]
                if bits["10"] or bits["23"]:
                    f0 = 2
                    cnt["v0_Frobenius_off_kerW"] += 1
                else:
                    cnt["v0_undetected"] += 1
        else:
            f0 = max(f0, fW(c))
        G = A.gain(N, f0, delta, s, arb(N).log())
        if G > 0:
            cnt["adaptive_terms"] += 1
        small += extra + max(G, 0)
        small_census += extra
        small_adaptive += max(G, 0)
        q0 = N ** f0
        qmin = q0 if qmin is None or q0 < qmin else qmin
    big = arb(0)
    binfo = []
    edge = XA
    for pre in prefixes:
        tp = HERE / (pre + ".txt")
        if tp.exists():
            summ = tp.read_text().splitlines()[-1]
        else:
            import gzip
            summ = gzip.open(str(tp) + ".gz", "rt").read().splitlines()[-1]
        m = re.search(r"XLO (\d+) XHI (\d+) H 2\^-16 NB (\d+)", summ)
        XLO, XHI, NB = int(m.group(1)), int(m.group(2)), int(m.group(3))
        # a D4 value divisible by the prime: census_d3k.c would read it as a square (unsafe in a W field),
        # census_kw.c (mode W) excludes the side; require none in the former, record the latter
        mz = re.search(r" zero (\d+)", summ) or re.search(r" zeroW (\d+)", summ)
        assert mz is not None and (int(mz.group(1)) == 0 or "mode W" in summ), summ
        assert XLO == edge
        edge = XHI
        raw = HERE / (pre + ".binsBW")
        if raw.exists():
            counts = np.fromfile(str(raw), dtype=np.uint64)
        else:
            import gzip
            counts = np.frombuffer(gzip.open(str(raw) + ".gz", "rb").read(), dtype=np.uint64)
        assert len(counts) == NB
        lh = (1 + arb(1) / 65536).log()
        tot = arb(0)
        for j in np.nonzero(counts)[0]:
            U = arb(XLO) * ((int(j) + 2) * lh).exp()          # even for j = NB - 1, U >= XLO (1+H)^(NB+1) > XHI
            tot += int(counts[j]) * arb(T(U, s).lower())
        big += tot
        binfo.append({"XLO": XLO, "XHI": XHI, "binsBW": int(counts.sum()), "sum_T_lower": str(tot.lower())})
    gain = small + big
    out = {"sigma": str(SIGMA), "orbits": ORBITS, "Y_E": str(Y_E), "Y_W": str(Y_W), "dyadic_E_W_term": str(W2),
           "Delta_sel": str(sel), "Delta_P4": str(sav), "R": str(R), "C_W_upper": str(C_W.upper()),
           "small_gain_lower": str(small.lower()), "census_gain_lower": str(big.lower()), "counts": cnt,
           "bins": binfo, "XC": edge, "C_eff_upper": str((C_W - gain).upper())}
    print(json.dumps(out, indent=1))
    main.components = {"Y_W": Y_W, "sel": sel, "sav": sav, "R": R, "Bhalf": Bhalf, "eps": eps,
                       "census_small": small_census, "adaptive_small": small_adaptive, "census_bins": big,
                       "qmin_rest_upto_XA": qmin, "XA": XA}
    return C_W, gain


if __name__ == "__main__":
    main(Q(sys.argv[1]), Q(sys.argv[2]), sys.argv[3], sys.argv[4:])
