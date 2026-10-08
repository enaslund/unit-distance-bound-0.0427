#!/usr/bin/env python3
"""Analytic ceiling with E_W replaced by E_W' = E M_10 M_23 M_19 (W' = span(psi_10, psi_23, psi_19), plane3.py).

  C_W'  = Y_W' - Delta_sel - Delta_P4 + eps (kappa_oo + R)
  Y_W'  = (1/[E_W':Q]) log zeta_{E_W'}(sigma)
        = Y_E/8 + (1/2048) sum_{o in 10,23,24,19,20} sum_w log L_{o,w}(sigma) + (1/1024) sum_{o in 23,24} sum_w log L8_{o,w}(sigma)
  (Gal(E_W'/B) is a central extension of Gal(E/B) = F_2^8 by Z' = F_2^3; its irreducible representations are the 256
   characters, the 5 x 64 two-dimensional rho_o (x) lambda_w (each twice in zeta_{E_W'}) and the 2 x 16
   four-dimensional rho_19 (x) rho_o (x) lambda_w, o = 23, 24 (each four times); [E_W':Q] = 4096.)
  Delta_sel: E_W'-term minus K-term at the selected primes (the dyadic E_W'-term from the exact Euler factors at 2
             of all 352 L-functions; at t1, t2, P41[1] the residue degree f_W' = lcm(2, f_D4));
  Delta_P4:  census primes of P_4 with f_W' = 2;
  gain  = sum over vector-0 primes with Frobenius in ker W' detected by the census of T(N)
          (norms <= XA here, binsBW3 of census_kv3.c / census_kv4.c above) + adaptive G_p with floors relative to E_W'.
The residue degree in E_W'/B of an unramified prime of nonzero vector v is 4 iff phi_o(v) = rho_o for some o of the
five D4 classes (equivalently some of the quadratic forms of psi_10, psi_23, psi_19 is 1 at v), else 2.

Usage: dihedral_ceiling3.py [W3|W4] DELTA SIGMA YE_JSON LV_DIR LV3_DIR PREFIX [PREFIX ...]   (default W3; W4 is
  W'' = W' + psi_17, with [E_W'':Q] = 8192, orbits 17, 7 and six more degree-8 families, and the binsBW4 bins)
  LV_DIR: dafe_orb<o>_<p>_<q>.json (o = 10, 23, 24); LV3_DIR: orb19_<p>_<q>.json, orb20_..., deg8_19_23_..., deg8_19_24_...
  (leval.py); census prefixes (census_kv3.c or census_kv4.c, the ker-W' bins binsBW3) tiling (XA, XC].
"""
import contextlib
import gzip
import io
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
sys.path.insert(0, str(P241))
sys.path.insert(0, str(CERT))
import env241  # noqa: F401,E402
from flint import arb, ctx  # noqa: E402
from interval241 import logderiv_tail_bound  # noqa: E402
import adaptive41 as A  # noqa: E402
import rootcheck as RC  # noqa: E402
with contextlib.redirect_stdout(io.StringIO()):
    from lie241 import V as LV  # noqa: E402

ctx.prec = 200
XA = 12 * 10**6
DEG8_BAD = HERE / "deg8" / "deg8_bad.json"
# the spaces of functionals: W' (dimension 3) and W'' = W' + psi_17 (dimension 4, plane3.py / fourth form)
SPACES = {
    "W3": {"dim": 3, "orbits": (10, 23, 24, 19, 20), "families": ((19, 23), (19, 24)), "masks": ("10", "23", "19"),
           "bins": "binsBW3", "inert": "inertv0_3.json", "maskfile": "wmasks3.json"},
    "W4": {"dim": 4, "orbits": (10, 23, 24, 19, 20, 17, 7),
           "families": ((19, 23), (19, 24), (7, 10), (17, 10), (17, 24), (7, 24), (7, 23), (17, 23)),
           "masks": ("10", "23", "19", "17"), "bins": "binsBW4", "inert": "inertv0_4.json", "maskfile": "wmasks4.json"},
}
# W4x: W'' with the L-values of orbits 10, 23, 24 also from hp3/ (dcoef4.c + leval.py, exportg.gp data with Euler
# factors to 3000) instead of hp/ (dafe.py), and the abscissae of hp3/sigma_set3x.txt
SPACES["W4x"] = {**SPACES["W4"], "orbits_from_hp3": (10, 23, 24), "sigma_set": "sigma_set3x.txt"}
SPACES["W3"]["sigma_set"] = SPACES["W4"]["sigma_set"] = "sigma_set3.txt"
SPACE = SPACES["W3"]


def g(q, s):
    return -(1 - arb(q) ** (-s)).log()


def T(N, s):
    return g(N, s) / 2 - g(N * N, s) / 4


def phi1(code, f):
    v = [(code >> k) & 1 for k in range(8)]
    r1 = [int(c) for c in f["rows"][0]]
    r2 = [int(c) for c in f["rows"][1]]
    return [sum(a * b for a, b in zip(r1, v)) % 2, sum(a * b for a, b in zip(r2, v)) % 2]


def read_rows(path, n, sigma):
    rows = json.loads(Path(path).read_text())
    assert sorted(r["k"] for r in rows) == list(range(n)), path
    assert all(r["sigma"] == str(sigma) for r in rows), path
    out = []
    for r in rows:
        L = arb(r["L"][0]).union(arb(r["L"][1]))
        assert L > 0
        out.append((r, L))
    return out


def local(P, x):
    return -(sum((c * x ** j for j, c in enumerate(P)), arb(0))).log()


def census_summary(pre):
    """the XLO line and the kerW3 (W') or kerW4 (W'') counts of the current SPACE"""
    tp = HERE / (pre + ".txt")
    txt = tp.read_text() if tp.exists() else gzip.open(str(tp) + ".gz", "rt").read()
    lines = txt.splitlines()
    xl = [ln for ln in lines if ln.startswith("XLO ")]
    w3 = [ln for ln in lines if ln.startswith("W3 ")]
    assert len(xl) == 1 and len(w3) == 1 and lines.index(w3[0]) == lines.index(xl[0]) + 1, pre      # census_kv3/4.c
    masks = json.loads((HERE / SPACE["maskfile"]).read_text())
    m3 = re.search(r"MW3 0x([0-9a-f]+) kerW3 (\d+) kerW3_detected (\d+)", w3[0])
    assert int(m3.group(1), 16) == masks["19"]
    if SPACE["dim"] == 3:
        return xl[0], int(m3.group(2)), int(m3.group(3))
    w4 = [ln for ln in lines if ln.startswith("W4 ")]
    assert len(w4) == 1 and lines.index(w4[0]) == lines.index(w3[0]) + 1, pre                       # census_kv4.c
    m4 = re.search(r"MW4 0x([0-9a-f]+) kerW4 (\d+) kerW4_detected (\d+)", w4[0])
    assert int(m4.group(1), 16) == masks["17"]
    return xl[0], int(m4.group(2)), int(m4.group(3))


def read_bins3(pre):
    summ, kw3, kw3det = census_summary(pre)
    m = re.search(r"XLO (\d+) XHI (\d+) H 2\^-16 NB (\d+)", summ)
    XLO, XHI, NB = int(m.group(1)), int(m.group(2)), int(m.group(3))
    mz = re.search(r" zeroW (\d+)", summ)
    assert mz is not None and "mode W" in summ, summ
    raw = HERE / (pre + "." + SPACE["bins"])
    if raw.exists():
        counts = np.fromfile(str(raw), dtype=np.uint64)
    else:
        counts = np.frombuffer(gzip.open(str(raw) + ".gz", "rb").read(), dtype=np.uint64)
    assert len(counts) == NB and int(counts.sum()) == kw3det
    return XLO, XHI, NB, counts


def main(delta_q, SIGMA, ye_path, lv_dir, lv3_dir, prefixes):
    ORBITS, FAMILIES, dim = SPACE["orbits"], SPACE["families"], SPACE["dim"]
    s = arb(SIGMA.numerator) / SIGMA.denominator
    eps = s - 1
    allf = json.loads((HERE / "d4all27.json").read_text())["fields"]
    fams = [allf[o] for o in ORBITS]
    masks = json.loads((HERE / SPACE["maskfile"]).read_text())
    mW = [masks[k] for k in SPACE["masks"]]
    ye = json.loads(Path(ye_path).read_text())
    assert ye["sigma"] == str(SIGMA)
    Y_E = arb(ye["normalized_log_zeta_EB"][0]).union(arb(ye["normalized_log_zeta_EB"][1]))
    suffix = f"_{SIGMA.numerator}_{SIGMA.denominator}"
    sum4, sum8 = arb(0), arb(0)
    tot2_4, tot2_8 = arb(0), arb(0)
    tot35_4, tot35_8 = {3: arb(0), 5: arb(0)}, {3: arb(0), 5: arb(0)}
    x2 = arb(2) ** (-s)
    xp = {3: arb(3) ** (-s), 5: arb(5) ** (-s)}
    for o in ORBITS:
        from_hp = o in (10, 23, 24) and o not in SPACE.get("orbits_from_hp3", ())
        f = (Path(lv_dir) / f"dafe_orb{o}{suffix}.json") if from_hp else (Path(lv3_dir) / f"orb{o}{suffix}.json")
        rows = read_rows(f, 64, SIGMA)
        data = json.loads((HERE / f"ddata_orb{o}.json").read_text())
        for (r, L), tw in zip(sorted(rows, key=lambda t: t[0]["k"]), data["twists"]):
            assert r["w"] == tw["w"] or json.loads(str(r["w"])) == tw["w"]
            assert int(r["Q"]) == tw["Q"]
            sum4 += L.log()
            tot2_4 += local(tw["bad"]["2"], x2)
            for p in (3, 5):
                tot35_4[p] += local(tw["bad"][str(p)], xp[p])
    bad8 = json.loads(DEG8_BAD.read_text())
    for o1, o in FAMILIES:
        rows = read_rows(Path(lv3_dir) / f"deg8_{o1}_{o}{suffix}.json", 16, SIGMA)
        fam = bad8[f"{o1}_{o}"]
        assert fam["pair"] == [o1, o]
        for (r, L), tw in zip(sorted(rows, key=lambda t: t[0]["k"]), fam["twists"]):
            assert r["w"] == tw["w"] and int(r["Q"]) == tw["Q"]
            sum8 += L.log()
            tot2_8 += local(tw["2"], x2)
            for p in (3, 5):
                tot35_8[p] += local(tw[str(p)], xp[p])
    # [E_W':Q] = 512 * 2^dim; log zeta_{E_W'} = log zeta_E + 2 sum log L (degree 4) + 4 sum log L8
    deg = 512 * 2**dim
    Y_W = Y_E / 2**dim + 2 * sum4 / deg + 4 * sum8 / deg
    E2 = 2 * g(4, s) / 16                      # the two dyadic primes, type (4,2) in E/B
    W2 = E2 / 2**dim + 2 * tot2_4 / deg + 4 * tot2_8 / deg
    K2 = 2 * g(16, s) / 64                     # their K-terms, type (8,4)
    assert W2 >= K2
    sel = W2 - K2
    # above 3 and 5 the types in E, E_W' and K coincide: the E_W'-terms from the 352 local factors equal the E-terms
    for p in (3, 5):
        Ep = 2 * g(p**2, s) / 8
        Wp = Ep / 2**dim + 2 * tot35_4[p] / deg + 4 * tot35_8[p] / deg
        assert abs(Wp - Ep) < arb(10) ** -40, (p, Wp, Ep)

    def fW(code):                               # residue degree in E_W'/B of an unramified prime of nonzero vector
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
    delta = arb(delta_q.numerator) / delta_q.denominator
    small = arb(0)
    small_census = arb(0)
    small_adaptive = arb(0)
    qmin = None
    cnt = {"v0_Frobenius_off_kerW3": 0, "v0_census": 0, "v0_undetected": 0, "adaptive_terms": 0}
    inert = json.loads((HERE / SPACE["inert"]).read_text())
    for N, c, rr in A.places(XA, with_root=True):
        f0 = A.f0_of(N, c)
        extra = arb(0)
        if c == 0:
            if rr is not None:
                b = RC.bits(N, rr)
                pat = sum(1 << i for i, x in enumerate(b) if x == -1)
                if any(bin(pat & m).count("1") % 2 for m in mW):
                    f0 = 2
                    cnt["v0_Frobenius_off_kerW3"] += 1
                elif pat:
                    f0 = 2
                    extra = T(N, s)
                    cnt["v0_census"] += 1
                else:
                    cnt["v0_undetected"] += 1
            else:
                bits = inert[str(int(round(N ** 0.5)))]
                if any(bits[k] for k in SPACE["masks"]):
                    f0 = 2
                    cnt["v0_Frobenius_off_kerW3"] += 1
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
        XLO, XHI, NB, counts = read_bins3(pre)
        assert XLO == edge
        edge = XHI
        lh = (1 + arb(1) / 65536).log()
        tot = arb(0)
        for j in np.nonzero(counts)[0]:
            U = arb(XLO) * ((int(j) + 2) * lh).exp()
            tot += int(counts[j]) * arb(T(U, s).lower())
        big += tot
        binfo.append({"XLO": XLO, "XHI": XHI, SPACE["bins"]: int(counts.sum()), "sum_T_lower": str(tot.lower())})
    gain = small + big
    out = {"space": [k for k, v in SPACES.items() if v is SPACE][0], "sigma": str(SIGMA), "orbits": ORBITS, "families8": FAMILIES,
           "Y_E": str(Y_E), "Y_W3": str(Y_W),
           "dyadic_E_W3_term": str(W2), "Delta_sel": str(sel), "Delta_P4": str(sav), "R": str(R),
           "C_W3_upper": str(C_W.upper()), "small_gain_lower": str(small.lower()), "census_gain_lower": str(big.lower()),
           "counts": cnt, "bins": binfo, "XC": edge, "C_eff_upper": str((C_W - gain).upper())}
    print(json.dumps(out, indent=1))
    main.components = {"Y_W": Y_W, "sel": sel, "sav": sav, "R": R, "Bhalf": Bhalf, "eps": eps,
                       "census_small": small_census, "adaptive_small": small_adaptive, "census_bins": big,
                       "qmin_rest_upto_XA": qmin, "XA": XA}
    return C_W, gain


if __name__ == "__main__":
    args = sys.argv[1:]
    if args[0] in SPACES:
        SPACE = SPACES[args.pop(0)]
    main(Q(args[0]), Q(args[1]), args[2], args[3], args[4], args[5:])
