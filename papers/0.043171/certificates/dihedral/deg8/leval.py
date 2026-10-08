#!/usr/bin/env python3
"""Certified L-values from the per-cell moments of octcoef.c (degree 8) or dcoef4.c (degree 4).

For each twist and abscissa s:  L(s) = t^s / prod Gamma(s/d + a_j) * [ sum_i sum_j q_ij(s) M_ij  +/- (sum_i A_i R_i + tail) ]
(gkernel.py).  Each moment is a ball around the double M_ij of radius

    W_ij [(j + 2 nth + 12) u + 10 cnt_i u^2] + A_i j (w_i + du)^(j-1) du,     W_ij = A_i (w_i + du)^j,

u = 2^-53, w_i = 1 - c_{i+1}/c_i: |u_n| <= w_i exactly (cells by exact thresholds).  The computed u_n is within
du = (d eps_t + 2 d u)(1 + 1e-9) of it, where t_d is the double used by the C program (from the metadata) and
eps_t >= |t_d/t - 1| is computed here in Arb: x = fl(t_d n) (and fl(x^2) for d = 2), fl(x/c_i) and the exact
subtraction of 1 (Sterbenz) cost d u + [d = 2] u + u; n and c_i are exact doubles.  The powers and the product
with a_n cost j u relative; Kahan summation (Higham, Thm 4.8) at most (2u + O(n u^2)) of the sum of absolute values;
the merge of the nth thread accumulators and the final subtraction 2 (nth + 2) u.

Rankin tail (degree 8): log E(beta) <= sum_{p <= PSMALL} log sum_k |a_{p^k}| p^(-k beta)  (PARI Euler factors; the
coefficients beyond k = 60 bounded by binom(k+7, 7)) + sum_{PSMALL < q <= N_max} |a_q| q^-beta (octcoef.c, with a
relative margin) + 8 sum_{exceptional q} q^-beta + 36.01 / PSMALL (the squares and higher powers of q > PSMALL,
binom(k+7, 7) q^(-k beta) summed) + 8 * 1.25506 beta N_max^(1 - beta) / ((beta - 1) log N_max) (q > N_max, pi(x) <=
1.25506 x / log x).  Degree 4: |a_n| <= d_4(n), zeta(beta)^4.

Usage: leval.py MOMENTS META SIGMA_FILE OUTDIR LABEL [--export EXPORT_JSON]    (degree 8 needs --export)
  SIGMA_FILE: one fraction p/q per line.  Writes OUTDIR/<LABEL>_<p>_<q>.json (rows as dafe.py) per abscissa.
"""
import json
import math
import struct
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gkernel as GK  # noqa: E402
from flint import arb, ctx  # noqa: E402

U = 2.0 ** -53
BETAS8 = (Q(21, 20), Q(11, 10), Q(6, 5), Q(3, 2))


def read_moments(path):
    raw = Path(path).read_bytes()
    ntw, D, ncell, nth = struct.unpack("4i", raw[:16])
    off = 16
    tw = []
    for w in range(ntw):
        cells = []
        for i in range(ncell):
            cnt, A = struct.unpack("QQ", raw[off:off + 16])
            off += 16
            M = struct.unpack(f"{D + 1}d", raw[off:off + 8 * (D + 1)])
            off += 8 * (D + 1)
            cells.append((cnt, A, M))
        rk = struct.unpack("4d", raw[off:off + 32])
        off += 32
        tw.append({"cells": cells, "rk": rk})
    tots = struct.unpack("4Q", raw[off:off + 32])
    off += 32
    (ne,) = struct.unpack("i", raw[off:off + 4])
    off += 4
    exc = list(struct.unpack(f"{ne}Q", raw[off:off + 8 * ne]))
    off += 8 * ne
    eul = None
    if off < len(raw):                       # octcoef.c: the Euler-product test sums at s = 19/10
        eul = list(struct.unpack(f"{ntw}d", raw[off:off + 8 * ntw]))
        off += 8 * ntw
    assert off == len(raw)
    return {"ntw": ntw, "D": D, "ncell": ncell, "nth": nth, "tw": tw, "tots": tots, "exc": exc, "eul": eul}


def eps_t(t_double, kappa, conductor):
    """upper bound for |t_d / t - 1|, t = kappa / sqrt(Q)"""
    old = ctx.prec
    ctx.prec = 256
    try:
        t = kappa() / arb(conductor).sqrt()
        return float((abs(arb(t_double) / t - 1)).upper()) * (1 + 1e-6) + 1e-300
    finally:
        ctx.prec = old


def moment_balls(cells, pts, D, nth, du):
    balls, absums = [], []
    for i, (cnt, A, M) in enumerate(cells):
        w = float(1 - pts[i + 1] / pts[i]) * (1 + 1e-12)
        row = []
        for j in range(D + 1):
            Wj = A * (w + du) ** j
            rad = Wj * ((j + 2 * nth + 12) * U + 10 * cnt * U * U)
            if j > 0:
                rad += A * j * (w + du) ** (j - 1) * du
            row.append(arb(M[j]) + arb(0, rad * (1 + 1e-9)))
        balls.append(row)
        absums.append(A)
    return balls, absums


def logE_octic(tw_export, PSMALL, NMAX, rk, exc):
    """beta -> arb upper bound for log E(beta), for one twist"""
    primes = sorted(int(p) for p in tw_export["small"] if int(p) <= PSMALL)
    out = {}
    for bi, beta in enumerate(BETAS8):
        assert abs(float(beta) - (1.05, 1.1, 1.2, 1.5)[bi]) < 1e-12
        bA = arb(beta.numerator) / beta.denominator
        tot = arb(0)
        K0 = 60
        for p in primes:
            P = tw_export["small"][str(p)]
            c = [1] + [0] * K0
            for k in range(1, K0 + 1):
                c[k] = -sum(P[j] * c[k - j] for j in range(1, min(k, len(P) - 1) + 1))
            x = arb(p) ** (-bA)
            s = sum((abs(c[k]) * x ** k for k in range(K0 + 1)), arb(0))
            # k > K0: |a_{p^k}| <= binom(k+7, 7), ratio <= 2 x for k > K0
            s += arb(math.comb(K0 + 8, 7)) * x ** (K0 + 1) / (1 - 2 * x)
            tot += s.log()
        tot += arb(rk[bi]) * (1 + arb(1) / 10**6)          # naive double summation of <= 10^9 terms: rel. error < 2e-7
        for q in exc:
            tot += 8 * arb(q) ** (-bA)
        tot += arb(3601) / 100 / PSMALL
        tot += 8 * arb("1.25506") * bA * arb(NMAX) ** (1 - bA) / ((bA - 1) * arb(NMAX).log())
        out[beta] = arb(tot.upper())
    return lambda b: out[b]


def main(momf, metaf, sigf, outdir, label, export=None):
    ctx.prec = 256
    mom = read_moments(momf)
    meta = json.loads(Path(metaf).read_text())
    sigmas = [Q(line.strip()) for line in Path(sigf).read_text().splitlines() if line.strip()]
    outdir = Path(outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    deg8 = export is not None
    if deg8:
        ex = json.loads(Path(export).read_text())
        types = ["octic"] * mom["ntw"]
        Ns = [meta["groups"][t["group"]]["N"] for t in meta["twists"]]
        Qs = [t["Q"] for t in meta["twists"]]
        ws = [t["w"] for t in meta["twists"]]
        logEs = [logE_octic(ex["twists"][k], meta["PSMALL"], meta["NMAX"], mom["tw"][k]["rk"], mom["exc"]) for k in range(mom["ntw"])]
        if mom["exc"]:
            raise SystemExit(f"leval: {len(mom['exc'])} exceptional primes: their terms must be added (not implemented)")
    else:
        types = [t["type"] for t in meta["twists"]]
        Ns = [t["N"] for t in meta["twists"]]
        Qs = [t["Q"] for t in meta["twists"]]
        ws = [t["w"] for t in meta["twists"]]
        logEs = [None] * mom["ntw"]
    tables = {ty: GK.HTable(ty) for ty in sorted(set(types))}
    pts = {ty: tables[ty].pts for ty in tables}
    if deg8:
        tds = [meta["groups"][t["group"]]["t"] for t in meta["twists"]]
    else:
        tds = [t["t"] for t in meta["twists"]]
    dus = []
    for k in range(mom["ntw"]):
        T = GK.TYPES[types[k]]
        et = eps_t(tds[k], T["kappa"], Qs[k])
        assert et < 64 * U, et
        dus.append((T["d"] * et + 2 * T["d"] * U) * (1 + 1e-9))
    balls = [moment_balls(mom["tw"][k]["cells"], pts[types[k]], mom["D"], mom["nth"], dus[k]) for k in range(mom["ntw"])]
    for s in sigmas:
        t0 = time.time()
        kern = {ty: GK.Kernel(tables[ty], s) for ty in tables}
        rows = []
        for k in range(mom["ntw"]):
            Mb, absums = balls[k]
            L = GK.evaluate_moments(kern[types[k]], Qs[k], Mb, absums, Ns[k], logEs[k], BETAS8 if deg8 else None)
            assert L > 0, (k, L)
            rows.append({"k": meta["twists"][k].get("k", k), "w": ws[k], "sigma": str(s), "type": types[k], "Q": Qs[k], "N": Ns[k],
                         "L": [str(L.lower()), str(L.upper())], "rel_rad": float(L.rad() / L.mid())})
        f = outdir / f"{label}_{s.numerator}_{s.denominator}.json"
        f.write_text(json.dumps(rows, indent=1) + "\n")
        print(f"leval: {label} sigma {s}: {len(rows)} L-values, max rel radius {max(r['rel_rad'] for r in rows):.3e}, "
              f"{time.time() - t0:.0f} s", flush=True)


if __name__ == "__main__":
    args = sys.argv[1:]
    exp = None
    if "--export" in args:
        i = args.index("--export")
        exp = args[i + 1]
        args = args[:i] + args[i + 2:]
    main(*args, export=exp)
