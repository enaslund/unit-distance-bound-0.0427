#!/usr/bin/env python3
"""Proposition E (README Section 11): the refined TV step with a signed kernel over several abscissae.

For abscissae 1 < sigma_1 < ... < sigma_m < 101/100, rationals c_1..c_m of any sign and b >= 0 such that
lambda = sum_j c_j g_{sigma_j} satisfies, for every real q >= q_min = 41^4 (the least floor norm of a
non-selected prime),
  (i)  lambda(q) >= g_1(q) - b w(q),      (ii)  lambda(q) >= 0,      (iii)  lambda is non-increasing,
one has  Z(1) <= Z_sel(1) + sum_j c_j F(sigma_j) + b (2 kappa_oo - T_sel),  where F(sigma) = Y_*(sigma) - Z_sel(sigma)
is the floor sum of the non-selected primes (census floors included).  F(sigma_j) is enclosed on both sides: the
L-values come from the long AFE (hp/: dafe.py with M = 999999, ye_hp.py), and the census bins enter through
tau(N) = sum_j c_j T_{sigma_j}(N), evaluated on the range of each group of bins.  Adaptive credits are not used.

(i)-(iii) are checked for x = log q in [log q_min, X_big] on cells: with S one of e^x(lambda - g_1 + b w),
e^x lambda, e^x lambda', the Taylor coefficients S_0, S_1, S_2 at the cell midpoint and an enclosure of S'''/6 over
the cell (power series over a ball) bound S on the cell; a cell that fails is bisected.  For x >= X_big the term of
the smallest abscissa (whose coefficient must be positive) dominates the others explicitly.

Usage:
  signed.py choose DELTA PREFIX [PREFIX ...]          float LP over hp/sigma_set.txt -> hp/signed_params.json
  signed.py certify DELTA PARAMS PREFIX [PREFIX ...]  rigorous checks and the certified constant
"""
import contextlib
import gzip
import io
import json
import math
import re
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
with contextlib.redirect_stdout(io.StringIO()):
    import dihedral_ceiling as DCm
from flint import arb, arb_series, ctx  # noqa: E402

ctx.prec = 200
HP = HERE / "hp"
SEL = [(16, Q(1, 32)), (9, Q(1, 4)), (25, Q(1, 4)), (29**4, Q(1, 4)), (41**4, Q(1, 8))]
QMIN = 41**4
LH = math.log1p(1 / 65536)


def A(x):
    x = Q(x)
    return arb(x.numerator) / x.denominator


def g(q, s):
    return -(1 - arb(q) ** (-s)).log()


def zsel(s):
    return sum((A(be) * g(q, s) for q, be in SEL), arb(0))


def w_arb(q):
    L = arb(q).log()
    tot = arb(0)
    m = 1
    while True:
        term = 1 / (arb(q) ** m + 1)
        tot += term
        if term < arb(10) ** -70:
            break
        m += 1
    return 2 * L * (tot + arb(0, 1) * (2 * term.upper()))   # tail < 2 * last term, kept in Arb


def kappa():
    ell = arb(9) / 4 * arb(2).log() + (arb(3).log() + arb(5).log() + arb(241).log()) / 2
    return (ell - arb.const_euler() - (4 * arb.pi()).log()) / 4


def B_r():
    return 2 * kappa() - sum((A(be) * w_arb(q) for q, be in SEL), arb(0))


def sig_files(sig):
    return HP / f"afe241hp_{sig.numerator}_{sig.denominator}.json"


def exact_part(delta, sig):
    """E(sigma) = Y_W - sel - sav - census_small - Z_sel(sigma): F(sigma) without the census bins."""
    with contextlib.redirect_stdout(io.StringIO()):
        DCm.main(delta, sig, str(sig_files(sig)), [], lv_dir=str(HP))
    c = DCm.main.components
    assert c["qmin_rest_upto_XA"] >= QMIN, c["qmin_rest_upto_XA"]       # no non-selected floor norm below 41^4
    s = A(sig)
    return c["Y_W"] - c["sel"] - c["sav"] - c["census_small"] - zsel(s)


def _exact_job(args):
    d, s = args
    E = exact_part(Q(d), Q(s))
    m, e = E.mid().man_exp()
    rm, re_ = E.rad().man_exp()
    return s, (int(m), int(e)), (int(rm), int(re_))


def exact_parts(delta, sigs, jobs=6):
    """exact_part for several abscissae in parallel processes; the balls are passed exactly (mantissa, exponent)"""
    import multiprocessing as mp_
    with mp_.get_context("fork").Pool(min(jobs, len(sigs))) as pool:
        res = pool.map(_exact_job, [(str(delta), str(s)) for s in sigs])
    out = {}
    for s, (m, e), (rm, re_) in res:
        out[s] = arb(m) * arb(2) ** e + arb(0, arb(rm) * arb(2) ** re_)
    return [out[str(s)] for s in sigs]


def read_bins(pre):
    tp = HERE / (pre + ".txt")
    txt = tp.read_text() if tp.exists() else gzip.open(str(tp) + ".gz", "rt").read()
    summ = txt.splitlines()[-1]
    m = re.search(r"XLO (\d+) XHI (\d+) H 2\^-16 NB (\d+)", summ)
    XLO, XHI, NB = int(m.group(1)), int(m.group(2)), int(m.group(3))
    raw = HERE / (pre + ".binsBW")
    if raw.exists():
        counts = np.fromfile(str(raw), dtype=np.uint64)
    else:
        counts = np.frombuffer(gzip.open(str(raw) + ".gz", "rb").read(), dtype=np.uint64)
    assert len(counts) == NB
    return XLO, XHI, NB, counts


def census_float(sig, prefixes):
    s = float(sig)
    tot = 0.0
    for pre in prefixes:
        XLO, XHI, NB, counts = read_bins(pre)
        js = np.nonzero(counts)[0]
        N = XLO * np.exp((js + 0.5) * LH)
        x = N ** (-s)
        tot += float(np.sum(counts[js].astype(float) * (-np.log1p(-x) / 2 + np.log1p(-x * x) / 4)))
    return tot


def census_tau(cs, sigs, prefixes, group=8):
    """Enclosure of sum over detected ker-W sides of tau(N) = sum_j c_j T_{sigma_j}(N), T = g(N)/2 - g(N^2)/4.  A side
    counted in bin j has N in [XLO (1+H)^(j-1), XLO (1+H)^(j+2)] (one bin of floating-point slack either way).  On a
    group of bins with N in [lo, hi] = mid + [-r, r], tau(N) lies in tau(mid) + tau'([lo, hi]) [-r, r] (mean value
    theorem), which keeps the dependency between the terms of tau out of the main part."""
    cA = [A(c) for c in cs]
    sA = [A(s) for s in sigs]
    lh = (1 + arb(1) / 65536).log()

    def tau(N):
        return sum((c * (g(N, s) / 2 - g(N * N, s) / 4) for c, s in zip(cA, sA)), arb(0))

    def dtau(N):                                  # d/dN of g(N, s)/2 - g(N^2, s)/4
        tot = arb(0)
        for c, s in zip(cA, sA):
            u = N ** (-s)
            tot += c * (-(s / 2) * u / (N * (1 - u)) + (s / 2) * u * u / (N * (1 - u * u)))
        return tot

    tot = arb(0)
    edge = None
    for pre in prefixes:
        XLO, XHI, NB, counts = read_bins(pre)
        assert XLO == (12 * 10**6 if edge is None else edge), (pre, XLO, edge)  # the prefixes tile (XA, XC], XA = 1.2e7
        edge = XHI
        nz = np.nonzero(counts)[0]
        i = 0
        while i < len(nz):
            j0 = int(nz[i])
            k = i
            while k + 1 < len(nz) and int(nz[k + 1]) < j0 + group:
                k += 1
            j1 = int(nz[k])
            cnt = int(counts[nz[i:k + 1]].sum())
            lo = (arb(XLO) * ((j0 - 1) * lh).exp()).lower()
            hi = (arb(XLO) * ((j1 + 2) * lh).exp()).upper()
            mid = (lo + hi) / 2
            r = (hi - lo) / 2
            hull = arb(lo).union(arb(hi))
            tot += cnt * (tau(mid) + dtau(hull) * arb(0, r.upper()))
            i = k + 1
    return tot


# ---------------------------------------------------------------- kernel conditions in x = log q
KTR = 10            # terms kept of -log(1 - y)/y = sum y^(k-1)/k and of 1/(1 - y); y = e^(-sigma x) <= 4e-7 here


def series_S(x0, cs, sigs, b, order=4):
    """power series in t of S_1, S_2, S_3 at x0 + t (x0 a number or a ball):
    S_1 = e^x (lambda - g_1 + b w), S_2 = e^x lambda, S_3 = e^x lambda', in the stable forms
    e^x g_s(e^x) = e^(-(s-1)x) sum_{k>=1} y^(k-1)/k,  e^x lambda' = -sum c s e^(-(s-1)x) sum_{k>=0} y^k  (y = e^(-s x)),
    e^x w(e^x) = 2x sum_{m>=1} e^(-(m-1)x)/(1 + e^(-m x)).  The series in y are cut after KTR terms; the remainder
    and its first three derivatives are below 1e-55 for x >= 14 (y <= 4e-7), which is added as a radius to every
    coefficient.  In w only positive terms are dropped (m > 6), which lowers S_1."""
    old = ctx.cap
    ctx.cap = order
    try:
        x = arb_series([x0, 1])
        tiny = arb(0, arb(10) ** -55)
        lam = arb_series([0])
        lamp = arb_series([0])
        for c, s in zip(cs, sigs):
            y = (-(s * x)).exp()
            E = (-((s - 1) * x)).exp()
            p = arb_series([0])
            q = arb_series([0])
            yk = arb_series([1])
            for k in range(1, KTR + 1):
                p += yk / k
                q += yk
                yk = yk * y
            lam += c * E * p
            lamp += -c * s * E * q
        y0 = (-x).exp()
        g1 = arb_series([0])
        yk = arb_series([1])
        for k in range(1, KTR + 1):
            g1 += yk / k
            yk = yk * y0
        W = arb_series([0])
        for m in range(1, 7):
            W += (-((m - 1) * x)).exp() / (1 + (-(m * x)).exp())
        W = 2 * x * W
        out = []
        for S in (lam - g1 + b * W, lam, lamp):
            co = S.coeffs()
            out.append(arb_series([v + tiny for v in co]))
        return out
    finally:
        ctx.cap = old


def cell_bounds(a, h, cs, sigs, b):
    """lower bounds of S1, S2 and upper bound of S3 on [a, a + h]"""
    m = a + h / 2
    r = h / 2
    P = series_S(m, cs, sigs, b)
    Bl = series_S(arb(m, r), cs, sigs, b)
    out = []
    for k, (sp, sb) in enumerate(zip(P, Bl)):
        c = sp.coeffs() + [arb(0)] * 4
        cb = sb.coeffs() + [arb(0)] * 4
        spread = abs(c[1]) * r + abs(c[2]) * r * r + abs(cb[3]) * r ** 3
        out.append(c[0] - spread if k < 2 else c[0] + spread)
    return out


def check_kernel(cs, sigs, b, xmin, xbig, h0=arb(1) / 20, depth=14):
    """(i)-(iii) on [xmin, xbig]; returns (ok, cells, worst slacks)"""
    cells = 0
    worst = [None, None, None]
    x = xmin
    while x < xbig:
        h = h0 if x < 60 else arb(x) / 100
        h = min(h, xbig - x) if xbig - x > 0 else h
        stack = [(x, h, 0)]
        while stack:
            a, hh, d = stack.pop()
            lo1, lo2, up3 = cell_bounds(a, hh, cs, sigs, b)
            cells += 1
            if lo1 > 0 and lo2 > 0 and up3 < 0:
                for i, v in enumerate((lo1.lower(), lo2.lower(), -up3.upper())):
                    if worst[i] is None or v < worst[i]:
                        worst[i] = v
                continue
            if d >= depth:
                return False, float(a.mid()), [str(lo1), str(lo2), str(up3)]
            stack.append((a + hh / 2, hh / 2, d + 1))
            stack.append((a, hh / 2, d + 1))
        x = x + h
    return True, cells, worst


def check_tail(cs, sigs, b, xbig):
    """x >= xbig: the term of the smallest abscissa dominates; also g_1 - b w < 0 there."""
    order = sorted(range(len(sigs)), key=lambda j: sigs[j])
    j1 = order[0]
    c1, s1 = cs[j1], sigs[j1]
    assert c1 > 0
    X = arb(xbig)
    rest = sum((abs(cs[j]) * (1 + (-X).exp()) * (-(sigs[j] - s1) * X).exp() for j in order[1:]), arb(0))
    restp = sum((abs(cs[j]) * sigs[j] * (1 + 2 * (-X).exp()) * (-(sigs[j] - s1) * X).exp() for j in order[1:]), arb(0))
    ok2 = c1 - rest > 0
    ok3 = c1 * s1 - restp > 0
    ok1 = 2 * b * X > 1 + 3 * (-X).exp()
    return bool(ok1 and ok2 and ok3)


# ---------------------------------------------------------------- choose (float LP)
def qg(x, s):
    out = np.empty_like(x)
    m = x < 40
    q = np.exp(x[m])
    out[m] = -np.log1p(-q ** (-s)) * q
    out[~m] = np.exp(-(s - 1) * x[~m]) * (1 + 0.5 * np.exp(-s * x[~m]))
    return out


def qw(x):
    out = np.empty_like(x)
    m = x < 40
    xx = x[m]
    tot = np.zeros_like(xx)
    for k in range(1, 60):
        tot += np.exp(-k * xx) / (1 + np.exp(-k * xx))
    out[m] = 2 * xx * tot * np.exp(xx)
    out[~m] = 2 * x[~m]
    return out


def lp(F, R, sigs, Br, margin=1e-6, xbig=2e6, xA=4000.0):
    """float LP: minimise sum c_j F_j (+ radius) + b B_r subject to (i) for x <= xA, (ii), (iii) on a grid, with
    margins proportional to rho(x) = e^{-(sigma_1 - 1) x} (the slowest term), and c_1 >= 0."""
    from scipy.optimize import linprog
    xmin = math.log(QMIN)
    xs = np.concatenate([np.linspace(xmin, 60, 2400), np.geomspace(60, xbig, 9000)])
    rho = np.exp(-(float(sigs[0]) - 1) * xs)
    G = np.array([qg(xs, float(s)) for s in sigs]).T
    g1 = qg(xs, 1.0)
    W = qw(xs)
    k = len(sigs)
    mA = xs <= xA
    dec = np.exp(-(xs[1:] - xs[:-1]))[:, None]
    D = G[1:] * dec - G[:-1]
    ri = (1 / rho)[:, None]                   # rows divided by rho: margins and solver tolerances become relative
    Am = np.vstack([np.hstack([-G[mA], G[mA], -W[mA][:, None]]) * ri[mA],
                    np.hstack([-G, G, np.zeros((len(xs), 1))]) * ri,
                    np.hstack([D, -D, np.zeros((len(xs) - 1, 1))]) * ri[:-1]])
    ub = np.concatenate([(-g1[mA]) / rho[mA] - margin, -margin * np.ones(len(xs)),
                         -margin * 1e-3 * np.minimum(1.0, xs[1:] - xs[:-1])])
    cost = np.concatenate([np.array(F) + np.array(R), -(np.array(F) - np.array(R)), [Br]])
    # column scaling (the abscissae give nearly dependent columns)
    cs_ = np.maximum(np.abs(Am).max(axis=0), 1e-300)
    Am = Am / cs_
    cost = cost / cs_
    bounds = [(0, None)] * (2 * k + 1)
    bounds[k] = (0, 0)
    best = None
    for method in ("highs-ds", "highs-ipm"):
        r = linprog(cost, A_ub=Am, b_ub=ub, bounds=bounds, method=method,
                    options={"primal_feasibility_tolerance": 1e-10, "dual_feasibility_tolerance": 1e-10})
        if r.status == 0 and (best is None or r.fun < best.fun):
            best = r
    if best is None:
        return None
    x = best.x / cs_
    return float(np.dot(x, np.concatenate([np.array(F) + np.array(R), -(np.array(F) - np.array(R)), [Br]]))), \
        x[:k] - x[k:2 * k], x[-1]


def choose(delta, prefixes, ns=None, margin=1e-6, xbig=2e6):
    if ns is None:
        ns = [int(v) for v in (HP / "sigma_set.txt").read_text().split()]
    sigs = [Q(n + 1, n) for n in sorted(ns, reverse=True)]           # smallest sigma first
    F, R = [], []
    for s, E in zip(sigs, exact_parts(delta, sigs)):
        F.append(float(E.mid()) - census_float(s, prefixes))
        R.append(float(E.rad()) + 1e-12)
    Br = float(B_r().mid())
    res = lp(F, R, sigs, Br, margin, xbig)
    assert res is not None, "LP failed"
    fun, c, b = res
    zs = float(zsel(arb(1)).mid())
    print(f"choose: {len(sigs)} abscissae, LP value (rest + TV) {fun:.7e}, C ~ {zs + fun:.8f}, b = {b:.6e}, "
          f"sum|c| = {np.abs(c).sum():.2f}")
    params = {"sigmas": [str(s) for s in sigs],
              "c": [str(Q(float(v)).limit_denominator(10**14)) for v in c],
              "b": str(Q(float(b) * (1 + 1e-9) + 1e-12).limit_denominator(10**14)),
              "xbig": str(int(xbig)), "lp_value": fun}
    (HP / "signed_params.json").write_text(json.dumps(params, indent=1))
    return params


# ---------------------------------------------------------------- certify
def certify(delta, params, prefixes):
    t0 = time.time()
    # abscissae whose coefficient is 0 do not enter lambda: drop them (the tail check needs the smallest one with c > 0)
    keep = [(Q(s), Q(c)) for s, c in zip(params["sigmas"], params["c"]) if Q(c) != 0]
    params = {**params, "sigmas": [str(s) for s, _ in keep], "c": [str(c) for _, c in keep]}
    sigs = [s for s, _ in keep]
    cs = [c for _, c in keep]
    b = Q(params["b"])
    xbig = int(params["xbig"])
    assert all(Q(1) < s < Q(101, 100) for s in sigs) and len(set(sigs)) == len(sigs) and b >= 0
    assert len(cs) == len(sigs)
    assert sum(abs(c) for c in cs) <= 10**6                 # keeps the 1e-55 remainder radius of series_S valid
    sA, cA, bA = [A(s) for s in sigs], [A(c) for c in cs], A(b)
    xmin = A(Q(int(float(arb(QMIN).log().lower()) * 10**6), 10**6))                  # <= log q_min
    assert xmin > 14 and xmin <= arb(QMIN).log()
    ok, cells, worst = check_kernel(cA, sA, bA, xmin, arb(xbig))
    assert ok, ("kernel conditions fail", cells, worst)
    assert check_tail(cA, sA, bA, xbig), "tail domination fails"
    total = arb(0)
    for c, E in zip(cA, exact_parts(delta, sigs)):
        total += c * E
    S = census_tau([Q(c) for c in params["c"]], sigs, prefixes)
    combo = total - S
    Br = B_r()
    C = zsel(arb(1)) + combo + bA * Br
    out = {"sigmas": params["sigmas"], "b": params["b"], "kernel_cells": cells,
           "kernel_min_slacks": [str(v) for v in worst], "xbig": xbig,
           "sum_abs_c": str(sum(abs(c) for c in cs)), "sum_c_E": str(total), "census_tau": str(S),
           "rest_plus_TV_upper": str((combo + bA * Br).upper()), "Z_sel(1)": str(zsel(arb(1))),
           "C_eff_upper": str(C.upper()), "seconds": round(time.time() - t0)}
    print(json.dumps(out, indent=1))
    return C


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "choose":
        choose(Q(sys.argv[2]), sys.argv[3:])
    elif mode == "certify":
        certify(Q(sys.argv[2]), json.loads(Path(sys.argv[3]).read_text()), sys.argv[4:])
    else:
        raise SystemExit(__doc__)
