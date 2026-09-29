#!/usr/bin/env python3
"""Interval-arithmetic geometric margin for the tower over B = Q(sqrt 241).

Reuses the manuscript's certified profile routines (mass, overlap, Fourier tube)
and finite shell windows.  Inputs: delta, analytic ceiling C, shell profile file.
"""
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
import env241  # noqa: E402
from mpmath import mp, iv  # noqa: E402
from interval_core import I, qi, lower, upper  # noqa: E402
from profile_certificate import mass_certificate, overlap_certificate, tube_certificate, interval_strings  # noqa: E402
from finite_windows import local_window  # noqa: E402

EF = {2: (8, 4), 3: (2, 2), 5: (2, 2), 29: (1, 4), 7: (1, 8)}
THETA = Q(65535, 131072)         # b/d = 1/(2|cl(c1)|) <= 2^-16, theta = (1-b/d)/2 >= 1/2 - 2^-17
PAPER_W = json.loads(env241.PAPER_WITNESS.read_text())


def margin(delta, C, shells, s=None, a=None, bern=None, verbose=True):
    delta = Q(delta)
    C = Q(C)
    p = 2 / (1 + delta)
    s = Q(s if s is not None else PAPER_W["s"])
    a = Q(a if a is not None else PAPER_W["a"])
    Bm = bern if bern is not None else [[Q(v) for v in row] for row in PAPER_W["bernstein"]]
    q = s * p - 1
    assert q > 0
    ell = qi(Q(9, 4)) * iv.log(2) + (iv.log(3) + iv.log(5) + iv.log(241)) / 2
    H = I(0)
    finite = I(0)
    for key, k in shells["ks"].items():
        prime = int(key)
        e, f = EF[prime]
        H += k * iv.log(prime) / e
        val, gain, rec = local_window(prime**f, int(k), shells["finite_profiles"][key], delta)
        finite += val / (e * f)
    mass, _ = mass_certificate(Bm, s, p, PAPER_W["mass_grid"], PAPER_W["mass_terms"])
    overlap, _ = overlap_certificate(Bm, s, a, PAPER_W["overlap_order"])
    jd = (iv.log(overlap) + 2 * qi(1 + delta) * iv.log(qi(q)) - 2 * qi(delta) * iv.log(iv.pi)
          + 2 * qi(delta) * iv.log(qi(a)) - qi(1 + delta) * iv.log(mass))
    ac = 2 * p * delta
    jc = iv.log(qi(p) / 2) + qi(delta) * (iv.log(qi(ac) / iv.pi) - 1)
    slope = -iv.log(iv.pi) - 2 * jc + jd
    logK, sigma_D, _ = tube_certificate(Bm, s, p, a, Q(PAPER_W["tube_width"]))
    mu = 2 * iv.exp(H / 2 - ell)
    fourier_ok = (0 < ac <= 1 and lower(sigma_D) > 1 and upper(logK) < lower(2 * iv.log(2))
                  and lower(mu) > 10)
    th = THETA
    Mstar = (finite - (I('.5') - qi(delta)) * ell - qi(C) + qi(1 - delta) * iv.log(2)
             + (1 - qi(th)) * iv.log(iv.pi) + (1 - 2 * qi(th)) * jc + qi(th) * jd)
    after = Mstar - 4 * qi(Q(1, 10**9))
    if verbose:
        print("delta", delta, "C", C, " J_D", interval_strings(jd)[0][:14], " slope>0", lower(slope) > 0,
              " fourier_ok", fourier_ok, " mu", float(lower(mu)), " margin_after", interval_strings(after)[0][:16])
    return after, fourier_ok, lower(slope) > 0


if __name__ == "__main__":
    mp.dps = 80
    iv.dps = 80
    delta = sys.argv[1]
    C = sys.argv[2]
    shells = json.loads(Path(sys.argv[3]).read_text())
    after, fourier_ok, slope_ok = margin(delta, C, shells)
    assert fourier_ok, "Fourier/period condition fails"
    assert slope_ok, "theta-slope of the margin is not positive (theta_min bound not usable)"
    print("certified lower margin after concentration:", "POSITIVE" if lower(after) > 0 else "NOT POSITIVE")
