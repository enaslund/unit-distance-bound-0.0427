#!/usr/bin/env python3
"""Refined Tsfasman-Vladut step (README Section 11): a certified bound for Z(1) from the bound at sigma and
the TV inequality, with the selected primes treated exactly.

With beta_q = beta_sel_q + beta_rest_q (the selected primes have known types in every K), for a >= 1, b >= 0 with

    g_1(q) <= a g_sigma(q) + b w(q)        for every q >= q_min                            (*)

(q_min = least norm a K-prime above a non-selected prime can have), one gets

    Z(1) <= Z_sel(1) + a (Y_*(sigma) - Z_sel(sigma)) + b (2 kappa_oo - sum_sel beta_q w(q)),

which replaces Y_*(sigma) + epsilon (kappa_oo + D).  (*) is checked rigorously for every q >= 2 (so q_min carries no weight): on [2, 2 q_min] by geometric cells
and monotonicity (kernel_small_ok), and for q >= q_min through the sufficient condition
h(x) = a e^{-eps x} + 2 b x (1 - e^{-x}) - (1 + 2 e^{-x}) >= 0 for x >= log q_min, since g_1(q) <= 1/(q-1),
g_sigma(q) >= q^-sigma, w(q) >= 2 log q/(q+1), q/(q+1) >= 1 - 1/q and q/(q-1) <= 1 + 2/q for q >= 2
(beyond X1 = 1/b + 1 the difference 2 b x (1 - e^{-x}) - 1 - 2 e^{-x} is positive and increasing).
Usage: lptv.py DELTA SIGMA YE_JSON A B PREFIX [PREFIX ...]      (A, B rationals)
"""
import contextlib
import io
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
with contextlib.redirect_stdout(io.StringIO()):
    import dihedral_ceiling as DCm
from flint import arb, ctx  # noqa: E402

ctx.prec = 200
# selected primes: (norm q of the K-primes, beta_q) -- types (8,4) at the two dyadic primes, (2,2) at the four
# primes above 3 and 5, (1,4) at t1, t2 above 29 and at P41[1]
SEL = [(16, Q(1, 32)), (9, Q(1, 4)), (25, Q(1, 4)), (29**4, Q(1, 4)), (41**4, Q(1, 8))]


def w(q):
    L = arb(q).log()
    tot = arb(0)
    m = 1
    while True:
        term = 1 / (arb(q) ** m + 1)
        tot += term
        if term < arb(10) ** -70:
            break
        m += 1
    tail = arb(0, 1) * (2 * term.upper())      # remaining terms < the last one times a geometric factor <= 2 (in Arb)
    return 2 * L * (tot + tail)


def kernel_ok(a, b, eps, xmin, step=Q(1, 64), depth=12):
    """h(x) >= 0 for x >= xmin.  On [x, x + w] h >= h(x) - w * sup|h'|, with
    |h'| <= a eps + 2 b (1 + x_hi e^{-x}) + 2 e^{-x} (bounded on each cell); a cell whose bound is not positive is
    bisected, down to width step / 2^depth; beyond X1 = 1/b + 1, 2 b x (1 - e^{-x}) - 1 - 2 e^{-x} is positive and
    increasing."""
    A, B, E = arb(a.numerator) / a.denominator, arb(b.numerator) / b.denominator, eps
    X1 = 1 / B + 1

    def low(x, w):
        xh = x + w
        hx = A * (-E * x).exp() + 2 * B * x * (1 - (-x).exp()) - (1 + 2 * (-x).exp())
        dmax = A * E + 2 * B * (1 + xh * (-x).exp()) + 2 * (-x).exp()
        return hx - w * dmax

    x = arb(xmin.numerator) / xmin.denominator
    h0 = arb(step.numerator) / step.denominator
    worst = None
    n = 0
    while x < X1:
        stack = [(x, h0, 0)]
        while stack:
            cx, w, d = stack.pop()
            lo = low(cx, w)
            n += 1
            if lo > 0:
                if worst is None or lo.lower() < worst:
                    worst = lo.lower()
                continue
            if d >= depth:
                return False, float(cx.mid()), lo.lower()
            stack.append((cx + w / 2, w / 2, d + 1))
            stack.append((cx, w / 2, d + 1))
        x = x + h0
    tail_ok = 2 * B * X1 * (1 - (-X1).exp()) - (1 + 2 * (-X1).exp()) > 0
    return bool(tail_ok), n, worst


def kernel_closed_form(a, b, eps, x0):
    """Independent check of h >= 0 on [x0, oo), x0 >= 1: h(x) = phi(x) - (2 b x + 2) e^{-x} with
    phi(x) = a e^{-eps x} + 2 b x - 1 convex, min phi = (2b/eps)(1 + log(a eps/(2b))) - 1, and
    (2 b x + 2) e^{-x} decreasing for x >= 1."""
    A, B = arb(a.numerator) / a.denominator, arb(b.numerator) / b.denominator
    assert x0 >= 1
    phimin = (2 * B / eps) * (1 + (A * eps / (2 * B)).log()) - 1
    return phimin - (2 * B * x0 + 2) * (-x0).exp()


def kernel_small_ok(a, b, s, qmax, ratio=Q(401, 400)):
    """(*) for 2 <= q <= qmax, on geometric cells [q0, q1]: g_1 and g_sigma decrease in q and
    w(q) >= 2 log q/(q+1), so it suffices that a g_sigma(q1) + 2 b log(q0)/(q1 + 1) >= g_1(q0)."""
    A, B = arb(a.numerator) / a.denominator, arb(b.numerator) / b.denominator
    r = arb(ratio.numerator) / ratio.denominator
    q0 = arb(2)
    worst = None
    n = 0
    while q0 < qmax:
        q1 = q0 * r
        lhs = -(1 - 1 / q0).log()
        rhs = A * (-(1 - q1 ** (-s)).log()) + 2 * B * q0.log() / (q1 + 1)
        d = ((rhs - lhs) * q0).lower()
        worst = d if worst is None or d < worst else worst
        if not rhs > lhs:
            return False, float(q0.mid()), worst
        q0 = q1
        n += 1
    return True, n, worst


def main(delta_q, sigma_q, ye_path, a, b, prefixes):
    with contextlib.redirect_stdout(io.StringIO()):
        C_W, gain = DCm.main(delta_q, sigma_q, ye_path, prefixes)
    c = DCm.main.components
    s = arb(sigma_q.numerator) / sigma_q.denominator
    eps = s - 1
    g = DCm.g
    Zsel = lambda u: sum((arb(be.numerator) / be.denominator * g(q, u) for q, be in SEL), arb(0))  # noqa: E731
    ell = arb(9) / 4 * arb(2).log() + (arb(3).log() + arb(5).log() + arb(241).log()) / 2
    kappa = (ell - arb.const_euler() - (4 * arb.pi()).log()) / 4
    assert abs(kappa - c["Bhalf"]) < arb(10) ** -40
    TVsel = sum((arb(be.numerator) / be.denominator * w(q) for q, be in SEL), arb(0))
    B_r = 2 * kappa - TVsel
    # termwise bound at sigma for the non-selected primes (census corrections included)
    Ystar = c["Y_W"] - c["sel"] - c["sav"] - c["census_small"] - c["census_bins"]
    Y_r = Ystar - Zsel(s)
    qmin = min(c["qmin_rest_upto_XA"], c["XA"])
    xmin = math.log(qmin) - 1e-9
    ok, info, worst = kernel_ok(a, b, eps, Q(int(xmin * 10**6), 10**6))
    assert ok, ("kernel inequality fails", info, worst)
    ok2, info2, worst2 = kernel_small_ok(a, b, s, arb(qmin) * 2)
    assert ok2, ("kernel inequality fails below q_min", info2, worst2)
    hcf = kernel_closed_form(a, b, eps, arb(int(xmin * 10**6)) / 10**6)
    assert hcf > 0, ("closed-form kernel bound fails", hcf)
    A_, B_ = arb(a.numerator) / a.denominator, arb(b.numerator) / b.denominator
    assert A_ >= 1
    bound = Zsel(1) + A_ * Y_r + B_ * B_r
    C_eff = bound - c["adaptive_small"]
    old = C_W - gain
    out = {"sigma": str(sigma_q), "a": str(a), "b": str(b), "q_min": qmin, "kernel_cells": info,
           "kernel_min_lower": str(worst), "kernel_cells_below_q_min": info2,
           "kernel_min_lower_below_q_min": str(worst2), "kernel_closed_form_lower": str(hcf.lower()), "Z_sel(1)": str(Zsel(1)), "Y_r(sigma)": str(Y_r), "B_r": str(B_r),
           "C_eff_old_upper": str(old.upper()), "C_eff_upper": str(C_eff.upper())}
    print(json.dumps(out, indent=1))
    return C_eff


if __name__ == "__main__":
    main(Q(sys.argv[1]), Q(sys.argv[2]), sys.argv[3], Q(sys.argv[4]), Q(sys.argv[5]), sys.argv[6:])
