#!/usr/bin/env python3
"""Certified approximate functional equation for degree-8 L-functions with gamma factor Gamma_C(s)^4.

For an entire L(s) = sum a_n n^-s with real a_n, Lambda(s) = Q^{s/2} Gamma_C(s)^4 L(s) = Lambda(1 - s), and real s:

    L(s) = t^s / Gamma(s)^4 * sum_n a_n [K_s(t n) + K_{1-s}(t n)],    t = (2 pi)^4 / sqrt(Q),

    K_b(x) = x^-b I_b(x),   I_b(x) = int_x^oo u^(b-1) G(u) du = (1/2 pi i) int Gamma(b + w)^4 x^-w dw/w,

with G(x) = G^{4,0}_{0,4}(x | 0,0,0,0) = (1/2 pi i) int Gamma(u)^4 x^-u du.  (I_b for b < 0 is the same contour
integral; the termwise formula below continues it analytically.)

Ingredients, all in Arb:
  * G and I_b at a point (or a ball) from the residue series at 0:
        G(x)   = sum_n x^n/(n!)^4 [e^3] H_n(e) x^-e,
        I_b(x) = Gamma(b)^4 - sum_n x^(n+b)/(n!)^4 [e^3] H_n(e) x^-e / (n + b - e),
    H_n(e) = Gamma(1+e)^4 prod_{k<=n} (1 - e/k)^-4, with the working precision raised to absorb the cancellation
    (the terms reach e^{4 x^{1/4}}), and a rigorous bound for the truncated tail (majorant series);
  * Taylor coefficients of G at a point from G, G', G'', G''' and the ODE x^3 G'''' + 6x^2 G''' + 7x G'' + G' = G;
    of K_b from x K_b' + b K_b = -G (p_{j+1} = -(k_j + (j + b) p_j)/(c (j+1)));
  * on each cell [c 31/32, c] of the x-grid c_i = X_TOP (31/32)^i, the degree-DEG Taylor polynomial at c and a
    Lagrange remainder from the (DEG+1)-th coefficient at the left end c 31/32 (K_b is completely monotone);
  * the Dirichlet tail beyond N: K_b(x) <= A x^(-b-c) with A = Gamma(b+c)^4 (b+c)/(4c) (Mellin-Barnes with
    |Gamma(sigma+iy)| <= Gamma(sigma) (1 + y^2/sigma^2)^-1/2), and Rankin with |a_n| <= d_8(n).
"""
import math
from fractions import Fraction as Q
from flint import arb, arb_series, ctx

DEG = 20
X_TOP = arb(2) ** 14            # K_b(x) < 1e-25 beyond (checked by the tail bound)
RATIO = arb(31) / 32


def _prec_for(x):
    xf = max(float(abs(x.mid())) + float(x.rad()), 1.0)
    return int(96 + 2 * 4 * xf ** 0.25 / math.log(2) + 60)


def _H_series(n_max):
    """H_n(e) = Gamma(1+e)^4 prod_{k<=n} (1 - e/k)^-4 as series to e^3, n = 0..n_max"""
    e = arb_series([0, 1])
    H = (1 + e).gamma() ** 4
    out = [H]
    for k in range(1, n_max + 1):
        H = H * (1 - e / k) ** (-4)
        out.append(H)
    return out


def _coef_bound(n, absL, k, bmin):
    """Cauchy bound on |e| = 1/2 for |[e^3] H_n(e) x^-e ff_k(n - e) / (n + b - e)| (or without the last factor):
    |Gamma(1+e)| <= Gamma(1/2) on |e| = 1/2 (|Gamma(z)| <= Gamma(Re z)), |1 - e/k|^-1 <= (1 - 1/(2k))^-1,
    |x^-e| <= e^(|L|/2), |ff_k(n - e)| <= (n + 1)^k, |n + b - e| >= n + bmin - 1/2 (> 0 for the n used)."""
    P = 1.0
    for kk in range(1, n + 1):
        P *= 1.0 / (1.0 - 1.0 / (2 * kk))
    M = math.gamma(0.5) ** 4 * P ** 4 * math.exp(absL / 2) * (n + 1) ** k
    den = n + bmin - 0.5
    if den <= 0.25:
        den = 0.25
    return M * 8 / den * 1.0001          # / rho^3 with rho = 1/2


def G_and_I(x, bs, kmax=3):
    """rigorous [G^(k)(x) for k <= kmax] and [I_b(x) for b in bs]; x an arb (point or ball), x > 0"""
    old_prec, old_cap = ctx.prec, ctx.cap
    ctx.prec = _prec_for(x)
    ctx.cap = 4
    try:
        x = arb(x)
        assert x > 0
        L = x.log()
        e = arb_series([0, 1])
        xe = (-(e * L)).exp()                                    # x^-e
        Gk = [arb(0)] * (kmax + 1)
        Ib = [arb(0)] * len(bs)
        bA = [arb(Q(b).numerator) / Q(b).denominator for b in bs]          # exact rationals at the raised precision
        xf = float(x.mid()) + float(x.rad())
        nstop = None
        n = 0
        H = (1 + e).gamma() ** 4
        nf4 = arb(1)
        xn = arb(1)
        while True:
            if n > 0:
                H = H * (1 - e / n) ** (-4)
                nf4 = nf4 * n ** 4
                xn = xn * x
            base = H * xe
            for k in range(kmax + 1):
                ff = arb_series([1])
                for i in range(k):
                    ff = ff * (n - i - e)
                c = (base * ff).coeffs() + [arb(0)] * 4
                Gk[k] += c[3] * (xn / x ** k) / nf4
            for i, b in enumerate(bA):
                c = (base / (n + b - e)).coeffs() + [arb(0)] * 4
                Ib[i] += c[3] * xn * x ** b / nf4
            if n > 2 * 4 * xf ** 0.25 + 8:
                t_n = xn / nf4
                if t_n.upper() < arb(2) ** (-ctx.prec // 2):
                    nstop = n
                    break
            n += 1
        # tail m > nstop: x^m/(m!)^4 has ratio x/(m+1)^4 <= 1/(2^4 * 2) here, the Cauchy bounds grow by at most
        # a factor 2 per step, so the tail is at most twice the first omitted term
        m = nstop + 1
        absL = float(abs(L).upper())
        tm = float((xn * x / (nf4 * arb(m) ** 4)).upper())
        bmin = min(float(b.lower()) for b in bA) if bA else 1.0
        remG = [2 * tm * _coef_bound(m, absL, k, 1.0) / float((x ** k).lower()) for k in range(kmax + 1)]
        remI = 2 * tm * _coef_bound(m, absL, 0, bmin)
        Gk = [g + arb(0, r) for g, r in zip(Gk, remG)]
        Ib = [arb(b).gamma() ** 4 - (I + arb(0, remI * float((x ** b).upper()))) for b, I in zip(bA, Ib)]
        return Gk, Ib
    finally:
        ctx.prec, ctx.cap = old_prec, old_cap


def G_taylor(c, gk, deg):
    """Taylor coefficients g_0..g_deg of G at c from g_j = G^(j)(c)/j! (j <= 3) and the ODE
    x^3 G'''' + 6 x^2 G''' + 7 x G'' + G' - G = 0."""
    g = [gk[0], gk[1], gk[2] / 2, gk[3] / 6]
    # coefficient of h^j in the ODE with x = c + h:
    #   sum over i of binom(3,i) c^(3-i) * [h^(j-i)] G''''  + 6 sum binom(2,i) c^(2-i) [h^(j-i)] G''' + 7 (c [h^j] G'' + [h^(j-1)] G'')
    #   + [h^j] G' - g_j = 0, with [h^m] G^(r) = (m+1)...(m+r) g_{m+r}
    def D(r, m):
        if m < 0:
            return arb(0)
        f = arb(1)
        for q in range(1, r + 1):
            f *= m + q
        return f * g[m + r]
    for j in range(0, deg - 3):
        # unknown g_{j+4} appears in c^3 [h^j] G'''' = c^3 (j+1)(j+2)(j+3)(j+4) g_{j+4}
        rest = arb(0)
        for i in range(1, 4):
            rest += math.comb(3, i) * c ** (3 - i) * D(4, j - i)
        for i in range(0, 3):
            rest += 6 * math.comb(2, i) * c ** (2 - i) * D(3, j - i)
        rest += 7 * (c * D(2, j) + D(2, j - 1))
        rest += D(1, j) - g[j]
        f = arb((j + 1) * (j + 2) * (j + 3) * (j + 4))
        g.append(-rest / (c ** 3 * f))
    return g


def K_taylor(c, gcoef, b, K0, deg):
    """Taylor coefficients of K_b at c from K_b(c) = K0 and x K' + b K = -G"""
    p = [K0]
    for j in range(deg):
        p.append(-(gcoef[j] + (j + b) * p[j]) / (c * (j + 1)))
    return p


def dyadic(m, e):
    """the exact number m 2^e"""
    return arb(m) * arb(2) ** e


class OcticKernel:
    """Per abscissa s (a Fraction): on each cell [c_{i+1}, c_i] of an exact dyadic grid (c_0 = X_TOP, ratio about
    31/32), polynomials P_b (b = s, 1 - s) of degree DEG in h = x - c_i with K_b(c_i + h) in P_b(h) + [-R_b, R_b]
    for h in [c_{i+1} - c_i, 0]."""

    def __init__(self, s, deg=DEG, x_bottom=arb(2) ** -40):
        s = Q(s)
        self.sq = s
        self.s = arb(s.numerator) / s.denominator
        self.deg = deg
        bs = [s, 1 - s]
        self.cells = []
        # grid c_i = m_i 2^-64 with m_0 = 2^78 (= 2^14) and m_{i+1} = floor(31 m_i / 32)
        m = 2 ** 78
        # K_b(x) = int_1^oo v^(b-1) G(x v) dv and G (the density of a product of four Exp(1) variables) are
        # completely monotone, so |K_b^(j)| decreases: on [c_{i+1}, c_i] the Lagrange remainder of the expansion
        # at c_i is at most |K_b^(DEG+1)(c_{i+1})|/(DEG+1)! (c_i - c_{i+1})^(DEG+1), a point evaluation.
        while True:
            m2 = (31 * m) // 32
            c, left = dyadic(m, -64), dyadic(m2, -64)
            if c < x_bottom:
                break
            width = dyadic(m - m2, -64)
            gk, Ib = G_and_I(c, bs)
            gco = G_taylor(c, gk, deg + 1)
            gkl, Ibl = G_and_I(left, bs)
            gcol = G_taylor(left, gkl, deg + 1)
            polys, rems = [], []
            for i, b in enumerate(bs):
                bA = arb(b.numerator) / b.denominator
                p = K_taylor(c, gco, bA, c ** (-bA) * Ib[i], deg)
                pl = K_taylor(left, gcol, bA, left ** (-bA) * Ibl[i], deg + 1)
                polys.append(p)
                rems.append(abs(pl[deg + 1]).upper() * width ** (deg + 1))
            self.cells.append((c, left, polys, rems))
            m = m2

    def prefactor(self, conductor):
        t = (2 * arb.pi()) ** 4 / arb(conductor).sqrt()
        return t, t ** self.s / self.s.gamma() ** 4

    def tail_bound(self, conductor, N):
        """sum_{n > N} d_8(n) (K_s + K_{1-s})(t n), with K_b(x) <= A x^(-b-cc), A = Gamma(b+cc)^4 (b+cc)/(4cc)
        (Mellin-Barnes on Re w = cc with |Gamma(sigma+iy)| <= Gamma(sigma) (1 + y^2/sigma^2)^-1/2), and Rankin:
        sum_{n>N} d_8(n) n^(-e) <= zeta(beta)^8 N^(beta - e) for e > beta.  The shift cc and beta are optimized."""
        t, _ = self.prefactor(conductor)
        best = None
        for beta in (Q(11, 10), Q(6, 5), Q(13, 10), Q(3, 2), Q(2)):
            bA = arb(beta.numerator) / beta.denominator
            z8 = bA.zeta() ** 8
            for cc in range(2, 80):
                tot = arb(0)
                for b in (self.s, 1 - self.s):
                    A = (b + cc).gamma() ** 4 * (b + cc) / (4 * cc)
                    ex = b + cc
                    tot += A * t ** (-ex) * z8 * arb(N) ** (bA - ex)
                if best is None or tot.upper() < best.upper():
                    best = tot
        return best


def _floor(x):
    n = x.floor().unique_fmpz()
    assert n is not None, "unresolved cell boundary: raise the precision"
    return int(n)


def evaluate_direct(a, conductor, kernel):
    """L(s) from coefficients a[0..N] (a[0] unused), summing over n with the cell polynomials; the n of a cell
    (left, c] are floor(left/t) + 1 .. floor(c/t), certified"""
    N = len(a) - 1
    t, pref = kernel.prefactor(conductor)
    tot = arb(0)
    err = arb(0)
    covered = 0
    for (c, left, polys, rems) in kernel.cells:
        lo = max(1, _floor(left / t) + 1)
        hi = min(N, _floor(c / t))
        if lo > hi:
            continue
        covered += hi - lo + 1
        for n in range(lo, hi + 1):
            if a[n] == 0:
                continue
            h = t * n - c
            for p, r in zip(polys, rems):
                v = arb(0)
                for co in reversed(p):
                    v = v * h + co
                tot += a[n] * v
                err += abs(a[n]) * r
    assert covered == N, (covered, N)            # cells tile 1..N (needs t * 1 > x_bottom and t * N <= X_TOP)
    tail = kernel.tail_bound(conductor, N)
    return pref * (tot + arb(0, (err + tail).upper()))
