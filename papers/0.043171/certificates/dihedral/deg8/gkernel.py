#!/usr/bin/env python3
"""Certified approximate-functional-equation kernels for self-dual L-functions with root number 1 and gamma factor

    gamma(s) = C kappa^(-s) prod_j Gamma(s/d + a_j),        a_j in {0, 1/2},  d in {1, 2}.

Types used here (TYPES): 'octic'   Gamma_C(s)^4            = 16 (2pi)^(-4s) Gamma(s)^4             (d = 1)
                          'quartic' Gamma_C(s)^2            =  4 (2pi)^(-2s) Gamma(s)^2             (d = 1)
                          'mixed31' Gamma_R(s)^3 Gamma_R(s+1) = pi^(-1/2) pi^(-2s) G(s/2)^3 G(s/2+1/2) (d = 2)
                          'mixed13' Gamma_R(s) Gamma_R(s+1)^3 = pi^(-3/2) pi^(-2s) G(s/2) G(s/2+1/2)^3 (d = 2)

AFE.  With Lambda(s) = Q^(s/2) gamma(s) L(s) = Lambda(1 - s), t = kappa / sqrt(Q), x_n = (t n)^d and real s:

    L(s) = t^s / prod_j Gamma(s/d + a_j) * sum_n a_n [K_{s/d}(x_n) + K_{(1-s)/d}(x_n)],

    K_b(x) = x^-b I_b(x),   I_b(x) = (1/2 pi i) int_(c) prod_j Gamma(b + a_j + u) x^-u du/u   (c right of all poles),

which follows from Lambda(s) = (1/2pi i) int [Lambda(s+w) + Lambda(1-s+w)] dw/w and u = w/d.  With
H(x) = (1/2 pi i) int prod_j Gamma(a_j + u) x^-u du (the Mellin convolution of the x^(a_j) e^-x):

  * I_b(x) = int_x^oo v^(b-1) H(v) dv and K_b(x) = int_1^oo v^(b-1) H(x v) dv.  At least one a_j is 0 and e^-x is
    completely monotone, so H and every K_b are completely monotone: |K_b^(k)| decreases on (0, oo);
  * x K_b' + b K_b = -H (Taylor recursion p_{j+1} = -(h_j + (j + b) p_j) / (c (j + 1)));
  * residue series (shifting the contour to the left; u = -n - a + e at the poles of order m_a = #{j: a_j = a}):
        H(x)   =  sum_a sum_n [e^(m_a - 1)] F_{a,n}(e) x^(n + a - e),
        I_b(x) =  prod_j Gamma(b + a_j) - sum_a sum_n [e^(m_a - 1)] F_{a,n}(e) x^(n + a + b - e) / (n + a + b - e),
        F_{a,n}(e) = ((-1)^n / n!)^m_a (Gamma(1 + e) prod_{k<=n} (1 - e/k)^-1)^m_a prod_{a' != a} Gamma(-n + a' - a + e)^m_a',
    and the Taylor coefficients of H at c from the derivatives of x^(n + a - e).  The cancellation in these
    alternating sums (terms up to about e^(4 x^(1/4))) is absorbed by raising the working precision; the truncated
    tail is bounded by Cauchy's estimate on |e| = rho (rho = 1/2 for one shift class, 1/4 for two) and a
    ratio bound that decreases in n (see _tail_bound);
  * Dirichlet tail beyond the last cell: K_b(x) <= A_c x^(-b-c), A_c = prod_j Gamma(b + a_j + c) * s_max / (m' c)
    (|Gamma(sigma + iy)| <= Gamma(sigma) (1 + y^2/sigma^2)^-1/2; m' = 4 for four gamma factors, 2 for two), and
    Rankin with |a_n| <= d_deg(n):  sum_{n > N} d_deg(n) n^-e <= zeta(beta)^deg N^(beta - e).

Cells: x-grid c_0 = XTOP(type), c_{i+1} = c_i 31/32 rounded down to 53 significant bits (exact doubles), down to
2^-40.  On [c_{i+1}, c_i], K_b(c_i + h) = sum_{j <= DEG} p_j h^j + r with |r| <= |p^left_{DEG+1}| (c_i - c_{i+1})^(DEG+1),
p^left the Taylor coefficients at c_{i+1} (complete monotonicity).  The kernel in the normalized variable
u = (x - c_i)/c_i is  sum_j (p_j c_i^j) u^j.
"""
import math
from fractions import Fraction as Q

from flint import arb, arb_series, ctx

DEG = 20
TYPES = {
    "octic":   {"shifts": (Q(0), Q(0), Q(0), Q(0)), "d": 1, "kappa": lambda: (2 * arb.pi()) ** 4, "xtop": 6144, "deg": 8},
    "quartic": {"shifts": (Q(0), Q(0)), "d": 1, "kappa": lambda: (2 * arb.pi()) ** 2, "xtop": 2**9, "deg": 4},
    "mixed31": {"shifts": (Q(0), Q(0), Q(0), Q(1, 2)), "d": 2, "kappa": lambda: arb.pi() ** 2, "xtop": 2**14, "deg": 4},
    "mixed13": {"shifts": (Q(0), Q(1, 2), Q(1, 2), Q(1, 2)), "d": 2, "kappa": lambda: arb.pi() ** 2, "xtop": 2**14, "deg": 4},
}
X_BOTTOM = Q(1, 2**40)


def A(q):
    q = Q(q)
    return arb(q.numerator) / q.denominator


def grid(xtop):
    """exact cell endpoints (Fractions with <= 53 significant bits), decreasing from xtop to below X_BOTTOM"""
    out = [Q(xtop)]
    M, E = xtop, 0
    assert isinstance(xtop, int) and 0 < xtop < 2**53
    while out[-1] >= X_BOTTOM:
        M = 31 * M
        E -= 5
        sh = M.bit_length() - 53
        if sh > 0:
            M >>= sh
            E += sh
        out.append(Q(M) * Q(2) ** E)
    return out


def _prec_for(xf, m):
    """working precision for the residue series of an m-fold Gamma product at x: its terms reach about
    exp(m x^(1/m))"""
    return int(96 + 2 * m * max(xf, 1.0) ** (1.0 / m) / math.log(2) + 60)


def _n0(xf, m, kmin=0):
    """truncation index: the terms x^n/(n!)^m decay geometrically (ratio <= 1/2 checked in _tail_bound)"""
    return max(int(2 * math.e * max(xf, 1.0) ** (1.0 / m)) + 10, kmin + 4)


class Shape:
    """the multiset of shifts, grouped: classes [(a, m_a)]"""

    def __init__(self, shifts):
        self.shifts = tuple(Q(a) for a in shifts)
        self.classes = sorted({a: self.shifts.count(a) for a in set(self.shifts)}.items())
        assert all(a in (Q(0), Q(1, 2)) for a, _ in self.classes) and Q(0) in dict(self.classes)
        self.rho = 0.5 if len(self.classes) == 1 else 0.25


def _F_series(shape, a, ma, n, e):
    """F_{a,n}(e) as an arb_series (without the x-power), length ma"""
    F = ((1 + e).gamma() * 1) ** ma
    sgn = -1 if (n * ma) % 2 else 1
    nf = arb(math.factorial(n)) ** ma if n < 400 else arb(n + 1).gamma() ** ma
    for k in range(1, n + 1):
        F = F * (1 - e / k) ** (-ma)
    F = F * (sgn / nf)
    for a2, m2 in shape.classes:
        if a2 == a:
            continue
        F = F * ((-n + A(a2 - a)) + e).gamma() ** m2
    return F


def _cauchy_logbound(shape, a, ma, n, absL, extra):
    """log of an upper bound for |[e^(ma-1)] F_{a,n}(e) x^-e * extra(e)| (Cauchy's estimate on |e| = rho), where
    |x^-e| <= exp(rho |log x|) and extra(e) is bounded by the float `extra` on the circle"""
    rho = shape.rho
    g1 = math.gamma(1 - rho)                           # |Gamma(1 + e)| <= Gamma(Re(1 + e)) <= Gamma(1 - rho)
    P = 1.0
    for k in range(1, n + 1):
        P /= (1 - rho / k)
    lg = ma * (math.log(g1) + math.log(P) - math.lgamma(n + 1))
    for a2, m2 in shape.classes:
        if a2 == a:
            continue
        # Gamma(-n + d + e), d = +-1/2: = pi / (sin(pi z) Gamma(1 - z)), |sin(pi z)| = |cos(pi e)| >= cos(pi rho),
        # |Gamma(sigma + iy)| >= Gamma(sigma) (pi y / sinh(pi y))^(1/2) >= 0.95 Gamma(sigma) for sigma >= 1, |y| <= 1/4,
        # and Gamma(Re(1 - z)) >= Gamma(sig) since Re(1 - z) >= sig >= 1.5 > 1.4616 (Gamma increasing there)
        d = float(a2 - a)
        sig = n + 1 - d - rho
        assert sig >= 1.5
        lg += m2 * (math.log(math.pi) - math.log(math.cos(math.pi * rho)) - math.log(0.95) - math.lgamma(sig))
    lg += rho * absL - (ma - 1) * math.log(rho)
    return lg + math.log(extra) + 1e-4


def _tail_bound(shape, xf, absL, n0, extra_fn, extra_decreasing=False):
    """bound for sum_{n >= n0} sum_a |[e^(m_a - 1)] F_{a,n} x^(n + a - e) extra_{a,n}|.  The Cauchy bounds C_a(n) x^(n+a)
    have consecutive ratios x (n + 1)^-m_a (1 - rho/(n+1))^-m_a prod (n + 1 - d - rho)^-m_a', each factor decreasing in
    n.  extra_fn is either a falling-factorial bound (its ratio decreases for n >= its order, n0 > order) and is kept
    in the ratio, or (extra_decreasing) a decreasing factor, bounded by its value at n0 and kept out of the ratio.  The
    ratio at n0 is then a bound for all later ratios; it is checked to be <= 1/2.  The result is floored at 1e-300
    (an underflowing float bound is below that)."""
    tot = 0.0
    lx = math.log(xf)
    for a, ma in shape.classes:
        e0 = 1.0 if extra_decreasing else extra_fn(a, n0)
        e1 = 1.0 if extra_decreasing else extra_fn(a, n0 + 1)
        l0 = _cauchy_logbound(shape, a, ma, n0, absL, e0) + (n0 + float(a)) * lx
        l1 = _cauchy_logbound(shape, a, ma, n0 + 1, absL, e1) + (n0 + 1 + float(a)) * lx
        r = math.exp(l1 - l0)
        assert r <= 0.5, (r, n0, xf)
        term = math.exp(l0) / (1 - r)
        if extra_decreasing:
            term *= extra_fn(a, n0)
        tot += term
    return max(tot * 1.0001, 1e-300)


def H_taylor(shape, c, kmax):
    """[h_0, ..., h_kmax], h_k = H^(k)(c)/k! at the exact point c (Fraction), certified"""
    xf = float(c)
    old = (ctx.prec, ctx.cap)
    ctx.prec = _prec_for(xf, len(shape.shifts)) + 4 * kmax
    try:
        x = A(c)
        L = x.log()
        absL = abs(math.log(xf))
        out = [arb(0)] * (kmax + 1)
        n0 = _n0(xf, len(shape.shifts), kmax)
        for a, ma in shape.classes:
            ctx.cap = ma
            e = arb_series([0, 1], prec=ctx.prec)
            xe = (-(e * L)).exp()
            for n in range(n0):
                base = _F_series(shape, a, ma, n, e) * xe
                xp = x ** (n + A(a))
                ff = arb_series([1])
                kfac = arb(1)
                for k in range(kmax + 1):
                    if k > 0:
                        ff = ff * (n + A(a) - (k - 1) - e)
                        kfac *= k
                    cf = (base * ff).coeffs()
                    cf = cf + [arb(0)] * (ma - len(cf))
                    out[k] += cf[ma - 1] * xp / (x ** k * kfac)
        # tail n >= n0: |ff_k(n + a - e)| <= prod_{i<k} (|n + a - i| + rho); / (k! c^k)
        for k in range(kmax + 1):
            def extra(a, n, k=k):
                v = 1.0
                for i in range(k):
                    v *= abs(n + float(a) - i) + shape.rho
                return v / (math.factorial(k) * xf ** k)
            out[k] += arb(0, _tail_bound(shape, xf, absL, n0, extra))
        return out
    finally:
        ctx.prec, ctx.cap = old


def I_values(shape, c, bs):
    """[I_b(c) for b in bs] (bs Fractions), certified"""
    xf = float(c)
    old = (ctx.prec, ctx.cap)
    # b near 0 (b = (1 - s)/d): Gamma(b)^m and the residue at u = -b nearly cancel; add the lost bits
    near = min(abs(float(n + a + b)) for b in bs for a, _ in shape.classes for n in (0, 1))
    ctx.prec = _prec_for(xf, len(shape.shifts)) + int(len(shape.shifts) * max(0.0, -math.log2(near))) + 40
    try:
        x = A(c)
        L = x.log()
        absL = abs(math.log(xf))
        n0 = _n0(xf, len(shape.shifts))
        res = []
        for b in bs:
            bA = A(b)
            tot = arb(0)
            G0 = arb(1)
            for aj in shape.shifts:
                G0 *= (bA + A(aj)).gamma()
            for a, ma in shape.classes:
                ctx.cap = ma
                e = arb_series([0, 1], prec=ctx.prec)
                xe = (-(e * L)).exp()
                for n in range(n0):
                    den = n + A(a) + bA
                    assert den != 0
                    base = _F_series(shape, a, ma, n, e) * xe / (den - e)
                    cf = base.coeffs()
                    cf = cf + [arb(0)] * (ma - len(cf))
                    tot += cf[ma - 1] * x ** (n + A(a) + bA)
            def extra(a, n, b=b):                     # decreasing in n for n >= n0 (n0 + b - rho > 0)
                assert n + float(a) + float(b) - shape.rho > 0
                return 1.0 / (n + float(a) + float(b) - shape.rho)
            tb = _tail_bound(shape, xf, absL, n0, extra, extra_decreasing=True) * xf ** float(b)
            res.append(G0 - tot + arb(0, tb))
        return res
    finally:
        ctx.prec, ctx.cap = old


def K_taylor(c, hco, b, K0, deg):
    p = [K0]
    for j in range(deg):
        p.append(-(hco[j] + (j + b) * p[j]) / (c * (j + 1)))
    return p


class HTable:
    """sigma-independent part: the grid and the Taylor coefficients of H at every endpoint (orders 0..DEG+1)"""

    def __init__(self, tname, deg=DEG, verbose=False):
        T = TYPES[tname]
        self.tname = tname
        self.shape = Shape(T["shifts"])
        self.deg = deg
        self.pts = grid(T["xtop"])
        self.h = []
        for i, c in enumerate(self.pts):
            self.h.append(H_taylor(self.shape, c, deg + 1))
            if verbose and i % 100 == 0:
                print(f"  H table {tname}: {i}/{len(self.pts)}", flush=True)


class Kernel:
    """per abscissa s: for each cell i, the polynomial q_i(u) = sum_j q_ij u^j of (K_{s/d} + K_{(1-s)/d})(c_i (1 + u))
    and the remainder bound R_i, u in [c_{i+1}/c_i - 1, 0]"""

    def __init__(self, table, s, prec=256):
        ctx.prec = prec
        T = TYPES[table.tname]
        self.table = table
        self.s = Q(s)
        self.d = T["d"]
        self.bs = [self.s / self.d, (1 - self.s) / self.d]
        shape, deg = table.shape, table.deg
        Ivals = [I_values(shape, c, self.bs) for c in table.pts]
        self.cells = []
        for i in range(len(table.pts) - 1):
            c, cl = table.pts[i], table.pts[i + 1]
            cA, clA = A(c), A(cl)
            width = cA - clA
            qsum = [arb(0)] * (deg + 1)
            R = arb(0)
            for k, b in enumerate(self.bs):
                bA = A(b)
                p = K_taylor(cA, table.h[i], bA, cA ** (-bA) * Ivals[i][k], deg)
                pl = K_taylor(clA, table.h[i + 1], bA, clA ** (-bA) * Ivals[i + 1][k], deg + 1)
                R += abs(pl[deg + 1]) * width ** (deg + 1)
                for j in range(deg + 1):
                    qsum[j] += p[j] * cA ** j
            self.cells.append({"c": c, "left": cl, "q": qsum, "R": arb(R.upper())})
        sA = A(self.s)
        G = arb(1)
        for aj in shape.shifts:
            G *= (sA / self.d + A(aj)).gamma()
        self.gprod = G

    def prefactor(self, conductor):
        t = TYPES[self.table.tname]["kappa"]() / arb(conductor).sqrt()
        return t, t ** A(self.s) / self.gprod

    def tail_bound(self, conductor, N, logE=None, betas=None):
        """sum_{n > N} |a_n| (K_{s/d} + K_{(1-s)/d})(x_n), x_n = (t n)^d, with Rankin's bound
        sum_{n > N} |a_n| n^-e <= N^(beta - e) E(beta); logE(beta) (a Fraction -> upper bound for log E(beta)) defaults
        to deg log zeta(beta) (|a_n| <= d_deg(n))"""
        T = TYPES[self.table.tname]
        t, _ = self.prefactor(conductor)
        shifts = self.table.shape.shifts
        mfac = 4 if len(shifts) == 4 else 2
        best = None
        for beta in (betas or (Q(11, 10), Q(6, 5), Q(13, 10), Q(3, 2), Q(2))):
            bA = A(beta)
            zd = (bA.zeta() ** T["deg"]) if logE is None else arb(logE(beta)).exp()
            for cc in range(1, 120):
                tot = arb(0)
                for b in self.bs:
                    sig = [A(b) + A(aj) + cc for aj in shifts]
                    if min(float(v.lower()) for v in sig) <= 0:
                        tot = None
                        break
                    Ac = arb(1)
                    for v in sig:
                        Ac *= v.gamma()
                    Ac *= max(sig, key=lambda v: float(v.upper())) / (mfac * cc)
                    ex = self.d * (A(b) + cc)                  # x_n^(-b-c) = (t n)^(-d (b + c))
                    if ex <= bA:
                        tot = None
                        break
                    tot += Ac * t ** (-ex) * zd * arb(N) ** (bA - ex)
                if tot is not None and (best is None or tot.upper() < best.upper()):
                    best = tot
        return best

    def nbounds(self, conductor):
        """exact integer thresholds: n is in cell i iff nb[i+1] < n <= nb[i] (x_n = (t n)^d in (c_{i+1}, c_i])"""
        t, _ = self.prefactor(conductor)
        out = []
        for c in self.table.pts:
            y = A(c) if self.d == 1 else A(c).sqrt()
            v = (y / t).floor().unique_fmpz()
            assert v is not None, "cell boundary unresolved"
            out.append(int(v))
        return out


def nbounds(tname, conductor):
    """exact integer thresholds of the grid of type tname for this conductor: n is in cell i iff
    nb[i+1] < n <= nb[i], i.e. x_n = (t n)^d in (c_{i+1}, c_i]"""
    T = TYPES[tname]
    t = T["kappa"]() / arb(conductor).sqrt()
    out = []
    for c in grid(T["xtop"]):
        y = A(c) if T["d"] == 1 else A(c).sqrt()
        v = (y / t).floor().unique_fmpz()
        assert v is not None, "cell boundary unresolved"
        out.append(int(v))
    return out


def evaluate_moments(kernel, conductor, moments, absums, N, logE=None, betas=None):
    """L(s) from per-cell moments M_ij = sum_{n in cell i} a_n u_n^j (as arb balls including their own errors) and
    A_i = sum_{n in cell i} |a_n|; N = the largest n summed (cells must cover 1..N)"""
    _, pref = kernel.prefactor(conductor)
    tot = arb(0)
    err = arb(0)
    for i, cell in enumerate(kernel.cells):
        if absums[i] == 0:
            continue
        for j, qj in enumerate(cell["q"]):
            tot += qj * moments[i][j]
        err += absums[i] * cell["R"]
    tail = kernel.tail_bound(conductor, N, logE, betas)
    return pref * (tot + arb(0, (err + tail).upper()))


def evaluate_direct(kernel, conductor, a):
    """L(s) from a[0..N] (a[0] unused) by summing the cell polynomials exactly in Arb (for tests)"""
    N = len(a) - 1
    t, pref = kernel.prefactor(conductor)
    nb = kernel.nbounds(conductor)
    tot = arb(0)
    err = arb(0)
    covered = 0
    for i, cell in enumerate(kernel.cells):
        lo, hi = max(1, nb[i + 1] + 1), min(N, nb[i])
        if lo > hi:
            continue
        cA = A(cell["c"])
        for n in range(lo, hi + 1):
            if a[n] == 0:
                continue
            x = (t * n) ** kernel.d
            u = x / cA - 1
            v = arb(0)
            for qj in reversed(cell["q"]):
                v = v * u + qj
            tot += a[n] * v
            err += abs(a[n]) * cell["R"]
        covered += hi - lo + 1
    assert covered == N, (covered, N)
    tail = kernel.tail_bound(conductor, N)
    return pref * (tot + arb(0, (err + tail).upper()))
