#!/usr/bin/env python3
"""Interval-arithmetic geometric margin for the tower over B = Q(sqrt 241).

Reuses the manuscript's certified profile routines (mass, overlap, Fourier tube)
and finite shell windows.  Inputs: delta, analytic ceiling C, shell profile file.

The first output line is the summary parsed by reproduce241.py (it keeps the
earlier name J_D for the pair functional).  The lines after it print every
enclosure stated in Section 8 of the paper, in the paper's notation: the
subscript R refers to the real places of F (compact coordinates, Gaussian
profile) and C to the complex places (pair coordinates, Student profile).
Printing does not change any computed value.
"""
import json
import sys
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
import env241  # noqa: E402
from mpmath import mp, iv  # noqa: E402
from interval_core import I, qi, lower, upper  # noqa: E402
from profile_certificate import mass_certificate, overlap_certificate, tube_certificate, interval_strings  # noqa: E402
from finite_windows import local_window  # noqa: E402

EF = {2: (8, 4), 3: (2, 2), 5: (2, 2), 29: (1, 4), 7: (1, 8)}
THETA = Q(65535, 131072)         # b/d = 1/(2|cl(iota_1)|) <= 2^-16, theta = (1-b/d)/2 >= 1/2 - 2^-17
PAPER_W = json.loads(env241.PAPER_WITNESS.read_text())


def enclosure(x, places=22):
    """Decimal enclosure of an interval: lower endpoint rounded down, upper rounded up."""
    lo, hi = interval_strings(x)
    step = Decimal(1).scaleb(-places)
    return "[%s, %s]" % (Decimal(lo).quantize(step, rounding=ROUND_FLOOR),
                         Decimal(hi).quantize(step, rounding=ROUND_CEILING))


def upper_decimal(text, places=22):
    """Round a decimal upper bound up to the given number of places."""
    return str(Decimal(text).quantize(Decimal(1).scaleb(-places), rounding=ROUND_CEILING))


def upper_rational(value, places=12):
    """Exact rational rounded up to the given number of decimal places."""
    value = Q(value)
    scale = 10**places
    return str(Decimal(-((-value.numerator * scale) // value.denominator)).scaleb(-places))


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
    local_terms = []
    for key, k in shells["ks"].items():
        prime = int(key)
        e, f = EF[prime]
        H += k * iv.log(prime) / e
        val, gain, rec = local_window(prime**f, int(k), shells["finite_profiles"][key], delta)
        finite += val / (e * f)
        # Report only: the hard-window value log(k+1) - delta*k*f*log(prime), per e*f.
        hard = (iv.log(int(k) + 1) - qi(delta) * int(k) * f * iv.log(prime)) / (e * f)
        local_terms.append((prime, e, f, int(k), len(shells["finite_profiles"][key]), val / (e * f), hard))
    mass, mass_rec = mass_certificate(Bm, s, p, PAPER_W["mass_grid"], PAPER_W["mass_terms"])
    overlap, overlap_rec = overlap_certificate(Bm, s, a, PAPER_W["overlap_order"])
    jd = (iv.log(overlap) + 2 * qi(1 + delta) * iv.log(qi(q)) - 2 * qi(delta) * iv.log(iv.pi)
          + 2 * qi(delta) * iv.log(qi(a)) - qi(1 + delta) * iv.log(mass))
    ac = 2 * p * delta
    jc = iv.log(qi(p) / 2) + qi(delta) * (iv.log(qi(ac) / iv.pi) - 1)
    slope = -iv.log(iv.pi) - 2 * jc + jd
    logK, sigma_D, tube_rec = tube_certificate(Bm, s, p, a, Q(PAPER_W["tube_width"]))
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
        # Terms of M_*(theta_*), in the order of the definition of M_*.
        terms = [("sum_r log F_{delta,r}/(e_r f_r)", finite),
                 ("-(1/2-delta) ell", -(I('.5') - qi(delta)) * ell),
                 ("-C", -qi(C)),
                 ("(1-delta) log 2", qi(1 - delta) * iv.log(2)),
                 ("(1-theta_*) log pi", (1 - qi(th)) * iv.log(iv.pi)),
                 ("(1-2 theta_*) J_R", (1 - 2 * qi(th)) * jc),
                 ("theta_* J_C^*", qi(th) * jd)]
        # The margin is affine in theta: M_*(theta) = M_*(0) + theta * slope.
        m_zero = (finite - (I('.5') - qi(delta)) * ell - qi(C) + qi(1 - delta) * iv.log(2)
                  + iv.log(iv.pi) + jc)
        theta_zero = -m_zero / slope
        report(p, q, ac, local_terms, finite, H, ell, mu, mass, mass_rec, overlap, overlap_rec,
               jc, jd, slope, logK, sigma_D, tube_rec, terms, Mstar, after, m_zero, theta_zero)
    return after, fourier_ok, lower(slope) > 0


def report(p, q, ac, local_terms, finite, H, ell, mu, mass, mass_rec, overlap, overlap_rec,
           jc, jd, slope, logK, sigma_D, tube_rec, terms, Mstar, after, m_zero, theta_zero):
    print("Certified enclosures (lower endpoints rounded down, upper endpoints rounded up):")
    print("  p = 2/(1+delta) =", p, "  q = s p - 1 =", q, "  a_R = 2 p delta =", ac)
    print("  local terms log F_{delta,r}/(e_r f_r): shell profile, and hard window")
    hard_sum = I(0)
    for prime, e, f, k, n, val, hard in local_terms:
        hard_sum += hard
        print("    r=%d (e,f)=(%d,%d) Q=%d k=%d weights=%d" % (prime, e, f, prime**f, k, n),
              enclosure(val, 16), enclosure(hard, 16))
    print("  finite sum sum_r log F_{delta,r}/(e_r f_r)", enclosure(finite))
    print("  hard-window sum J - delta H              ", enclosure(hard_sum))
    print("  H   ", enclosure(H))
    print("  ell ", enclosure(ell))
    print("  pair mass E P(T,T')^p", enclosure(mass))
    print("    largest local ratio rho_Q  =", mass_rec["max_local_radius"],
          "<", upper_rational(mass_rec["max_local_radius"]))
    print("    sum of binomial tail allowances <", upper_decimal(mass_rec["analytic_tail_upper"], 30))
    print("  overlap lower expression Z_* (order %d)" % overlap_rec["order"], enclosure(overlap))
    print("    signed remainder E_{-,1} <", upper_decimal(overlap_rec["signed_tail_upper"], 30))
    print("  J_R  (compact Gaussian)          ", enclosure(jc))
    print("  J_C^* (lower bound for J_C)      ", enclosure(jd))
    print("  slope -log(pi) - 2 J_R + J_C^*   ", enclosure(slope))
    q0 = Q(tube_rec["relative_change"])
    print("  tube quantity q_0 =", q0, "<", upper_rational(q0))
    print("  log K_C  ", enclosure(logK))
    print("  sigma_C  ", enclosure(sigma_D))
    print("  mu = 2 exp(H/2 - ell)", enclosure(mu))
    print("  terms of M_*(theta_*):")
    for name, value in terms:
        print("    %-34s" % name, enclosure(value))
    print("  M_*(theta_*)            ", enclosure(Mstar))
    print("  M_*(theta_*) - 4*10^-9  ", enclosure(after))
    print("  M_*(0)                  ", enclosure(m_zero))
    print("  zero theta_0 of M_*     ", enclosure(theta_zero))


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
