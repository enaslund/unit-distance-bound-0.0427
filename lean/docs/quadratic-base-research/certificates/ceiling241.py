"""Analytic ceiling for the tower over B=Q(sqrt 241) (approach b).

C = Y_*(sigma) + eps*((ell - gamma - log 4pi)/4 + R),   sigma = 1+eps,
Y_*(sigma) = (1/512) log zeta_{E_B}(sigma) - [excess of E_B over K at selected primes]
             - [census saving at primes with f_min = 4, N <= X'].
All subtracted terms are nonnegative and computed with outward-rounded Arb balls.
"""
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
import env241  # noqa: E402,F401
from flint import arb, ctx  # noqa: E402
from census241 import primes_upto, legendre, sqrtmod, KB, NORMS  # noqa: E402
from interval241 import logderiv_tail_bound  # noqa: E402

ctx.prec = 200
SQINR = [int(x) for x in open(HERE / "sqinR.txt").read().split()]


def a(q, s):
    """-log(1 - q^-s) as an arb ball."""
    return -(1 - arb(q) ** (-s)).log()


def census_saving_and_R(s, X):
    sav = arb(0)
    Rsum = arb(0)
    for p in primes_upto(X):
        if p in (2, 3, 5, 7, 29):
            continue
        if p == 241:
            places = [(241, sum((1 << i) for i, (aa, b, den) in enumerate(KB)
                                 if legendre((aa * pow(den, -1, 241)) % 241, 241) == -1))]
        elif legendre(241, p) == 1:
            r = sqrtmod(241, p)
            places = []
            for rr in (r, p - r):
                c = 0
                for i, (aa, b, den) in enumerate(KB):
                    x = ((aa + b * rr) * pow(den, -1, p)) % p
                    if legendre(x, p) == -1:
                        c |= 1 << i
                places.append((p, c))
        else:
            if p * p > X:
                continue
            c = sum((1 << i) for i, nm in enumerate(NORMS) if legendre(nm, p) == -1)
            places = [(p * p, c)]
        for N, c in places:
            if c == 0:
                f0 = 1
            elif SQINR[c]:
                f0 = 2
            else:
                f0 = 4
                sav += a(N**2, s) / 4 - a(N**4, s) / 8
            Rsum += arb(N).log() / (2 * (arb(N) ** (2 * f0) - 1))
    # primes of B with norm n > X (split primes p > X, and inert p with p^2 > X): f0 >= 1 and at most
    # two primes of B have any given norm n. Bound sum_{n>X} log n/(n^2-1)
    # by (log X + 1)/(X*(1-X^-2)), with every operation performed in Arb.
    Rsum += logderiv_tail_bound(X)
    return sav, Rsum


def main(sigma, Y_E_lo, Y_E_hi, X=10**6):
    s = arb(sigma.numerator) / sigma.denominator
    eps = s - 1
    Y_E = arb(Y_E_lo).union(arb(Y_E_hi))
    # selected primes: E_B type vs K type (relative (e,f) over B; contribution a(N^f,s)/(2 e f))
    exc = arb(0)
    exc += 2 * (a(2**2, s) / (2 * 4 * 2) - a(2**4, s) / (2 * 8 * 4))       # two dyadic primes
    exc += 2 * (a(29**2, s) / (2 * 1 * 2) - a(29**4, s) / (2 * 1 * 4))    # two primes above 29
    exc += 1 * (a(49**2, s) / (2 * 1 * 2) - a(49**4, s) / (2 * 1 * 4))    # inert prime 7
    sav, Rrest = census_saving_and_R(s, X)
    Ystar = Y_E - exc - sav
    ell = arb(9) / 4 * arb(2).log() + (arb(3).log() + arb(5).log() + arb(241).log()) / 2
    gam = arb.const_euler()  # rigorous ball for the Euler-Mascheroni constant
    Bhalf = (ell - gam - (4 * arb.pi()).log()) / 4
    # R: selected primes exact (relative types), plus census remainder
    R_sel = (2 * arb(2).log() / (2 * 8 * (arb(2) ** (2 * 4) - 1))
             + 2 * arb(3).log() / (2 * 2 * (arb(3) ** (2 * 2) - 1))
             + 2 * arb(5).log() / (2 * 2 * (arb(5) ** (2 * 2) - 1))
             + 2 * arb(29).log() / (2 * (arb(29) ** 8 - 1))
             + arb(49).log() / (2 * (arb(49) ** 8 - 1)))
    R = R_sel + Rrest
    C = Ystar + eps * (Bhalf + R)
    Bsel = (2 * a(2**4, 1) / (2 * 8 * 4) + 2 * a(3**2, 1) / (2 * 2 * 2) + 2 * a(5**2, 1) / (2 * 2 * 2)
            + 2 * a(29**4, 1) / (2 * 4) + a(49**4, 1) / (2 * 4))
    out = {"sigma": str(sigma), "Y_E": str(Y_E), "selected_excess": str(exc), "census_saving": str(sav),
           "Y_star": str(Ystar), "B_half": str(Bhalf), "R": str(R), "C": str(C), "C_upper": str(C.upper()),
           "B_sel(1)": str(Bsel), "C_minus_Bsel": str(C - Bsel)}
    print(json.dumps(out, indent=1))
    return C


if __name__ == "__main__":
    d = json.load(open(sys.argv[1]))
    lo, hi = d["normalized_log_zeta_EB"]
    main(Q(d["sigma"]), lo, hi)
