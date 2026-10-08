"""Analytic ceiling for the 41-cap variation (tower over B=Q(sqrt 241)).

Same formula as ceiling241.py:
  C = Y_*(sigma) + eps*((ell - gamma - log 4pi)/4 + R),
but the selected set swaps the inert prime 7 (relative f=4, absolute f=8)
for a single B-prime above the split prime 41 (relative f=4, absolute f=4,
effective absolute (e,f)=(2,4) since only half the F-primes above 41 are used).
The other B-prime above 41 and the inert prime 7 are unselected (census
f_min=4 for both, since their Frobenius squares avoid R2; see check41.py).

Y_E (genus-field zeta) is inherited unchanged from the 241 certificate
(afe241_301_300.json, hash-checked): the genus field E_B depends only on the
Kummer group V, not on the caps. The capped-41 excess and the census/census-R
are recomputed here with outward-rounded Arb balls.
"""
import hashlib
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
Q241 = HERE.parent.parent / "0.04273/certificates"
sys.path.insert(0, str(Q241))
import env241  # noqa: E402,F401  (path setup for flint import below)
from flint import arb, ctx  # noqa: E402
from census241 import primes_upto, legendre, sqrtmod, KB, NORMS  # noqa: E402
from interval241 import logderiv_tail_bound  # noqa: E402

ctx.prec = 200

EXPECTED = {
    "sqinR.txt": "d565c97146a8b5861bf60b7b3dc57e314057ff3cdd6bed95b3a83b524811168a",
    # the October 2, 2026 corrected record, hashed without its timing field (rewritten by every replay)
    "afe241_301_300.json": "f3d0ec0c5392bb26e8e45b5e8798f287c10f42da07ee3a67eea207dd915048fe",
}


def checked(name):
    p = Q241 / name
    if name.endswith(".json"):
        data = json.loads(p.read_text())
        data.pop("seconds", None)
        h = hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest()
    else:
        h = hashlib.sha256(p.read_bytes()).hexdigest()
    assert h == EXPECTED[name], (name, h)
    return p


SQINR = [int(x) for x in checked("sqinR.txt").read_text().split()]


def capped41_code():
    r = sqrtmod(241, 41)
    c = 0
    for i, (aa, b, den) in enumerate(KB):
        x = ((aa + b * r) * pow(den, -1, 41)) % 41
        if legendre(x, 41) == -1:
            c |= 1 << i
    return c


CAPPED41 = capped41_code()
assert CAPPED41 == 28, CAPPED41  # vector [0,0,1,1,1,0,0,0], P41[1]


def a(q, s):
    return -(1 - arb(q) ** (-s)).log()


def census_saving_and_R(s, X):
    sav = arb(0)
    Rsum = arb(0)
    for p in primes_upto(X):
        if p in (2, 3, 5, 29):
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
                if p == 41 and c == CAPPED41:
                    continue  # capped B-prime: in selected excess, not census
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
    # sum_{n>X} log n/(n^2-1) <= (log X + 1)/(X (1 - X^-2)), every operation in Arb
    Rsum += logderiv_tail_bound(int(X))
    return sav, Rsum


def main(sigma, Y_E_lo, Y_E_hi, X=10**6):
    s = arb(sigma.numerator) / sigma.denominator
    eps = s - 1
    Y_E = arb(Y_E_lo).union(arb(Y_E_hi))
    exc = arb(0)
    exc += 2 * (a(2**2, s) / (2 * 4 * 2) - a(2**4, s) / (2 * 8 * 4))
    exc += 2 * (a(29**2, s) / (2 * 1 * 2) - a(29**4, s) / (2 * 1 * 4))
    exc += 1 * (a(41**2, s) / (2 * 1 * 2) - a(41**4, s) / (2 * 1 * 4))  # single capped B-prime
    sav, Rrest = census_saving_and_R(s, X)
    Ystar = Y_E - exc - sav
    ell = arb(9) / 4 * arb(2).log() + (arb(3).log() + arb(5).log() + arb(241).log()) / 2
    gam = arb.const_euler()
    Bhalf = (ell - gam - (4 * arb.pi()).log()) / 4
    R_sel = (2 * arb(2).log() / (2 * 8 * (arb(2) ** (2 * 4) - 1))
             + 2 * arb(3).log() / (2 * 2 * (arb(3) ** (2 * 2) - 1))
             + 2 * arb(5).log() / (2 * 2 * (arb(5) ** (2 * 2) - 1))
             + 2 * arb(29).log() / (2 * (arb(29) ** 8 - 1))
             + 1 * arb(41).log() / (2 * (arb(41) ** 8 - 1)))
    R = R_sel + Rrest
    C = Ystar + eps * (Bhalf + R)
    Bsel = (2 * a(2**4, 1) / (2 * 8 * 4) + 2 * a(3**2, 1) / (2 * 2 * 2) + 2 * a(5**2, 1) / (2 * 2 * 2)
            + 2 * a(29**4, 1) / (2 * 4) + 1 * a(41**4, 1) / (2 * 4))
    out = {"sigma": str(sigma), "Y_E": str(Y_E), "selected_excess": str(exc), "census_saving": str(sav),
           "Y_star": str(Ystar), "B_half": str(Bhalf), "R": str(R), "C": str(C), "C_upper": str(C.upper()),
           "B_sel(1)": str(Bsel), "C_minus_Bsel": str(C - Bsel)}
    print(json.dumps(out, indent=1))
    return C


if __name__ == "__main__":
    d = json.loads(checked("afe241_301_300.json").read_text())
    lo, hi = d["normalized_log_zeta_EB"]
    main(Q(d["sigma"]), lo, hi)
