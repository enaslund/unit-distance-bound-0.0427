#!/usr/bin/env python3
"""Rigorous upper bound for the left side of hypothesis H of ChallengeZeta241.lean.

H:  log ζ_E(1+ε)/512 + ε((ℓ − γ − log 4π)/4 − (ζ_E'/ζ_E)(2)/512) < 852/10000,
ε = 1/300, ℓ = (9/4) log 2 + (1/2) log 3615, E = Q(√241, √α) the genus field
(degree 512, Kummer basis α of kummer241.gp).

* (1/512) log ζ_E(301/300): the rigorous AFE enclosure afe241_301_300.json.
* −(ζ_E'/ζ_E)(2)/512 = Σ_𝔭 log N𝔭 / (2 e(N𝔭^{2f} − 1)) over primes 𝔭 of B, with
  (e, f) the relative ramification index and residue degree of 𝔭 in E/B:
  (4,2) above 2, (2,2) above 3 and 5, and for the other primes f = 1 or 2
  according as all eight radicands are squares modulo 𝔭 (e = 1). Primes of
  norm ≤ X are summed exactly (Arb balls); the rest is bounded by
  Σ_{n>X} log n/(n²−1) ≤ (log X + 1)/X, since at most two primes of B have a
  given norm and each term is at most log N/(2(N²−1)).
All quantities are Arb balls; the printed bound is an upper endpoint.
"""
import json
import math
from pathlib import Path

import env241  # noqa: F401  (path set-up, PYLIB)
from flint import arb, ctx
from census241 import primes_upto, legendre, sqrtmod, KB, NORMS

ctx.prec = 200
HERE = Path(__file__).resolve().parent


def lg(x):
    return arb(x).log()


def logderiv_sum(X):
    total = arb(0)
    # selected primes of B, relative E-types
    total += 2 * lg(2) / (2 * 4 * (arb(2) ** 4 - 1))
    total += 2 * lg(3) / (2 * 2 * (arb(3) ** 4 - 1))
    total += 2 * lg(5) / (2 * 2 * (arb(5) ** 4 - 1))
    for p in primes_upto(X):
        if p in (2, 3, 5):
            continue
        if p == 241:
            c = sum(1 << i for i, (a, b, d) in enumerate(KB) if legendre((a * pow(d, -1, 241)) % 241, 241) == -1)
            places = [(241, c)]
        elif legendre(241, p) == 1:
            r = sqrtmod(241, p)
            places = []
            for rr in (r, p - r):
                c = 0
                for i, (a, b, d) in enumerate(KB):
                    if legendre(((a + b * rr) * pow(d, -1, p)) % p, p) == -1:
                        c |= 1 << i
                places.append((p, c))
        else:
            if p * p > X:
                continue
            c = sum(1 << i for i, nm in enumerate(NORMS) if legendre(nm, p) == -1)
            places = [(p * p, c)]
        for N, c in places:
            f = 1 if c == 0 else 2
            total += lg(N) / (2 * (arb(N) ** (2 * f) - 1))
    tail = arb((math.log(X) + 1) / X) * (1 + arb(1) / 10**6)
    return total + tail


def main(X=10**6):
    ye = json.load(open(HERE / "afe241_301_300.json"))
    lo, hi = ye["normalized_log_zeta_EB"]
    eps = arb(1) / 300
    ell = arb(9) / 4 * lg(2) + lg(3615) / 2
    bhalf = (ell - arb.const_euler() - (4 * arb.pi()).log()) / 4
    R = logderiv_sum(X)
    lhs_hi = arb(hi) + eps * (bhalf + R)
    ceiling = arb(852) / 10000
    out = {
        "normalized_log_zeta_E_upper": hi,
        "B_half": str(bhalf),
        "minus_logderiv_over_512_upper": str(R.upper()),
        "lhs_upper": str(lhs_hi.upper()),
        "ceiling": "852/10000",
        "slack_lower": str((ceiling - lhs_hi).lower()),
        "holds": bool((ceiling - lhs_hi).lower() > 0),
        "X": X,
    }
    (HERE / "h241_receipt.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
