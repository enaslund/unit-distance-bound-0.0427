"""Rigorous values of log zeta_{E_B}(sigma)/512 for the genus field E_B of the tower over B=Q(sqrt 241).

Uses the manuscript's certified degree-two AFE kernels (nonpositive-afe.py) with root number 1
(each L(s,chi_e) = zeta_{B(sqrt alpha_e)}/zeta_B), and zeta_B = zeta * L(chi_241) via Hurwitz zeta.
Output: JSON-number endpoints rounded outward for the factors, and Arb
midpoint--radius strings for the normalized logarithm.
"""
import importlib.util
import json
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

import env241  # noqa: E402
from flint import arb, acb, ctx  # noqa: E402
from interval241 import outward_float_bounds  # noqa: E402

npafe = env241.nonpositive_afe()


def legendre241(a):
    a %= 241
    if a == 0:
        return 0
    return 1 if pow(a, 120, 241) == 1 else -1


def zeta_B(s):
    L = sum((legendre241(a) * s.zeta(arb(a) / 241) for a in range(1, 241)), arb(0)) / arb(241) ** s
    return s.zeta() * L, L


def main(sigma_q=Q(301, 300), rows_path="lrows241.json", out="afe241.json", degree=20):
    ctx.prec = 256
    s = npafe.rational(sigma_q)
    rows = json.load(open(rows_path))["rows"]
    kernels = {}
    total = arb(0)
    recs = []
    t0 = time.monotonic()
    zB, L241 = zeta_B(s)
    assert zB > 0
    total += zB.log()
    for row in rows:
        kind = row["kind"]
        if kind not in kernels:
            kernels[kind] = npafe.SplitKernels(s, kind, degree)
        result, A, B, err = npafe.evaluate(row, kernels[kind])
        # root number +1:  L = A + B, with each side carrying error <= err
        Lval = A.real + B.real
        Lball = Lval + arb(0, 2 * err.upper())
        assert Lball > 0, (row["label"], Lball)
        total += Lball.log()
        recs.append({"label": row["label"], "kind": kind, "conductor": row["conductor"],
                     "L": outward_float_bounds(Lball),
                     "imag_check": outward_float_bounds(abs(A.imag) + abs(B.imag))[1]})
    Y = total / 512
    res = {"sigma": str(sigma_q), "zeta_B": outward_float_bounds(zB),
           "L_chi241": outward_float_bounds(L241),
           "normalized_log_zeta_EB": [str(Y.lower()), str(Y.upper())],
           "rows": recs, "seconds": time.monotonic() - t0}
    json.dump(res, open(out, "w"), indent=1)
    print("sigma", sigma_q, "Y_E =", Y, "seconds", res["seconds"])
    return Y


if __name__ == "__main__":
    sq = Q(sys.argv[1]) if len(sys.argv) > 1 else Q(301, 300)
    main(sq, out=f"afe241_{str(sq).replace('/', '_')}.json")
