#!/usr/bin/env python3
"""Certified enclosures of L_w(sigma), sigma = 301/300, for the 64 twists of one D4 field.

Uses the certified degree-four kernels of the 1.0418235 archive (nonpositive-afe.py, kind 'quartic',
gamma_R(s)^2 gamma_R(s+1)^2 = gamma_C(s)^2).  L_w = zeta(K_w)/zeta(Bc) is a quotient of Dedekind zeta
functions, so its completed function satisfies Lambda(s) = Lambda(1-s): root number +1, L = A + B.
Usage: dafe.py ORBIT [SIGMA [OUTFILE [M]]]   (writes dafe_orb<ORBIT>.json, or dafe_orb<ORBIT>_<p>_<q>.json for
SIGMA = p/q != 301/300, or OUTFILE; M = AFE length for every twist, default floor(4 sqrt Q) + 1, M < 10^6)
"""
import json
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent.parent / "0.04273/certificates"))
sys.path.insert(0, str(HERE))
import env241  # noqa: E402
from flint import arb, ctx  # noqa: E402
import dcoeffs as DC  # noqa: E402

npafe = env241.nonpositive_afe()


def run(orbit, sigma=Q(301, 300), outfile=None, M=None):
    ctx.prec = 256
    data = DC.load(orbit)
    s = npafe.rational(sigma)
    kern = npafe.SplitKernels(s, "quartic", 20)
    spf = DC.spf_sieve(10**6 - 1)          # M (the AFE length, if given) must stay below 10^6, see dcoeffs.py
    res = []
    for k, tw in enumerate(data["twists"]):
        t0 = time.time()
        Qc, N, a = DC.coefficients(data, tw, spf, M=M)
        row = {"kind": "quartic", "conductor": Qc, "N": N, "coefficients": a, "label": f"orbit {orbit} w={tw['w']}"}
        result, A, B, err = npafe.evaluate(row, kern)
        L = A.real + B.real + arb(0, 2 * err.upper())
        assert L > 0 and abs(A.imag).upper() == 0 and abs(B.imag).upper() == 0
        res.append({"k": k, "w": tw["w"], "sigma": str(sigma), "Q": Qc, "N": N, "L": [str(L.lower()), str(L.upper())],
                    "err": float(err.upper()), "seconds": round(time.time() - t0, 1)})
    name = f"dafe_orb{orbit}.json" if sigma == Q(301, 300) else f"dafe_orb{orbit}_{sigma.numerator}_{sigma.denominator}.json"
    (HERE / (outfile or name)).write_text(json.dumps(res, indent=1) + "\n")
    print(f"dafe: orbit {orbit}: 64 twists, max err {max(r['err'] for r in res):.3e}")
    return res


if __name__ == "__main__":
    run(int(sys.argv[1]), Q(sys.argv[2]) if len(sys.argv) > 2 else Q(301, 300), sys.argv[3] if len(sys.argv) > 3 else None,
        int(sys.argv[4]) if len(sys.argv) > 4 else None)
