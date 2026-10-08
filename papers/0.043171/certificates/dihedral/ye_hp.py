#!/usr/bin/env python3
"""Y_E at sigma with a longer approximate functional equation (Proposition E needs small radii).

Same computation as afe241.py of the 0.04273 certificates (whose files are not modified): the rows of the 255
L-functions are built by lfun241.py's functions, but with N = floor(MULT sqrt q) + 1 for MULT = 8 instead of 4,
into hp_lrows241.json here; afe241.main then evaluates them.  The kernels need 2 pi MULT < 64.
Usage: ye_hp.py [--outdir DIR] SIGMA [SIGMA ...]      (writes DIR/afe241hp_<p>_<q>.json, default hp/)
"""
import json
import math
import os
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
P241 = HERE.parent.parent.parent / "0.04273/certificates"
MULT = 8
ROWS = HERE / "hp_lrows241.json"


def build_rows():
    cwd = os.getcwd()
    os.chdir(P241)
    sys.path.insert(0, str(P241))
    try:
        import lfun241 as LF
        _, cmax = max((LF.local_small(e) for e in range(1, 256)), key=lambda t: t[1])
        nmax_all = int(MULT * math.isqrt(LF.D * cmax)) + 2
        fv = LF.frob_vectors(nmax_all)
        rows = []
        for e in range(1, 256):
            _, cond = LF.local_small(e)
            q = LF.D * cond
            nmax = int(MULT * math.isqrt(q)) + 1
            rows.append({"label": f"e={e}", "kind": LF.kind_of(e), "conductor": q, "N": nmax,
                         "coefficients": LF.coefficients(e, nmax, fv)})
    finally:
        os.chdir(cwd)
    ROWS.write_text(json.dumps({"rows": rows}))
    print("ye_hp: rows with MULT", MULT, "max N", max(r["N"] for r in rows))


def main(sigmas, outdir=None):
    outdir = Path(outdir) if outdir else HERE / "hp"
    assert 2 * math.pi * MULT < 64
    if not ROWS.exists():
        build_rows()
    cwd = os.getcwd()
    os.chdir(P241)
    sys.path.insert(0, str(P241))
    try:
        import afe241
        for sq in sigmas:
            out = outdir / f"afe241hp_{sq.numerator}_{sq.denominator}.json"
            afe241.main(sq, rows_path=str(ROWS), out=str(out))
    finally:
        os.chdir(cwd)


if __name__ == "__main__":
    args = sys.argv[1:]
    od = None
    if args and args[0] == "--outdir":
        od, args = args[1], args[2:]
    main([Q(a) for a in args], od)
