#!/usr/bin/env python3
"""Proposition E (README Section 11a) over E_W' (dihedral_ceiling3.py): the same signed-kernel argument and checks as
signed.py, with F(sigma) = Y_W'(sigma) - Z_sel(sigma) - (census floors relative to E_W').  The L-values of orbits
10, 23, 24 and Y_E are those of hp/ (dafe.py with M = 999999, ye_hp.py); orbits 19, 20 and the 32 degree-8 functions
come from hp3/ (deg8/leval.py); the census bins are the ker-W' bins (binsBW3) of census_kv3.c / census_kv4.c.

Usage (SPACE = W3 for E_W', W4 for E_W'' = E_W' M_17, W4x = W4 with orbits 10, 23, 24 from hp3/ and the abscissae
of hp3/sigma_set3x.txt; see dihedral_ceiling3.py):
  signed3.py SPACE choose DELTA OUT_PARAMS PREFIX [PREFIX ...]     float LP over the abscissae of hp3/sigma_set3.txt
  signed3.py SPACE certify DELTA PARAMS PREFIX [PREFIX ...]        rigorous checks and the certified constant
"""
import contextlib
import io
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import signed as S  # noqa: E402
import dihedral_ceiling3 as DC3  # noqa: E402
from flint import arb  # noqa: E402

HP3 = HERE / "hp3"


def exact_part3(delta, sig):
    """E(sigma) = Y_W' - sel - sav - census_small - Z_sel(sigma): F(sigma) without the census bins."""
    with contextlib.redirect_stdout(io.StringIO()):
        DC3.main(delta, sig, str(S.sig_files(sig)), str(S.HP), str(HP3), [])
    c = DC3.main.components
    assert c["qmin_rest_upto_XA"] >= S.QMIN, c["qmin_rest_upto_XA"]
    return c["Y_W"] - c["sel"] - c["sav"] - c["census_small"] - S.zsel(S.A(sig))


S.exact_part = exact_part3
S.read_bins = DC3.read_bins3


def choose(delta, out, prefixes, margin=1e-6, xbig=2e6):
    ns = [int(v) for v in (HP3 / DC3.SPACE["sigma_set"]).read_text().split()]
    sigs = [Q(n + 1, n) for n in sorted(ns, reverse=True)]
    F, R = [], []
    for s, E in zip(sigs, S.exact_parts(delta, sigs)):
        F.append(float(E.mid()) - S.census_float(s, prefixes))
        R.append(max(float(E.rad()), 1e-10))   # floor: keeps the LP well conditioned (it penalizes sum |c|);
                                               # the certification uses the exact balls
    Br = float(S.B_r().mid())
    res = S.lp(F, R, sigs, Br, margin, xbig)
    assert res is not None, "LP failed"
    fun, c, b = res
    zs = float(S.zsel(arb(1)).mid())
    print(f"choose3: {len(sigs)} abscissae, LP value (rest + TV) {fun:.7e}, C ~ {zs + fun:.8f}, b = {b:.6e}, "
          f"sum|c| = {np.abs(c).sum():.2f}")
    params = {"sigmas": [str(s) for s in sigs],
              "c": [str(Q(float(v)).limit_denominator(10**14)) for v in c],
              "b": str(Q(float(b) * (1 + 1e-9) + 1e-12).limit_denominator(10**14)),
              "xbig": str(int(xbig)), "lp_value": fun}
    Path(out).write_text(json.dumps(params, indent=1))
    return params


if __name__ == "__main__":
    args = sys.argv[1:]
    if not args or args[0] not in DC3.SPACES:
        raise SystemExit(__doc__)
    DC3.SPACE = DC3.SPACES[args[0]]
    mode = args[1]
    if mode == "choose":
        choose(Q(args[2]), args[3], args[4:])
    elif mode == "certify":
        S.certify(Q(args[2]), json.loads(Path(args[3]).read_text()), args[4:])
    else:
        raise SystemExit(__doc__)
