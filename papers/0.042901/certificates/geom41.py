#!/usr/bin/env python3
"""Interval-arithmetic geometric margin for the 41-cap variation.

Same transfer as geom241.py (tower over B=Q(sqrt 241)), but the selected set
swaps the inert prime 7 (absolute (e,f)=(1,8)) for a single B-prime above the
split prime 41 (effective absolute (e,f)=(2,4): half the F-primes above 41,
those over the capped B-prime, carry windows with Q=41^4).

Inputs: witness JSON with delta, C, s, a, bernstein, ks, finite_profiles.
"""
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
Q241 = HERE.parent.parent / "0.04273/certificates"
sys.path.insert(0, str(Q241))
import env241  # noqa: E402,F401
import geom241  # noqa: E402
from profile_certificate import interval_strings  # noqa: E402
from interval_core import lower  # noqa: E402
from mpmath import mp, iv  # noqa: E402

geom241.EF = {2: (8, 4), 3: (2, 2), 5: (2, 2), 29: (1, 4), 41: (2, 4)}

EXPECTED_EF = {"2": [8, 4], "3": [2, 2], "5": [2, 2], "29": [1, 4], "41": [2, 4]}


def verify(witness_path):
    mp.dps = 80
    iv.dps = 80
    w = json.loads(Path(witness_path).read_text())
    assert w["EF"] == EXPECTED_EF, w.get("EF")
    assert w["theta_min"] == "65535/131072"
    shells = {"ks": w["ks"], "finite_profiles": w["finite_profiles"]}
    after, fok, sok = geom241.margin(
        w["delta"], w["C"], shells, s=w["s"], a=w["a"],
        bern=[[Q(v) for v in row] for row in w["bernstein"]], verbose=True)
    assert fok, "Fourier/period condition fails"
    assert sok, "theta-slope not positive"
    lo = interval_strings(after)[0]
    print("certified lower margin after concentration:", lo)
    assert lower(after) > 0, "nonpositive margin"
    return {"delta": w["delta"], "C": w["C"], "margin_after_concentration_lower": lo,
            "fourier_ok": fok, "slope_ok": sok}


if __name__ == "__main__":
    print(json.dumps(verify(sys.argv[1]), indent=1))
