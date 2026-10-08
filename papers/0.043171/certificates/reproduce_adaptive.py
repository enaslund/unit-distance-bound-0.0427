#!/usr/bin/env python3
"""Replay for the adaptive-census refinement of the 41-cap tower over B = Q(sqrt 241).

Steps (asserted):
  1. Base analytic ceiling C <= 0.04871285 for the 41-cap design -> ../../0.042901/certificates/ceiling41.py
  2. Adaptive census gain: certified lower bound for sum_p G(p) >= gain_used -> adaptive41.py
  3. Certified margin > 0 at delta (witness) with the effective constant C - gain_used,
     Fourier condition and positive theta-slope -> geom241.margin with the 41-cap EF table.
The mathematics of steps 2-3 is in ../README.md (Propositions A and B).
Requires PARI/GP (step 1 imports only Python), mpmath 1.3.0, python-flint 0.9.0.
"""
import json
import re
import subprocess
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
P41 = HERE.parent.parent / "0.042901/certificates"
P241 = HERE.parent.parent / "0.04273/certificates"
PY = [sys.executable, "-B"]


def run(cmd, cwd):
    return subprocess.run(cmd, capture_output=True, text=True, check=True, cwd=str(cwd)).stdout


def main(witness):
    t0 = time.monotonic()
    w = json.loads((HERE / witness).read_text())
    rec = {"witness": witness, "delta": w["delta"]}
    out = run(PY + ["ceiling41.py"], P41)
    d = json.loads(out[out.index("{"):])
    cu = re.search(r"\[([0-9.]+)", d["C_upper"]).group(1)
    assert Q(cu) < Q(w["C"]), (cu, w["C"])
    rec["base_ceiling"] = {"C_upper": d["C_upper"], "used": w["C"]}
    ad = w["adaptive"]
    out = run(PY + ["adaptive41.py", w["delta"], ad["sigma"], str(ad["X"])], HERE)
    g = json.loads(out[out.index("{"):])
    glo = re.search(r"\[([0-9.e-]+)", g["gain_lower"]).group(1)
    assert Q(g["gain_lower"].split()[0].lstrip("[")) - Q(g["gain_lower"].split()[2].rstrip("]")) >= Q(ad["gain_used"]), g["gain_lower"]
    rec["adaptive_gain"] = {"gain_lower": g["gain_lower"], "used": ad["gain_used"], "counts": g["counts"],
                            "largest_N_with_gain": g["largest_N_with_gain"]}
    C_eff = Q(w["C"]) - Q(ad["gain_used"])
    sys.path.insert(0, str(P41))
    sys.path.insert(0, str(P241))
    import env241  # noqa: F401
    import geom241
    from interval_core import lower
    from profile_certificate import interval_strings
    from mpmath import mp, iv
    geom241.EF = {2: (8, 4), 3: (2, 2), 5: (2, 2), 29: (1, 4), 41: (2, 4)}
    assert w["EF"] == {"2": [8, 4], "3": [2, 2], "5": [2, 2], "29": [1, 4], "41": [2, 4]}
    assert w["theta_min"] == "65535/131072"
    mp.dps = 80
    iv.dps = 80
    shells = {"ks": w["ks"], "finite_profiles": w["finite_profiles"]}
    after, fok, sok = geom241.margin(w["delta"], str(C_eff), shells, s=w["s"], a=w["a"],
                                     bern=[[Q(v) for v in row] for row in w["bernstein"]], verbose=False)
    assert fok and sok and lower(after) > 0
    rec["geometry"] = {"C_effective": str(C_eff), "margin_after_concentration_lower": interval_strings(after)[0][:22]}
    rec["status"] = f"PASS adaptive-census replay for delta = {w['delta']} (exponent 1+delta)"
    rec["seconds"] = round(time.monotonic() - t0)
    print(json.dumps(rec, indent=1))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "witness_0.042925.json")
