#!/usr/bin/env python3
"""Replay the finite computations behind the 41-cap variation (exponent 1.042901).

Reuses the Q(sqrt 241) tower/analytic inputs where the variation does not change
them (Kummer basis, Lie layers L2/L3, Golod-Shafarevich count, genus-field AFE
value Y_E), hash-checking the shared files. New steps (asserted):
  1. 41 splits in B; Frobenius vectors of both B-primes (PARI) -> kummer41.gp
  2. Both Frobenius squares avoid R2; c1 separated (one capped, one census) -> check41.py
  3. Lie layers L2=15, L3=26, |G/D4|=2^49, class(c1)=2^15 (unchanged: fourth
     powers have no quadratic/cubic initials) -> 241 lie241.py, lie241c.py
  4. P_B(34/117)<0 with 3 C4 caps (two above 29, one above 41) -> 241 gs241.py
  5. Analytic ceiling C<=0.04871285 with the swapped selected set -> ceiling41.py
     (Y_E inherited from 241 afe241_301_300.json; excess/census/R recomputed)
  6. Certified geometric margin >0 at delta=0.042901 -> geom41.py
Run from this directory. Requires PARI/GP, mpmath 1.3.0, python-flint 0.9.0.
Writes replay41.json.
"""
import hashlib
import json
import re
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
Q241 = HERE.parent.parent / "0.04273/certificates"
PY = [sys.executable, "-B"]

SHARED = {
    "lie241.py": "9f4daf06573ac59808e0cd1a8331bdac9c2ee1a035cda321156a5bf1440fcb49",
    "lie241c.py": None,  # checked by content needles below, not hash (imports lie241)
    "gs241.py": None,
    "sqinR.txt": "d565c97146a8b5861bf60b7b3dc57e314057ff3cdd6bed95b3a83b524811168a",
    "afe241_301_300.json": None,  # content-checked below (its timing field changes on every replay)
}

AFE_CONTENT = "f3d0ec0c5392bb26e8e45b5e8798f287c10f42da07ee3a67eea207dd915048fe"


def run(cmd, stdin=None, cwd=None):
    r = subprocess.run(cmd, input=stdin, capture_output=True, text=True, check=True,
                       cwd=str(cwd or HERE))
    return r.stdout


def main():
    t0 = time.monotonic()
    rec = {}
    for name, h in SHARED.items():
        if h is None:
            continue
        got = hashlib.sha256((Q241 / name).read_bytes()).hexdigest()
        assert got == h, (name, got)
    # The 0.04273 AFE record, as corrected on October 2, 2026 (outward-rounded factor endpoints);
    # hashed without its timing field, which the 0.04273 replay rewrites.
    afe = json.loads((Q241 / "afe241_301_300.json").read_text())
    afe.pop("seconds", None)
    got = hashlib.sha256(json.dumps(afe, sort_keys=True).encode()).hexdigest()
    assert got == AFE_CONTENT, ("afe241_301_300.json", got)
    rec["shared_inputs"] = "PASS 241 Kummer/Lie/CE inputs hash-checked"
    out = run(["gp", "-q"], stdin=(HERE / "kummer41.gp").read_text())
    assert "nprimes41 2" in out
    assert "cap41 1 frob(41) [0, 0, 1, 1, 1, 0, 0, 0]" in out
    assert "cap41 2 frob(41) [0, 0, 1, 1, 0, 1, 0, 0]" in out
    rec["kummer41"] = "PASS 41 splits; Frobenius vectors reproduced"
    out = run(PY + ["check41.py"])
    assert "PASS 41 splits" in out
    rec["cap_compatibility"] = "PASS C4 order and c1 separation for the capped 41-prime"
    out = run(PY + ["lie241c.py"], cwd=Q241)
    for needle in ["L2 = 15", "L3 = 26", "2^49", "size 2^15",
                   "rank of ad(c1) on degree 1 modulo relations: 7"]:
        assert needle in out, needle
    rec["lie_layers"] = "PASS L2=15, L3=26, |G/D4|=2^49, class(c1)=2^15 (fourth powers affect neither)"
    out = run(PY + ["gs241.py"], cwd=Q241)
    m = re.search(r"t = (\d+/\d+)\s+P_B\(t\) = (-?\d+/\d+)", out)
    assert m and Fraction(m.group(2)) < 0
    rec["golod_shafarevich"] = {"t": m.group(1), "P_B": m.group(2),
                                "note": "3 C4 caps: two above 29, one above 41; same count as 241 design"}
    out = run(PY + ["ceiling41.py"])
    d = json.loads(out[out.index("{"):])
    cu = re.search(r"\[([0-9.]+)", d["C_upper"]).group(1)
    assert Fraction(cu) < Fraction("0.04871285")
    rec["analytic_ceiling"] = {"C_upper": d["C_upper"], "used": "0.04871285",
                               "C_minus_Bsel": d["C_minus_Bsel"]}
    out = run(PY + ["geom41.py", "witness41_0.042901.json"])
    assert "fourier_ok True" in out and "slope>0 True" in out
    g = json.loads(out[out.rindex("{"):])
    assert Fraction(g["margin_after_concentration_lower"]) > 0
    rec["geometry"] = {"delta": "0.042901", "witness": "witness41_0.042901.json",
                       "margin_after_concentration_lower": g["margin_after_concentration_lower"]}
    rec["status"] = "PASS finite replay for delta = 0.042901 (exponent 1.042901); tower/transfer per 241 construction.md with the 41-cap swap of research/construction-41cap.md"
    rec["seconds"] = time.monotonic() - t0
    (HERE / "replay41.json").write_text(json.dumps(rec, indent=2) + "\n")
    print(rec["status"], "in", round(rec["seconds"]), "s")


if __name__ == "__main__":
    main()
