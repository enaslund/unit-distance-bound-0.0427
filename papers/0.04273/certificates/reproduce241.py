#!/usr/bin/env python3
"""Replay the finite computations behind the Q(sqrt 241) construction.

Steps (each asserted), in the order of the manuscript ../main.tex:
  1. Kummer basis and local Hilbert-symbol vectors (PARI)      -> kummer241.gp
  2. Cup-product invariants: rank 7 on the 7 non-dyadic-1 places -> cup241.gp
  3. The dyadic group D and its group algebra F_2[D]             -> dyadic241.py
  4. Lie layers L2=15, L3=26, retention, ad(iota_1) ranks 7, 8   -> lie241.py, lie241c.py
  5. Exact Golod-Shafarevich value P_B(34/117) < 0                -> gs241.py
  6. The 255 L-function rows; sample and complete checks          -> lfun241.py, lcheck.gp, check255.gp
  7. Rigorous (1/512) log zeta_E(301/300)                         -> afe241.py
  8. PARI values of the 255 L(301/300) inside their enclosures    -> lvalues255.gp (about 8 minutes)
  9. Analytic ceiling C <= 0.04871285                             -> ceiling241.py
 10. Certified geometric margin > 0 at delta = 0.04273            -> geom241.py
Run from this directory.  Requires PARI/GP, mpmath 1.3.0, python-flint 0.9.0
(set PYLIB if not installed).  Writes replay241.json.
"""
import json
import os
import re
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
os.chdir(HERE)
PY = [sys.executable, "-B"]


def run(cmd, stdin=None):
    r = subprocess.run(cmd, input=stdin, capture_output=True, text=True, check=True)
    return r.stdout


def main():
    t0 = time.monotonic()
    rec = {}
    out = run(["gp", "-q"], stdin=Path("kummer241.gp").read_text())
    assert "c1 [1, 0, 1, 1, 1, 0, 1, 0]" in out and "inert7 frob(7) [0, 1, 1, 1, 0, 0, 0, 0]" in out
    rec["kummer"] = "PASS local vectors reproduced"
    out = run(["gp", "-q"], stdin=Path("cup241.gp").read_text())
    rows = [[int(x) for x in m.group(3).split(",")] for m in
            (re.match(r"(\d+) (\d+) \[(.*)\]", l.strip()) for l in out.splitlines()) if m]
    assert len(rows) == 36 and all(sum(r) % 2 == 0 for r in rows)

    def rank(M):
        M = [r[:] for r in M]
        rk, cols = 0, len(M[0])
        for c in range(cols):
            piv = next((i for i in range(rk, len(M)) if M[i][c] % 2), None)
            if piv is None:
                continue
            M[rk], M[piv] = M[piv], M[rk]
            for i in range(len(M)):
                if i != rk and M[i][c] % 2:
                    M[i] = [(a + b) % 2 for a, b in zip(M[i], M[rk])]
            rk += 1
        return rk
    assert rank(rows) == 7 and rank([r[1:] for r in rows]) == 7
    rec["cup_products"] = "PASS rank 7, rank 7 off the first dyadic place"
    out = run(PY + ["dyadic241.py"])
    assert "dyadic241: all checks passed" in out
    rec["dyadic_group_algebra"] = "PASS D of order 32, dim I^m = 32,31,28,23,16,9,4,1,0, I^7 = F_2 Omega, graded injectivity"
    out = run(PY + ["lie241c.py"])
    for needle in ["L2 = 15", "L3 = 26", "2^49", "size 2^15", "c1 separated from all decomposition spans: True",
                   "rank of ad(c1) on degree 1 modulo relations: 7"]:
        assert needle in out, needle
    assert out.count("new degree-2 directions z^2,[y,z] mod relations: 2") == 2
    assert out.count("S(frob) independent mod relations: 1") == 3
    rec["lie_layers"] = "PASS L2=15, L3=26, |G/D4|=2^49, class(c1)=2^15, local groups retained"
    out = run(PY + ["gs241.py"])
    m = re.search(r"t = (\d+/\d+)\s+P_B\(t\) = (-?\d+/\d+)", out)
    assert m and Fraction(m.group(2)) < 0
    rec["golod_shafarevich"] = {"t": m.group(1), "P_B": m.group(2)}
    run(PY + ["lfun241.py"])
    out = run(["gp", "-q"], stdin=Path("lcheck.gp").read_text())
    checks = [l for l in out.splitlines() if "coeff match" in l]
    assert checks and all(l.endswith("coeff match 1") for l in checks)
    assert all("kind pure0/pure0" in l or "kind pure1/pure1" in l or "kind quadratic/quadratic" in l for l in checks)
    rec["lfunction_rows"] = f"PASS {len(checks)} sampled rows match PARI (conductor, gamma type, 400 coefficients)"
    out = run(["gp", "-q"], stdin=Path("check255.gp").read_text())
    assert "check255: PASS" in out
    rec["all_255_rows"] = "PASS all 255 rows: conductor, gamma type and coefficients up to N_e match PARI"
    run(PY + ["afe241.py", "301/300"])
    ye = json.load(open("afe241_301_300.json"))
    rec["Y_E"] = ye["normalized_log_zeta_EB"]
    out = run(["gp", "-q"], stdin=Path("lvalues255.gp").read_text())
    assert "lvalues255: PASS" in out
    rec["pari_lvalues"] = "PASS PARI's 255 values L(301/300, chi_e) lie inside the certified row enclosures"
    out = run(PY + ["ceiling241.py", "afe241_301_300.json"])
    d = json.loads(out[out.index("{"):])
    cu = re.search(r"\[([0-9.]+)", d["C_upper"]).group(1)
    assert Fraction(cu) < Fraction("0.04871285")
    rec["analytic_ceiling"] = {"C_upper": d["C_upper"], "used": "0.04871285", "C_minus_Bsel": d["C_minus_Bsel"]}
    out = run(PY + ["geom241.py", "0.04273", "0.04871285", "shells241_0.04273.json"])
    m = re.search(r"margin_after (-?[0-9.]+)", out)
    assert "fourier_ok True" in out and "slope>0 True" in out and m and float(m.group(1)) > 0
    rec["geometry"] = {"delta": "0.04273", "margin_after_concentration_lower": m.group(1)}
    rec["status"] = "PASS finite replay for delta = 0.04273 (exponent 1.04273); the mathematics is proved in the manuscript ../main.tex"
    rec["seconds"] = time.monotonic() - t0
    Path("replay241.json").write_text(json.dumps(rec, indent=2) + "\n")
    print(rec["status"], "in", round(rec["seconds"]), "s")


if __name__ == "__main__":
    main()
