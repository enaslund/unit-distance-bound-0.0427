#!/usr/bin/env python3
"""Replay for the census refinement of the 41-cap tower over B = Q(sqrt 241) (README Sections 4-9).

Steps (asserted):
  1. base ceiling C (ceiling41.py) below the witness constant, at the witness sigma;
  2. the fifteen D4 functionals kill R_2 and have rank 15 (d4fields.py; regenerates d4fields15.h);
  3. each beta_i is an S-unit with the D4 pattern and F0_i(sqrt beta_i)/F0_i unramified outside S
     (vd4.gp, an independent construction of F0_i);
  4. the Legendre test agrees with root counts of the degree-16 fields (rootcheck.py);
  5. both census programs (census_d3.c, census_d3w.c) reproduce, prime by prime and field by field,
     the Python test on all vector-0 primes of norm 6e4..1.2e7; the stored census bins hash-check
     (with --rerun, the census is recomputed and compared);
  6. certified gain (census_gain.py) at least the witness value;
  7. certified margin > 0 at delta with C_eff = C - gain, Fourier condition and positive slope.
Run from this directory; needs gcc with OpenMP, PARI/GP, mpmath 1.3.0, python-flint 0.9.0.
"""
import gzip
import hashlib
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


def run(cmd, cwd=HERE, stdin=None):
    return subprocess.run(cmd, capture_output=True, text=True, check=True, cwd=str(cwd), input=stdin).stdout


def bins_sha(prefix):
    p = HERE / (prefix + ".bins")
    data = p.read_bytes() if p.exists() else gzip.open(str(HERE / (prefix + ".bins.gz")), "rb").read()
    return hashlib.sha256(data).hexdigest()


def main(witness, rerun=False):
    t0 = time.monotonic()
    w = json.loads((HERE / witness).read_text())
    cen = w["census"]
    rec = {"witness": witness, "delta": w["delta"]}
    # 1
    out = run(PY + ["ceiling41.py"], P41)
    d = json.loads(out[out.index("{"):])
    assert d["sigma"] == cen["sigma"], (d["sigma"], cen["sigma"])
    cu = re.search(r"\[([0-9.]+)", d["C_upper"]).group(1)
    assert Q(cu) < Q(w["C"])
    rec["base_ceiling"] = {"C_upper": d["C_upper"], "used": w["C"], "sigma": d["sigma"]}
    # the floors f0 of adaptive41.py must be those of Y_* in ceiling41.py (same P_4 census range)
    import inspect
    sys.path.insert(0, str(P41))
    sys.path.insert(0, str(HERE))
    import ceiling41
    import adaptive41
    assert inspect.signature(ceiling41.main).parameters["X"].default == adaptive41.CENSUS_X
    assert ceiling41.CAPPED41 == adaptive41.CAPPED41
    # 2
    out = run(PY + ["d4search.py"])
    assert "D4 classes (distinct functionals): 27  rank: 15" in out and "census fields are among them" in out
    out = run(PY + ["d4fields.py"])
    assert "rank 15" in out
    rec["d4_functionals"] = "PASS 15 functionals vanish on R_2, rank 15"
    # 3
    out = run(["gp", "-q", "-s", "4000000000", "vd4.gp"], stdin="")
    assert "vd4: PASS all 15 fields" in out, out[-2000:]
    rec["d4_fields"] = "PASS S-units, D4 pattern, unramified outside S (15 fields)"
    # 4
    out = run(PY + ["rootcheck.py"])
    assert "rootcheck: PASS 80" in out
    rec["root_counts"] = "PASS 80 primes x 15 fields"
    # 5
    sys.path.insert(0, str(HERE))
    import rootcheck
    X = 12 * 10**6
    s = bytearray([1]) * (X + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(X**0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    from census241 import legendre, sqrtmod
    ref = []
    for p in range(60001, X + 1):
        if s[p] and p % 120 in (1, 49) and legendre(241, p) == 1:
            r = sqrtmod(241, p)
            for rr in (r, p - r):
                b = rootcheck.bits(p, rr)
                if b is not None:
                    ref.append("%d %d %s" % (p, rr, "".join("1" if x == -1 else ("0" if x == 1 else "z") for x in b)))
    ref.sort(key=lambda t: (int(t.split()[0]), int(t.split()[1])))
    for prog in ("census_d3", "census_d3w"):
        run(["gcc", "-O3", "-fopenmp", "-o", prog, prog + ".c", "-lm"])
        run(["./" + prog, "6e4", "1.2e7", "4", "check_" + prog, "debug"])
        got = sorted((l.split(None, 1)[1].strip() for l in (HERE / ("check_" + prog + ".txt")).read_text().splitlines()
                      if l.startswith("bits")), key=lambda t: (int(t.split()[0]), int(t.split()[1])))
        assert got == ref, prog
    rec["census_programs"] = f"PASS census_d3 and census_d3w agree with Python on all {len(ref)} vector-0 primes of norm 6e4..1.2e7"
    for pre in cen["prefixes"]:
        if rerun:
            txt = (HERE / (pre + ".txt")).read_text().splitlines()[-1]
            m = re.search(r"XLO (\d+) XHI (\d+)", txt)
            run(["./census_d3w", m.group(1), m.group(2), "12", pre + "_rerun"])
            assert hashlib.sha256((HERE / (pre + "_rerun.bins")).read_bytes()).hexdigest() == cen["sha256_bins"][pre]
        assert bins_sha(pre) == cen["sha256_bins"][pre], pre
    rec["census_data"] = "PASS stored bins hash-check" + (" and recomputed" if rerun else "")
    # 6
    out = run(PY + ["census_gain.py", w["delta"], cen["sigma"], str(cen["XA"])] + cen["prefixes"])
    g = json.loads(out[out.index("{"):])
    ball = g["gain_lower"].strip("[]").split()
    assert Q(ball[0]) - Q(ball[2]) >= Q(cen["gain_used"]), g["gain_lower"]
    rec["gain"] = {"gain_lower": g["gain_lower"], "used": cen["gain_used"], "small_counts": g["small_counts"],
                   "census": g["census"], "XC": g["XC"]}
    # 7
    C_eff = Q(w["C"]) - Q(cen["gain_used"])
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
    rec["status"] = f"PASS census replay for delta = {w['delta']} (exponent 1+delta)"
    rec["seconds"] = round(time.monotonic() - t0)
    (HERE / ("replay_" + w["delta"] + ".json")).write_text(json.dumps(rec, indent=1) + "\n")
    print(json.dumps(rec, indent=1))


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    main(args[0] if args else "witness_0.042965.json", rerun="--rerun" in sys.argv)
