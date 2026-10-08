#!/usr/bin/env python3
"""Replay for the dihedral refinement (README Sections 8-10): ceiling over E_W = E M_10 M_23 at the witness
abscissa, census and adaptive dichotomy relative to E_W, certified margin.

Steps (asserted; files that a step regenerates in place must come out byte-identical, else they are restored
and the replay fails):
  1. base ceiling (ceiling41.py at 301/300, for reference) and the genus-field value Y_E at the witness sigma
     recomputed by afe241.py (after lfun241.py) equal to the stored afe241_<p>_<q>.json;
  2. the 27 D4 classes and rank 15 (d4search.py), the 15 census fields (d4fields.py, vd4.gp, rootcheck.py);
  3. the plane W (plane.py) and its three D4 fields (vplane.gp);
  4. the exported L-function data (export.gp, which also asserts r1(K) = r1(Bc)) reproduce ddata_orb*.json;
  5. coefficients of all 192 twists agree with PARI's zeta quotients up to NCHK; PARI's lfun agrees with the
     certified values on two twists per family (dcheck.py, at the witness sigma);
  6. the certified L-values at the witness sigma (dafe.py) reproduce the stored enclosures;
  7. census_d3k.c reproduces the Python classification on norms 6e4..1.2e7; census_kw.c (prefixes kw*) reproduces
     all census_d3k.c outputs on three ranges, and census_kv.c (prefixes kv*, AVX-512 IFMA) those of census_kw.c; stored census data hash-check (--rerun recomputes the census:
     about 13 CPU-hours for k1e13, and with census_kw.c about 7 CPU-hours for kw4e13, more for larger ranges);
  8. dihedral_ceiling.py, and lptv.py when the witness asks for the refined TV step (Proposition D), or signed.py
     when it asks for the signed kernel (Proposition E; the long-AFE data in hp/ are hash-checked and recomputed at
     the extreme abscissae, at all of them with --full-lv), give C_eff at most the witness value;
  9. certified margin > 0 at delta with C_eff, Fourier condition, positive slope.
Run from this directory.  Needs gcc with OpenMP, PARI/GP, mpmath 1.3.0, python-flint 0.9.0.
Options: --quick (NCHK = 3000 instead of 20000), --rerun, --full-lv.
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
CERT = HERE.parent
P41 = CERT.parent.parent / "0.042901/certificates"
P241 = CERT.parent.parent / "0.04273/certificates"
PY = [sys.executable, "-B"]


def run(cmd, cwd=HERE, stdin=None):
    return subprocess.run(cmd, capture_output=True, text=True, check=True, cwd=str(cwd), input=stdin).stdout


def sha(path):
    p = Path(path)
    data = p.read_bytes() if p.exists() else gzip.open(str(p) + ".gz", "rb").read()
    return hashlib.sha256(data).hexdigest()


def ensure_raw(path):
    p = Path(path)
    if not p.exists():
        p.write_bytes(gzip.open(str(p) + ".gz", "rb").read())


class Unchanged:
    """Files that a step regenerates in place must come out byte-identical; otherwise they are restored and the
    replay fails."""
    def __init__(self, *paths):
        self.saved = {Path(p): Path(p).read_bytes() for p in paths if Path(p).exists()}

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        changed = [p for p, b in self.saved.items() if not p.exists() or p.read_bytes() != b]
        for p in changed:
            p.write_bytes(self.saved[p])
        assert not changed, ("regenerated files differ (restored)", [str(p) for p in changed])
        return False


def main(witness, rerun=False, nchk=20000, full_lv=False):
    t0 = time.monotonic()
    w = json.loads((HERE / witness).read_text())
    dih = w["dihedral"]
    sigma = dih["sigma"]
    sp, sq = sigma.split("/")
    rec = {"witness": witness, "delta": w["delta"], "sigma": sigma}
    # 1
    out = run(PY + ["ceiling41.py"], P41)
    rec["base_ceiling_C_upper_301_300"] = json.loads(out[out.index("{"):])["C_upper"]
    with Unchanged(P241 / "lrows241.json"):
        run(PY + ["lfun241.py"], P241)
    run(PY + ["afe241.py", sigma], P241)
    produced = P241 / f"afe241_{sp}_{sq}.json"
    new_ye = json.loads(produced.read_text())["normalized_log_zeta_EB"]
    old_ye = json.loads((HERE / dih["Y_E"]).read_text())["normalized_log_zeta_EB"]
    assert new_ye == old_ye, (new_ye, old_ye)
    if sigma != "301/300":
        produced.unlink()
    rec["Y_E"] = new_ye
    # 2
    for name, h in dih["sha256"].items():          # pinned files outside the census (e.g. ../d4fields15.h)
        if name.startswith("../"):
            assert sha(HERE / name) == h, name
    with Unchanged(CERT / "d4fields15.json", CERT / "d4fields15.h", CERT / "vd4_data.gp", CERT / "mtilde15.gp"):
        out = run(PY + ["d4search.py"], CERT)
        assert "D4 classes (distinct functionals): 27  rank: 15" in out
        out = run(PY + ["d4fields.py"], CERT)
        assert "rank 15" in out
        out = run(["gp", "-q", "-s", "4000000000", "vd4.gp"], CERT, stdin="")
        assert "vd4: PASS all 15 fields" in out
        out = run(PY + ["rootcheck.py"], CERT)
        assert "rootcheck: PASS 80" in out
    rec["d4_census_fields"] = "PASS 27 classes, rank 15; 15 census fields verified; root counts"
    # 3
    out = run(PY + ["plane.py"])
    assert "plane: PASS" in out
    out = run(["gp", "-q", "-s", "4000000000", "vplane.gp"], stdin="")
    assert "vplane: PASS orbits 10, 23, 24" in out
    rec["plane"] = "PASS psi_10 + psi_23 = psi_24, all of D4 type, maximal; fields of orbits 10, 23, 24 verified"
    # 4
    for o in dih["orbits"]:                    # regenerated into a separate file; the stored data are not moved
        name = f"ddata_orb{o}.json"
        assert sha(HERE / name) == dih["sha256"][name]
        new = f"replay_ddata_orb{o}.json"
        try:
            run(["gp", "-q", "-s", "4000000000"], stdin=f'ORB={o}; OUT="{new}"; read("export.gp");')
            assert sha(HERE / new) == dih["sha256"][name], o
        finally:
            (HERE / new).unlink(missing_ok=True)
    rec["export"] = "PASS export.gp reproduces ddata_orb10/23/24.json (r1(K) = r1(Bc) asserted)"
    with Unchanged(HERE / "inertv0.json"):
        out = run(PY + ["inertv0.py"])
    assert "in ker W at [2521]" in out
    rec["inert_vector0"] = out.strip().splitlines()[-1]
    # 5, 6
    for o in dih["orbits"]:
        stored_name = f"dafe_orb{o}_{sp}_{sq}.json"
        stored = json.loads((HERE / stored_name).read_text())
        tmp = f"replay_dafe_orb{o}.json"
        try:
            run(PY + ["dafe.py", str(o), sigma, tmp])
            new = json.loads((HERE / tmp).read_text())
            assert [r["L"] for r in new] == [r["L"] for r in stored], o
        finally:
            (HERE / tmp).unlink(missing_ok=True)
        out = run(PY + ["dcheck.py", str(o), str(nchk), "0,33", sigma])
        assert f"agree with PARI up to {nchk}" in out and out.count("checkfeq") == 2
    rec["l_values"] = (f"PASS certified enclosures of the 192 values L({sigma}) reproduced; coefficients agree with "
                       f"PARI up to {nchk}; 6 lfun comparisons")
    # 7
    run(["gcc", "-O3", "-fopenmp", "-I", "..", "-o", "census_d3k", "census_d3k.c", "-lm"])
    run(["./census_d3k", "6e4", "1.2e7", "4", "check_k", "13", "0x888", "0x2888", "debug"])
    sys.path.insert(0, str(CERT))
    sys.path.insert(0, str(P241))
    import rootcheck
    from census241 import legendre, sqrtmod
    X = 12 * 10**6
    s = bytearray([1]) * (X + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(X**0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    ref = []
    for p in range(60001, X + 1):
        if s[p] and p % 120 in (1, 49) and legendre(241, p) == 1:
            r = sqrtmod(241, p)
            for rr in (r, p - r):
                b = rootcheck.bits(p, rr)
                if b is not None:
                    ref.append("%d %d %s" % (p, rr, "".join("1" if x == -1 else ("0" if x == 1 else "z") for x in b)))
    key = lambda t: (int(t.split()[0]), int(t.split()[1]))  # noqa: E731
    got = sorted((l.split(None, 1)[1].strip() for l in (HERE / "check_k.txt").read_text().splitlines()
                  if l.startswith("bits")), key=key)
    assert got == sorted(ref, key=key)
    # census_kw.c (used for the prefixes kw*) against census_d3k.c: all outputs of mode check, and the
    # .binsBW and undetected list of mode W, on three ranges
    kw_used = any(Path(pre).name.startswith(("kw", "kv")) for pre in dih["prefixes"])
    kv_used = any(Path(pre).name.startswith("kv") for pre in dih["prefixes"])
    ifma = "avx512ifma" in Path("/proc/cpuinfo").read_text() if Path("/proc/cpuinfo").exists() else False
    if kw_used:
        run(["gcc", "-O3", "-fopenmp", "-I", "..", "-o", "census_kw", "census_kw.c", "-lm"])
        if kv_used and ifma:
            run(["gcc", "-O3", "-march=native", "-fopenmp", "-I", "..", "-o", "census_kv", "census_kv.c", "-lm"])
        for lo, hi in (("6e4", "1.2e7"), ("1e13", "1.0004e13"), ("5e13", "5.0004e13")):
            run(["./census_d3k", lo, hi, "4", "cmp_old", "13", "0x888", "0x2888"])
            run(["./census_kw", lo, hi, "4", "cmp_chk", "13", "0x888", "0x2888", "check"])
            run(["./census_kw", lo, hi, "4", "cmp_w", "13", "0x888", "0x2888", "W"])
            for ext in ("bins", "binsB1", "binsBW"):
                assert (HERE / ("cmp_old." + ext)).read_bytes() == (HERE / ("cmp_chk." + ext)).read_bytes(), (lo, ext)
            assert (HERE / "cmp_old.binsBW").read_bytes() == (HERE / "cmp_w.binsBW").read_bytes(), lo
            und = lambda f: sorted(l for l in (HERE / f).read_text().splitlines() if l.startswith("undetected"))  # noqa: E731
            o = (HERE / "cmp_old.txt").read_text().splitlines()[-1]
            assert o == (HERE / "cmp_chk.txt").read_text().splitlines()[-1], lo
            assert und("cmp_old.txt") == und("cmp_chk.txt") == und("cmp_w.txt"), lo
            if kv_used and ifma:
                for mode, pre in (("W", "cmp_v"), ("Wcheck", "cmp_vc")):
                    run(["./census_kv", lo, hi, "4", pre, "13", "0x888", "0x2888", mode])
                    assert (HERE / (pre + ".binsBW")).read_bytes() == (HERE / "cmp_w.binsBW").read_bytes(), (lo, mode)
                    assert (HERE / (pre + ".txt")).read_text().splitlines()[-1] == (HERE / "cmp_w.txt").read_text().splitlines()[-1], (lo, mode)
                    assert und(pre + ".txt") == und("cmp_w.txt"), (lo, mode)
    for name, h in dih["sha256"].items():
        if name.startswith("census/"):
            assert sha(HERE / name) == h, name
    if rerun:
        for pre in dih["prefixes"]:
            tp = HERE / (pre + ".txt")
            txt = (tp.read_text() if tp.exists() else gzip.open(str(tp) + ".gz", "rt").read()).splitlines()[-1]
            m = re.search(r"XLO (\d+) XHI (\d+)", txt)
            if Path(pre).name.startswith("kv") and ifma:
                run(["./census_kv", m.group(1), m.group(2), "12", "rerun_k", "13", "0x888", "0x2888", "W"])
            elif Path(pre).name.startswith(("kw", "kv")):     # census_kw.c W gives the same .binsBW as census_kv.c
                run(["./census_kw", m.group(1), m.group(2), "12", "rerun_k", "13", "0x888", "0x2888", "W"])
            else:
                run(["./census_d3k", m.group(1), m.group(2), "12", "rerun_k", "13", "0x888", "0x2888"])
            assert hashlib.sha256((HERE / "rerun_k.binsBW").read_bytes()).hexdigest() == dih["sha256"][pre + ".binsBW"]
    rec["census"] = ("PASS census_d3k agrees with Python on norms 6e4..1.2e7"
                     + ("; census_kw agrees with census_d3k on three ranges" if kw_used else "")
                     + ("; census_kv (W, Wcheck) agrees with census_kw on them" if kv_used and ifma else
                        "; census_kv not run (no AVX-512 IFMA)" if kv_used else "")
                     + "; stored census data hash-check" + (" and recomputed" if rerun else ""))
    # 8
    for pre in dih["prefixes"]:
        ensure_raw(HERE / (pre + ".binsBW"))
    out = run(PY + ["dihedral_ceiling.py", w["delta"], sigma, dih["Y_E"]] + dih["prefixes"])
    g = json.loads(out[out.index("{"):])
    rec["ceiling"] = {k: g[k] for k in ("Y_E", "Y_W", "dyadic_E_W_term", "Delta_sel", "Delta_P4", "C_W_upper",
                                        "small_gain_lower", "census_gain_lower", "counts", "bins", "XC", "C_eff_upper")}
    if "refined_TV" in dih:
        rt = dih["refined_TV"]
        out = run(PY + ["lptv.py", w["delta"], sigma, dih["Y_E"], rt["a"], rt["b"]] + dih["prefixes"])
        g = json.loads(out[out.index("{"):])
        rec["refined_TV"] = g
    if "signed" in dih:                        # Proposition E: signed kernel over the abscissae of dih["signed"]
        sg = dih["signed"]
        hp_files = [n for n in dih["sha256"] if n.startswith("hp/")]
        for s_ in sg["sigmas"]:
            p_, q_ = s_.split("/")
            needed = [f"hp/afe241hp_{p_}_{q_}.json"] + [f"hp/dafe_orb{o}_{p_}_{q_}.json" for o in dih["orbits"]]
            assert all(n in hp_files for n in needed), s_
        for name in hp_files + ["hp_lrows241.json"]:          # the rows that ye_hp.py reuses are pinned too
            assert sha(HERE / name) == dih["sha256"][name], name
        sample = sg["sigmas"] if full_lv else [sg["sigmas"][0], sg["sigmas"][-1]]
        tmp = HERE / "replay_hp"
        tmp.mkdir(exist_ok=True)
        try:
            for s_ in sample:
                p_, q_ = s_.split("/")
                run(PY + ["ye_hp.py", "--outdir", str(tmp), s_])
                key = "normalized_log_zeta_EB"
                assert (json.loads((tmp / f"afe241hp_{p_}_{q_}.json").read_text())[key]
                        == json.loads((HERE / "hp" / f"afe241hp_{p_}_{q_}.json").read_text())[key]), s_
                for o in dih["orbits"]:
                    name = f"dafe_orb{o}_{p_}_{q_}.json"
                    run(PY + ["dafe.py", str(o), s_, str(tmp / name), "999999"])
                    new = json.loads((tmp / name).read_text())
                    old = json.loads((HERE / "hp" / name).read_text())
                    assert [r_["L"] for r_ in new] == [r_["L"] for r_ in old], (s_, o)
            pf = tmp / "params.json"
            pf.write_text(json.dumps(sg))
            out = run(PY + ["signed.py", "certify", w["delta"], str(pf)] + dih["prefixes"])
        finally:
            for f_ in tmp.glob("*"):
                f_.unlink()
            tmp.rmdir()
        g = json.loads(out[out.index("{"):])
        rec["signed"] = {**g, "recomputed_abscissae": sample}
    m = re.search(r"\[([0-9.e-]+) \+/- ([0-9.e-]+)\]", g["C_eff_upper"])
    assert Q(m.group(1)) + Q(m.group(2)) <= Q(dih["C_eff"]), (g["C_eff_upper"], dih["C_eff"])
    # 9
    sys.path.insert(0, str(P41))
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
    after, fok, sok = geom241.margin(w["delta"], dih["C_eff"], {"ks": w["ks"], "finite_profiles": w["finite_profiles"]},
                                     s=w["s"], a=w["a"], bern=[[Q(v) for v in row] for row in w["bernstein"]],
                                     verbose=False)
    assert fok and sok and lower(after) > 0
    rec["geometry"] = {"C_effective": dih["C_eff"], "margin_after_concentration_lower": interval_strings(after)[0][:22]}
    rec["status"] = f"PASS dihedral replay for delta = {w['delta']} (exponent 1+delta)"
    rec["seconds"] = round(time.monotonic() - t0)
    (HERE / ("replay_" + w["delta"] + ".json")).write_text(json.dumps(rec, indent=1) + "\n")
    print(json.dumps(rec, indent=1))


def cleanup():
    """Remove the binaries and scratch outputs of step 7, and raw census files that have a .gz copy."""
    for name in ("census_d3k", "census_kw", "census_kv"):
        (HERE / name).unlink(missing_ok=True)
    for pre in ("check_k", "cmp_old", "cmp_chk", "cmp_w", "cmp_v", "cmp_vc", "rerun_k"):
        for ext in (".bins", ".binsB1", ".binsBW", ".txt"):
            (HERE / (pre + ext)).unlink(missing_ok=True)
    for raw in (HERE / "census").glob("*.binsBW"):
        if Path(str(raw) + ".gz").exists():
            raw.unlink()


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    try:
        main(args[0] if args else "witness_0.043119.json", rerun="--rerun" in sys.argv,
             nchk=3000 if "--quick" in sys.argv else 20000, full_lv="--full-lv" in sys.argv)
    finally:
        cleanup()
