#!/usr/bin/env python3
"""Replay for the certificates over E_W' (README Section 11b; witness key dihedral.space = "W3") and E_W''
(dihedral.space = "W4"): the signed kernel of Proposition E with Y_* computed in E_W' resp. E_W''.

Steps (asserted):
  1. the D4 data: 27 classes and rank 15 (d4search.py), the census fields (d4fields.py, vd4.gp, rootcheck.py), the
     spaces W' and W'' (plane3.py, wmasks3.json; for W'' also plane4.py, wmasks4.json) and their D4 fields
     (vplane3.gp / vplane4.gp); for general shell weights, general_windows_check.py (brute-force shell lemma);
  2. exports: export.gp reproduces ddata_orb10/23/24.json, exportg.gp ddata_orb<o>.json of the new orbits, export8.gp
     the degree-8 exports (stored gzipped in deg8/data/), mkbad: deg8/deg8_bad.json; inertv0_3.py / inertv0_4.py;
  3. coefficients and moments: dcoef4.c (all degree-4 families of hp3) and, with --full, octcoef.c (degree 8; about one
     CPU-hour per family) with their rule checks against PARI (the rule check alone otherwise); octtest.py (Euler
     product at 19/10) on the degree-8 moments;
  4. L-values: Y_E and orbits 10, 23, 24 (hp/, as reproduce_dihedral.py step 8) and the hp3/ values recomputed at
     three abscissae with nonzero coefficient (the smallest, the largest, the largest |c|; all used ones with
     --full-lv) equal the stored ones; every file the certification reads is pinned and hash-checks;
  5. census: census_kv4.c agrees with census_kv.c (binsBW, undetected lists, modes W and Wcheck) on three ranges; its
     ker-W, ker-W' and ker-W'' bins on norms 6e4..1.2e7 equal an independent classification (rootcheck.py and the
     masks); the ker-W bins of the stored w4_* prefixes equal the earlier reviewed census data; all hash-check
     (--rerun recomputes them);
  6. signed3.py certify gives C_eff at most the witness value; 7. certified margin > 0 at delta (geom241.margin, with
     general shell weights where the witness gives a weight matrix: ../margin_general.py, ../general_windows.py).
Run from this directory.  Needs gcc with OpenMP and AVX-512 IFMA (census_kv4.c), PARI/GP, python-flint 0.9.0.
Options: --full (octcoef.c), --full-lv, --rerun.
"""
import gzip
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
import time
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
CERT = HERE.parent
D8 = HERE / "deg8"
P41 = CERT.parent.parent / "0.042901/certificates"
P241 = CERT.parent.parent / "0.04273/certificates"
PY = [sys.executable, "-B"]


def run(cmd, cwd=HERE, stdin=None):
    return subprocess.run(cmd, capture_output=True, text=True, check=True, cwd=str(cwd), input=stdin).stdout


def sha(path):
    p = Path(path)
    data = p.read_bytes() if p.exists() else gzip.open(str(p) + ".gz", "rb").read()
    return hashlib.sha256(data).hexdigest()


class Unchanged:
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


def main(witness, full=False, full_lv=False, rerun=False):
    t0 = time.monotonic()
    w = json.loads((HERE / witness).read_text())
    dih = w["dihedral"]
    space = dih["space"]
    sys.path.insert(0, str(HERE))
    import dihedral_ceiling3 as DC3
    SP = DC3.SPACES[space]
    hs = dih["sha256"]
    rec = {"witness": witness, "delta": w["delta"], "space": space}
    for name, h in hs.items():                      # every pinned file
        assert sha(HERE / name) == h, name
    # every file the certification reads is pinned
    need = [f"ddata_orb{o}.json" for o in SP["orbits"]] + ["deg8/deg8_bad.json", SP["inert"], SP["maskfile"],
                                                           "d4all27.json", "vd4_data27.gp", "hp_lrows241.json"]
    used = [s_ for s_, c_ in zip(dih["signed"]["sigmas"], dih["signed"]["c"]) if Q(c_) != 0]
    for s_ in used:
        p_, q_ = s_.split("/")
        hp3o = SP.get("orbits_from_hp3", ())
        need += [f"hp/afe241hp_{p_}_{q_}.json"] + [f"hp/dafe_orb{o}_{p_}_{q_}.json" for o in (10, 23, 24) if o not in hp3o]
        need += [f"hp3/orb{o}_{p_}_{q_}.json" for o in list(hp3o) + list(SP["orbits"][3:])]
        need += [f"hp3/deg8_{o1}_{o2}_{p_}_{q_}.json" for o1, o2 in SP["families"]]
    for pre in dih["prefixes"]:
        need += [pre + ".txt", pre + "." + SP["bins"]]
    need += [f"deg8/data/ddata_orb{o}g.json" for o in SP.get("orbits_from_hp3", ())]
    missing = [n for n in need if n not in hs]
    assert not missing, ("files read but not pinned", missing)
    rec["hashes"] = f"PASS {len(hs)} pinned files, covering all {len(need)} files the certification reads"
    # 1
    with Unchanged(CERT / "d4fields15.json", CERT / "d4fields15.h", CERT / "vd4_data.gp", CERT / "mtilde15.gp"):
        out = run(PY + ["d4search.py"], CERT)
        assert "D4 classes (distinct functionals): 27  rank: 15" in out
        out = run(PY + ["d4fields.py"], CERT)
        assert "rank 15" in out
        out = run(["gp", "-q", "-s", "4000000000", "vd4.gp"], CERT, stdin="")
        assert "vd4: PASS all 15 fields" in out
        out = run(PY + ["rootcheck.py"], CERT)
        assert "rootcheck: PASS 80" in out
    with Unchanged(HERE / "wmasks3.json"):
        out = run(PY + ["plane3.py"])
    assert "plane3: PASS" in out
    if space == "W4":                               # W'': structure, family pairs, maximality, wmasks4.json
        with Unchanged(HERE / "wmasks4.json"):
            out4 = run(PY + ["plane4.py"])
        assert "plane4: PASS" in out4
    vp = "vplane3.gp" if space == "W3" else "vplane4.gp"
    out = run(["gp", "-q", "-s", "4000000000", vp], stdin="")
    assert "PASS orbits" in out
    rec["d4"] = "PASS 27 classes, rank 15, census fields, " + out.strip().splitlines()[-1]
    if any(isinstance(v[0], list) for v in w["finite_profiles"].values()):
        outg = run(PY + ["general_windows_check.py"], CERT)
        assert "all 48 brute-force cases agree" in outg
        rec["general_shells"] = "PASS general_windows_check.py: shell lemma for general weights, 48 brute-force cases"
    # 2
    tmp = Path(tempfile.mkdtemp(prefix="replay_w3_", dir=str(HERE)))
    try:
        for o in (10, 23, 24):
            new = tmp / f"ddata_orb{o}.json"
            run(["gp", "-q", "-s", "4000000000"], stdin=f'ORB={o}; OUT="{new}"; read("export.gp");')
            assert sha(new) == hs[f"ddata_orb{o}.json"], o
        for o in SP["orbits"][3:]:
            new = tmp / f"ddata_orb{o}.json"
            run(["gp", "-q", "-s", "4000000000"], stdin=f'ORB={o}; PSMALL=3000; OUT="{new}"; read("deg8/exportg.gp");')
            assert sha(new) == hs[f"ddata_orb{o}.json"], o
        exports = []
        for o1, o2 in SP["families"]:
            new = tmp / f"deg8_{o1}_{o2}.json"
            ps = json.loads(gzip.open(str(D8 / "data" / f"deg8_{o1}_{o2}.json.gz"), "rt").read())["PSMALL"]
            run(["gp", "-q", "-s", "12000000000"],
                stdin=f'O1={o1}; O2={o2}; PSMALL={ps}; OUT="{new}"; read("deg8/export8.gp");')
            assert sha(new) == hs[f"deg8/data/deg8_{o1}_{o2}.json"], (o1, o2)
            exports.append(str(new))
        run(PY + [str(D8 / "mkbad.py"), str(tmp / "bad.json")] + exports)
        newbad = json.loads((tmp / "bad.json").read_text())
        oldbad = json.loads((D8 / "deg8_bad.json").read_text())
        for o1, o2 in SP["families"]:
            assert newbad[f"{o1}_{o2}"] == oldbad[f"{o1}_{o2}"], (o1, o2)
        rec["exports"] = "PASS export.gp, exportg.gp, export8.gp reproduce the stored data; deg8_bad.json"
        inert = SP["inert"]
        with Unchanged(HERE / inert):
            out = run(PY + [inert.replace(".json", ".py")])
        rec["inert_vector0"] = out.strip().splitlines()[-1]
        # 3, 4
        used_c = [(Q(v), Q(c)) for v, c in zip(dih["signed"]["sigmas"], dih["signed"]["c"]) if Q(c) != 0]
        if full_lv:
            sample = [v for v, _ in used_c]
        else:
            pick = {min(used_c)[0], max(used_c)[0], max(used_c, key=lambda t: abs(t[1]))[0]}
            sample = sorted(pick)
        (tmp / "sig.txt").write_text("".join(f"{s}\n" for s in sample))
        run(["gcc", "-O3", "-march=native", "-Wall", "-o", str(tmp / "dcoef4"), str(D8 / "dcoef4.c"), "-lm"])
        run(["gcc", "-O3", "-march=native", "-fopenmp", "-Wall", "-o", str(tmp / "octcoef"), str(D8 / "octcoef.c"), "-lm"])
        lvdir = tmp / "lv"
        hp3o = SP.get("orbits_from_hp3", ())
        for o in hp3o:                                 # exportg.gp data (Euler factors to 3000) of orbits 10, 23, 24
            (tmp / f"ddata_orb{o}g.json").write_bytes(gzip.open(str(D8 / "data" / f"ddata_orb{o}g.json.gz"), "rb").read())
            assert sha(tmp / f"ddata_orb{o}g.json") == hs[f"deg8/data/ddata_orb{o}g.json"], o
            new = tmp / f"regen_orb{o}g.json"
            run(["gp", "-q", "-s", "4000000000"], stdin=f'ORB={o}; PSMALL=3000; OUT="{new}"; read("deg8/exportg.gp");')
            assert sha(new) == hs[f"deg8/data/ddata_orb{o}g.json"], o
        for o in list(hp3o) + list(SP["orbits"][3:]):
            groups = dih["orbit_runs"][str(o)]                 # twist index lists sharing a kernel grid
            src = tmp / f"ddata_orb{o}g.json" if o in hp3o else HERE / f"ddata_orb{o}.json"
            for gi, idx in enumerate(groups):
                inp = tmp / f"orb{o}_{gi}.in"
                run(PY + [str(D8 / "dprep4.py"), str(src), str(inp), ",".join(map(str, idx))])
                out = run([str(tmp / "dcoef4"), str(inp), str(tmp / f"orb{o}_{gi}.mom")])
                run(PY + [str(D8 / "leval.py"), str(tmp / f"orb{o}_{gi}.mom"), str(inp) + ".json", str(tmp / "sig.txt"),
                          str(lvdir), f"orb{o}_part{gi}"])
            for s in sample:
                rows = []
                for gi in range(len(groups)):
                    rows += json.loads((lvdir / f"orb{o}_part{gi}_{s.numerator}_{s.denominator}.json").read_text())
                rows.sort(key=lambda r: r["k"])
                old = json.loads((HERE / "hp3" / f"orb{o}_{s.numerator}_{s.denominator}.json").read_text())
                assert [r["L"] for r in rows] == [r["L"] for r in old], (o, s)
        for (o1, o2), ex in zip(SP["families"], exports):
            inp = tmp / f"fam{o1}_{o2}.in"
            run(PY + [str(D8 / "octprep.py"), ex, str(inp)])
            mom = tmp / f"fam{o1}_{o2}.mom"
            if full:
                out = run([str(tmp / "octcoef"), str(inp), str(mom), str(dih["octcoef_threads"])])
                assert sha(mom) == hs[f"deg8/data/fam{o1}_{o2}.mom"], (o1, o2)
            else:                                   # the rule check only (exits nonzero on a disagreement)
                run([str(tmp / "octcoef"), str(inp), str(mom), "2", "validate"])
                mom.write_bytes(gzip.open(str(D8 / "data" / f"fam{o1}_{o2}.mom.gz"), "rb").read())
                assert sha(mom) == hs[f"deg8/data/fam{o1}_{o2}.mom"], (o1, o2)
            out = run(PY + [str(D8 / "octtest.py"), str(mom), str(inp) + ".json", ex])
            assert "agree at s = 19/10" in out
            run(PY + [str(D8 / "leval.py"), str(mom), str(inp) + ".json", str(tmp / "sig.txt"), str(lvdir),
                      f"deg8_{o1}_{o2}", "--export", ex])
            for s in sample:
                new = json.loads((lvdir / f"deg8_{o1}_{o2}_{s.numerator}_{s.denominator}.json").read_text())
                old = json.loads((HERE / "hp3" / f"deg8_{o1}_{o2}_{s.numerator}_{s.denominator}.json").read_text())
                assert [r["L"] for r in new] == [r["L"] for r in old], (o1, o2, s)
        rec["l_values"] = (f"PASS dcoef4/leval reproduce the hp3 values of orbits {list(SP.get('orbits_from_hp3', ())) + list(SP['orbits'][3:])} and leval the "
                           f"degree-8 values at {[str(s) for s in sample]}; octtest (Euler product at 19/10) on every "
                           f"family" + ("; octcoef.c moments recomputed" if full else ""))
        # hp/ (Y_E, orbits 10, 23, 24): as reproduce_dihedral.py step 8
        for s in sample:
            run(PY + ["ye_hp.py", "--outdir", str(tmp), str(s)])
            key = "normalized_log_zeta_EB"
            assert (json.loads((tmp / f"afe241hp_{s.numerator}_{s.denominator}.json").read_text())[key]
                    == json.loads((HERE / "hp" / f"afe241hp_{s.numerator}_{s.denominator}.json").read_text())[key]), s
            for o in (10, 23, 24):
                if o in SP.get("orbits_from_hp3", ()):
                    continue
                name = f"dafe_orb{o}_{s.numerator}_{s.denominator}.json"
                run(PY + ["dafe.py", str(o), str(s), str(tmp / name), "999999"])
                new = json.loads((tmp / name).read_text())
                old = json.loads((HERE / "hp" / name).read_text())
                assert [r["L"] for r in new] == [r["L"] for r in old], (s, o)
        # 5
        run(["gcc", "-O3", "-march=native", "-fopenmp", "-I", "..", "-o", str(tmp / "census_kv"), "census_kv.c", "-lm"])
        run(["gcc", "-O3", "-march=native", "-fopenmp", "-I", "..", "-o", str(tmp / "census_kv4"), "census_kv4.c", "-lm"])
        for lo, hi in (("6e4", "1.2e7"), ("1e13", "1.0004e13"), ("5e13", "5.0004e13")):
            for mode in ("W", "Wcheck"):
                run([str(tmp / "census_kv"), lo, hi, "4", str(tmp / "a"), "13", "0x888", "0x2888", mode])
                run([str(tmp / "census_kv4"), lo, hi, "4", str(tmp / "b"), "13", "0x888", "0x2888", mode, "0x88", "0x8"])
                assert (tmp / "a.binsBW").read_bytes() == (tmp / "b.binsBW").read_bytes(), (lo, mode)
                la, lb = (tmp / "a.txt").read_text().splitlines(), (tmp / "b.txt").read_text().splitlines()
                assert sorted(x for x in la if x.startswith("undetected")) == sorted(x for x in lb if x.startswith("undetected"))
                assert [x for x in la if x.startswith("XLO")] == [x for x in lb if x.startswith("XLO")]
        # census_kv4.c's ker-W, ker-W' and ker-W'' bins on 6e4..1.2e7 against an independent classification:
        # rootcheck.bits (the 15 census symbols at the vector-0 sides) and the masks of wmasks4.json
        run([str(tmp / "census_kv4"), "60000", "12000000", "4", str(tmp / "c"), "13", "0x888", "0x2888", "Wcheck", "0x88", "0x8"])
        sys.path.insert(0, str(CERT))
        sys.path.insert(0, str(P241))
        import math as _m
        import numpy as _np
        import rootcheck
        from census241 import legendre, sqrtmod
        mk = json.loads((HERE / "wmasks4.json").read_text())
        XLO, X = 60000, 12 * 10**6
        NB = int(_m.ceil(_m.log(X / XLO) / _m.log1p(1 / 65536))) + 2
        ref = {e: _np.zeros(NB, dtype=_np.uint64) for e in ("binsBW", "binsBW3", "binsBW4")}
        sv = bytearray([1]) * (X + 1)
        sv[0:2] = b"\x00\x00"
        for i in range(2, int(X**0.5) + 1):
            if sv[i]:
                sv[i * i::i] = bytearray(len(sv[i * i::i]))
        WMASK = mk["10"] | mk["23"]
        for p_ in range(XLO + 1, X + 1):
            if not (sv[p_] and p_ % 120 in (1, 49) and legendre(241, p_) == 1):
                continue
            r_ = sqrtmod(241, p_)
            for rr in (r_, p_ - r_):
                b = rootcheck.bits(p_, rr)
                if b is None:
                    continue
                pat = sum(1 << i for i, x in enumerate(b) if x == -1)
                if any(x == 0 and (WMASK >> i) & 1 for i, x in enumerate(b)) or not pat:
                    continue                                   # zero in a W field (excluded), or undetected
                par = lambda m: bin(pat & m).count("1") % 2   # noqa: E731
                if par(mk["10"]) or par(mk["23"]):
                    continue
                j = min(int(_m.floor(_m.log(p_ / XLO) / _m.log1p(1 / 65536))), NB - 1)
                ref["binsBW"][j] += 1
                if not par(mk["19"]):
                    ref["binsBW3"][j] += 1
                    if not par(mk["17"]):
                        ref["binsBW4"][j] += 1
        for e in ("binsBW", "binsBW3", "binsBW4"):
            got = _np.fromfile(str(tmp / ("c." + e)), dtype=_np.uint64)
            assert len(got) == NB and (got == ref[e]).all(), e
        for pre in dih["prefixes"]:                    # nesting of the stored bins
            a_ = _np.frombuffer(gzip.open(str(HERE / (pre + ".binsBW.gz")), "rb").read(), dtype=_np.uint64)
            b_ = _np.frombuffer(gzip.open(str(HERE / (pre + ".binsBW3.gz")), "rb").read(), dtype=_np.uint64)
            c_ = _np.frombuffer(gzip.open(str(HERE / (pre + ".binsBW4.gz")), "rb").read(), dtype=_np.uint64)
            assert (b_ <= a_).all() and (c_ <= b_).all(), pre
        # the ker-W bins of the census_kv4.c prefixes equal those of the reviewed earlier census data on the same
        # ranges (census_d3k.c / census_kw.c / census_kv.c), which pins MW1 = 0x888, MW2 = 0x2888 as well
        earlier = {(12000000, 10**13): "census/k1e13", (10**13, 4 * 10**13): "census/kw4e13",
                   (4 * 10**13, 15 * 10**13): "census/kv15e13", (15 * 10**13, 29 * 10**13): "census/kv29e13",
                   (29 * 10**13, 43 * 10**13): "census/kv43e13", (43 * 10**13, 56 * 10**13): "census/kv56e13",
                   (56 * 10**13, 70 * 10**13): "census/kv70e13", (70 * 10**13, 85 * 10**13): "census/kv85e13"}
        for pre in dih["prefixes"]:
            tp = HERE / (pre + ".txt")
            txt = (tp.read_text() if tp.exists() else gzip.open(str(tp) + ".gz", "rt").read())
            m = re.search(r"XLO (\d+) XHI (\d+)", txt)
            old = earlier.get((int(m.group(1)), int(m.group(2))))
            if old is not None:                        # (8.5e14, 2^50) has no earlier counterpart
                assert sha(HERE / (pre + ".binsBW")) == sha(HERE / (old + ".binsBW")), (pre, old)
        if rerun:
            for pre in dih["prefixes"]:
                tp = HERE / (pre + ".txt")
                txt = (tp.read_text() if tp.exists() else gzip.open(str(tp) + ".gz", "rt").read())
                m = re.search(r"XLO (\d+) XHI (\d+)", txt)
                run([str(tmp / "census_kv4"), m.group(1), m.group(2), "12", str(tmp / "r"), "13", "0x888", "0x2888", "W",
                     "0x88", "0x8"])
                for ext in ("binsBW", "binsBW3", "binsBW4"):
                    assert hashlib.sha256((tmp / ("r." + ext)).read_bytes()).hexdigest() == hs[pre + "." + ext], (pre, ext)
        rec["census"] = ("PASS census_kv4 = census_kv on three ranges (W, Wcheck); its ker-W/W'/W'' bins on 6e4..1.2e7 "
                         "= an independent classification; stored bins nested; ker-W bins = earlier census data; "
                         "stored data hash-check" + (" and recomputed" if rerun else ""))
        # 6
        pf = tmp / "params.json"
        pf.write_text(json.dumps(dih["signed"]))
        out = run(PY + ["signed3.py", space, "certify", w["delta"], str(pf)] + dih["prefixes"])
        g = json.loads(out[out.index("{"):])
        rec["signed"] = g
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    m = re.search(r"\[([0-9.e-]+) \+/- ([0-9.e-]+)\]", g["C_eff_upper"])
    assert Q(m.group(1)) + Q(m.group(2)) <= Q(dih["C_eff"]), (g["C_eff_upper"], dih["C_eff"])
    if witness == "witness_0.043171.json":
        # the constants displayed in the manuscript (Lemma ce:values, proof of Theorem an:ceiling), fail closed
        for key, bound in (("rest_plus_TV_upper", "0.000607837"), ("C_eff_upper", "0.0422763211")):
            m = re.search(r"\[([0-9.e-]+) \+/- ([0-9.e-]+)\]", g[key])
            assert Q(m.group(1)) + Q(m.group(2)) < Q(bound), (key, g[key], bound)
        rec["displayed_constants"] = "PASS rest + TV < 0.000607837 (Lemma ce:values); C < 0.0422763211"
    # 7
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
    # finite profiles: product lists (finite_windows.local_window) or, at some places, general weight matrices
    # w_ij of Definition fw:shell-profile (general_windows.local_window_general, Lemma fw:shell-lemma)
    sys.path.insert(0, str(CERT))
    from margin_general import margin_general
    after, fok, sok = margin_general(w["delta"], dih["C_eff"], {"ks": w["ks"], "finite_profiles": w["finite_profiles"]},
                                     s=w["s"], a=w["a"], bern=[[Q(v) for v in row] for row in w["bernstein"]],
                                     verbose=False, EF=geom241.EF)
    assert fok and sok and lower(after) > 0
    rec["geometry"] = {"C_effective": dih["C_eff"], "margin_after_concentration_lower": interval_strings(after)[0][:22]}
    rec["status"] = f"PASS replay over {space} for delta = {w['delta']} (exponent 1+delta)"
    rec["seconds"] = round(time.monotonic() - t0)
    (HERE / ("replay_" + w["delta"] + ".json")).write_text(json.dumps(rec, indent=1) + "\n")
    print(json.dumps(rec, indent=1))


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    main(args[0], full="--full" in sys.argv, full_lv="--full-lv" in sys.argv, rerun="--rerun" in sys.argv)
