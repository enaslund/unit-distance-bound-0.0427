#!/usr/bin/env python3
"""Input file of dcoef4.c for the 64 twists of one D4 field, from the export of exportg.gp (ddata_orb<o>.json with r1K,
r1Bc, PSMALL).  The gamma type of zeta(K_w)/zeta(Bc) is Gamma_R^(r1(K) - r1(Bc)) Gamma_C^(r2(K) - r2(Bc)):
(0, 2) 'quartic', (2, 1) 'mixed31', (-2, 3) 'mixed13'; all twists of one orbit must share the grid (same d, xtop).
Usage: dprep4.py EXPORT_JSON OUTPUT [K1,K2,...]   (writes OUTPUT and OUTPUT.json; optional subset of twist indices)
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gkernel as GK  # noqa: E402

KB = [(-1, 0, 1), (-71011068, 4574225, 1), (-6101, -393, 2), (6101, -393, 2), (31, -2, 1), (31, 2, 1), (326, -21, 1), (326, 21, 1)]
TYPEMAP = {(0, 2): "quartic", (2, 1): "mixed31", (-2, 3): "mixed13"}


def gamma_type(r1K, r1Bc):
    r2K, r2Bc = (8 - r1K) // 2, (4 - r1Bc) // 2
    return TYPEMAP[(r1K - r1Bc, r2K - r2Bc)]


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def main(src, out, sel=None):
    """sel: the indices of the twists to include (all by default); they must share the grid (d, xtop)"""
    d = json.loads(Path(src).read_text())
    PS = d["PSMALL"]
    idx = list(range(len(d["twists"]))) if sel is None else sel
    types = [gamma_type(d["twists"][k]["r1K"], d["r1Bc"]) for k in idx]
    T0 = GK.TYPES[types[0]]
    assert all(GK.TYPES[t]["d"] == T0["d"] and GK.TYPES[t]["xtop"] == T0["xtop"] for t in types)
    pts = GK.grid(T0["xtop"])
    rows, meta = [], []
    for k, ty in zip(idx, types):
        tw = d["twists"][k]
        nb = GK.nbounds(ty, tw["Q"])
        t = GK.TYPES[ty]["kappa"]() / GK.arb(tw["Q"]).sqrt()
        rows.append((tw, float(t.mid()), nb))
        meta.append({"k": k, "w": tw["w"], "Q": tw["Q"], "type": ty, "N": nb[0], "t": float(t.mid())})
    NMAX = max(r[2][0] for r in rows)
    assert NMAX < PS * PS, (NMAX, PS)
    L = [f"NTW {len(idx)}", f"D {GK.DEG}", f"DPOW {T0['d']}", f"PSMALL {PS}", f"NMAX {NMAX}", "KB"]
    L += [f"{a} {b} {den}" for a, b, den in KB]
    for key, name in (("c", "C"), ("g0", "G0"), ("g1", "G1")):
        a, b, den = d[key]
        L += [name, f"{a} {b} {den}"]
    L += [f"CELLS {len(pts) - 1}", " ".join(float(c).hex() for c in pts)]
    L += ["TW"]
    for tw, t, nb in rows:
        L.append(f"{sum(int(x) << k for k, x in enumerate(tw['w']))} {t.hex()} {nb[0]} " + " ".join(str(v) for v in nb))
    ps = primes_upto(PS)
    L += [f"EULER {len(ps)}"]
    for p in ps:
        row = [str(p)]
        for k in idx:
            tw = d["twists"][k]
            P = list(tw["bad"][str(p)] if p in (2, 3, 5) else tw["small"][str(p)])
            while len(P) > 1 and P[-1] == 0:
                P.pop()
            row.append(f"{len(P) - 1} " + " ".join(str(c) for c in P))
        L.append(" ".join(row))
    Path(out).write_text("\n".join(L) + "\n")
    Path(out + ".json").write_text(json.dumps({"src": str(src), "PSMALL": PS, "NMAX": NMAX, "twists": meta}, indent=1) + "\n")
    from collections import Counter
    print(f"dprep4: {out}: types {dict(Counter(types))}, NMAX {NMAX}, {len(ps)} Euler primes")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], [int(v) for v in sys.argv[3].split(",")] if len(sys.argv) > 3 else None)
