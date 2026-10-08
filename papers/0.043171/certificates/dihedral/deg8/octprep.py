#!/usr/bin/env python3
"""Input file of octcoef.c for one degree-8 family, from deg8_19_<O>.json (export8.gp) and the 'octic' grid of
gkernel.py.  Usage: octprep.py EXPORT_JSON OUTPUT [PSMALL_CAP [validate]]   (validate: N clipped below PSMALL^2, for the
rule check of octcoef.c only)
The two conductors of the family form the two groups; for each, t = (2 pi)^4 / sqrt(Q) (nearest double), N = the
last n with t n <= XTOP, and the exact cell thresholds.  Writes OUTPUT and OUTPUT.json (the metadata octeval.py uses).
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gkernel as GK  # noqa: E402

KB = [(-1, 0, 1), (-71011068, 4574225, 1), (-6101, -393, 2), (6101, -393, 2), (31, -2, 1), (31, 2, 1), (326, -21, 1), (326, 21, 1)]
BETAS = ["1.05", "1.1", "1.2", "1.5"]


def mask(v):
    return sum(int(b) << k for k, b in enumerate(v))


def main(src, out, pcap=None, validate=False):
    d = json.loads(Path(src).read_text())
    PS = d["PSMALL"] if pcap is None else min(d["PSMALL"], pcap)
    Qs = sorted({tw["Q"] for tw in d["twists"]})
    assert len(Qs) == 2 and len(d["twists"]) == 16
    pts = GK.grid(GK.TYPES["octic"]["xtop"])
    groups = []
    for Qc in Qs:
        nb = GK.nbounds("octic", Qc)
        t = GK.TYPES["octic"]["kappa"]() / GK.arb(Qc).sqrt()
        groups.append({"Q": Qc, "t": float(t.mid()), "N": nb[0], "nb": nb})
    if validate:
        for G in groups:
            G["N"] = min(G["N"], PS * PS - 1)
            G["nb"] = [min(v, G["N"]) for v in G["nb"]]
    NMAX = max(g["N"] for g in groups)
    assert NMAX < PS * PS, (NMAX, PS)
    lines = [f"NTW 16", f"D {GK.DEG}", f"PSMALL {PS}", f"NMAX {NMAX}", f"BETAS {len(BETAS)} " + " ".join(BETAS), "KB"]
    lines += [f"{a} {b} {den}" for a, b, den in KB]
    for key, name in (("c19", "C19"), ("g0_19", "G0_19"), ("g1_19", "G1_19"), ("cO", "CO"), ("g0_O", "G0_O"), ("g1_O", "G1_O")):
        a, b, den = d[key]
        lines += [name, f"{a} {b} {den}"]
    lines += ["R " + " ".join(str(mask(r)) for r in d["r"])]
    lines += ["TW"] + [f"{mask(tw['w'])} {Qs.index(tw['Q'])}" for tw in d["twists"]]
    lines += [f"CELLS {len(pts) - 1}", " ".join(float(c).hex() for c in pts)]
    for c in pts:
        assert float(c) == c                         # exact doubles
    for g, G in enumerate(groups):
        lines += [f"GROUP {g} {G['t'].hex()} {G['N']}", " ".join(str(v) for v in G["nb"])]
    primes = sorted(int(p) for p in d["twists"][0]["small"] if int(p) <= PS)
    lines += [f"EULER {len(primes)}"]
    for p in primes:
        row = [str(p)]
        for tw in d["twists"]:
            P = list(tw["small"][str(p)])
            while len(P) > 1 and P[-1] == 0:
                P.pop()
            row.append(f"{len(P) - 1} " + " ".join(str(c) for c in P))
        lines.append(" ".join(row))
    Path(out).write_text("\n".join(lines) + "\n")
    meta = {"src": str(src), "PSMALL": PS, "NMAX": NMAX, "betas": BETAS, "pair": d["pair"],
            "groups": [{"Q": G["Q"], "t": G["t"], "N": G["N"]} for G in groups],
            "twists": [{"w": tw["w"], "Q": tw["Q"], "group": Qs.index(tw["Q"])} for tw in d["twists"]]}
    Path(out + ".json").write_text(json.dumps(meta, indent=1) + "\n")
    print(f"octprep: {out}: PSMALL {PS}, N {[G['N'] for G in groups]}, {len(primes)} Euler primes, {len(pts) - 1} cells")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else None, len(sys.argv) > 4 and sys.argv[4] == "validate")
