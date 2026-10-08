#!/usr/bin/env python3
"""The space W'' = span(psi_10, psi_23, psi_19, psi_17) of degree-two functionals (orbits of d4all27.json), for E_W''.

Checks: the nonzero elements of W'' are the seven D4 classes 10, 23, 24, 19, 20, 17, 7 (alternating rank 2;
psi_7 = psi_17 + psi_19) and eight functionals of alternating rank 4, each the sum of two of those D4 classes with
the pairs (19,23), (19,24), (7,10), (17,10), (17,24), (7,24), (7,23), (17,23) (the degree-8 families); no
functional outside W'' keeps all ranks <= 4 when added (so W'' is maximal for that property).  Writes the masks of
the seven classes in the census basis (wmasks4.json): a vector-0 prime with census pattern b has Frobenius in ker W''
iff parity(b & m) = 0 for m = m_10, m_23, m_19, m_17.
"""
import contextlib
import io
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent.parent.parent / "0.04273/certificates"))
with contextlib.redirect_stdout(io.StringIO()):
    from d4fields import psi, coords36
    from lie241 import rels, f2rank
from plane3 import alt_rank  # noqa: E402

PAIRS = [(19, 23), (19, 24), (7, 10), (17, 10), (17, 24), (7, 24), (7, 23), (17, 23)]


def main():
    R = np.array([coords36(m) for m in rels])
    allf = json.loads((HERE / "d4all27.json").read_text())["fields"]
    P = {o: psi(allf[o]["rows"], allf[o]["rho"]) for o in range(27)}
    for o in range(27):
        assert not (R.dot(P[o]) % 2).any()
    keys = {P[o].tobytes(): o for o in range(27)}
    basis = [P[10], P[23], P[19], P[17]]
    assert f2rank(np.array(basis)) == 4
    span = {}
    for m in range(1, 16):
        v = np.bitwise_xor.reduce([basis[t] for t in range(4) if (m >> t) & 1])
        span[v.tobytes()] = v
    d4 = sorted(keys[k] for k in span if k in keys)
    assert d4 == [7, 10, 17, 19, 20, 23, 24], d4
    assert all(alt_rank(v) == 2 for k, v in span.items() if k in keys)
    r4 = [v for k, v in span.items() if k not in keys]
    assert len(r4) == 8 and all(alt_rank(v) == 4 for v in r4)
    sums = sorted(tuple(sorted(p)) for p in PAIRS)
    got = []
    for a, b in PAIRS:
        v = P[a] ^ P[b]
        assert v.tobytes() in span and v.tobytes() not in keys
        got.append(v.tobytes())
    assert len(set(got)) == 8                         # the eight rank-4 functionals, one pair each
    # maximality: no functional outside W'' (in the 15-dimensional space) keeps all ranks <= 4
    F15 = json.loads((HERE.parent / "d4fields15.json").read_text())
    Bm = np.array([psi(f["rows"], f["rho"]) for f in F15], dtype=np.uint8)
    vecs = {}
    for m in range(1, 1 << 15):
        vecs[m] = np.bitwise_xor.reduce([Bm[i] for i in range(15) if (m >> i) & 1])
    W = [np.zeros(36, dtype=np.uint8)] + list(span.values())
    Wb = {w.tobytes() for w in W}
    for m, v in vecs.items():
        if v.tobytes() in Wb:
            continue
        assert max(alt_rank(v ^ w) for w in W) > 4, hex(m)
    masks = {}
    for o in (10, 23, 24, 19, 20, 17, 7):
        found = [m for m, v in vecs.items() if (v == P[o]).all()]
        assert len(found) == 1
        masks[str(o)] = found[0]
    old = json.loads((HERE / "wmasks3.json").read_text())
    assert all(masks[k] == old[k] for k in old)
    out = HERE / "wmasks4.json"
    if out.exists():
        assert json.loads(out.read_text()) == masks
    else:
        out.write_text(json.dumps(masks) + "\n")
    print("plane4: PASS W'' = span(psi_10, psi_23, psi_19, psi_17): D4 classes", d4, "and eight rank-4 forms",
          sums, "; maximal; masks", {k: hex(v) for k, v in masks.items()})


if __name__ == "__main__":
    main()
