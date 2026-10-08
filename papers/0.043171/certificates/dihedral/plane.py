#!/usr/bin/env python3
"""The plane W = {0, psi_10, psi_23, psi_24} of degree-two functionals (orbits of d4all27.json).

Checks: each psi_o is the functional of (rows, rho) and vanishes on R_2; psi_10 + psi_23 = psi_24; the 27
D4 classes of d4search.py contain all three, so every nonzero element of W is of D4 type; there is no
3-dimensional subspace with this property (so the plane is maximal).  Writes the masks expressing psi_10
and psi_23 in the basis of the fifteen census functionals (d4fields15.json): a vector-0 prime with census
bit pattern b has Frobenius in ker(psi_10) cap ker(psi_23) iff parity(b & m10) = parity(b & m23) = 0.
"""
import contextlib
import io
import itertools
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent.parent.parent / "0.04273/certificates"))
with contextlib.redirect_stdout(io.StringIO()):
    from d4fields import psi, coords36
    from lie241 import rels, f2rank


def main():
    R = np.array([coords36(m) for m in rels])
    allf = json.loads((HERE / "d4all27.json").read_text())["fields"]
    P = {}
    for o in range(27):
        f = allf[o]
        p = psi(f["rows"], f["rho"])
        assert p.tolist() == f["psi"] and not (R.dot(p) % 2).any()
        P[o] = p
    keys = {P[o].tobytes() for o in range(27)}
    assert len(keys) == 27
    assert ((P[10] ^ P[23]) == P[24]).all()
    # maximality: no 3-dim subspace all of whose nonzero elements are D4 classes
    for a, b, c in itertools.combinations(range(27), 3):
        vs = [P[a], P[b], P[c]]
        if f2rank(np.array(vs)) < 3:
            continue
        if all(np.bitwise_xor.reduce([vs[t] for t in range(3) if (m >> t) & 1]).tobytes() in keys for m in range(1, 8)):
            raise AssertionError("3-dim D4-closed subspace exists")
    F15 = json.loads((HERE.parent / "d4fields15.json").read_text())
    Bm = np.array([psi(f["rows"], f["rho"]) for f in F15], dtype=np.uint8)
    masks = {}
    for o in (10, 23, 24):
        found = [m for m in range(1, 1 << 15)
                 if (np.bitwise_xor.reduce([Bm[i] for i in range(15) if (m >> i) & 1]) == P[o]).all()]
        assert len(found) == 1
        masks[str(o)] = found[0]
    assert masks == json.loads((HERE / "wmasks.json").read_text())
    print("plane: PASS psi_10 + psi_23 = psi_24, all D4 type, plane maximal; masks", masks)


if __name__ == "__main__":
    main()
