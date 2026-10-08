#!/usr/bin/env python3
"""The space W' = span(psi_10, psi_23, psi_19) of degree-two functionals (orbits of d4all27.json), for the field E_W'.

Checks: psi_10 + psi_19 = psi_20 and psi_10 + psi_23 = psi_24, so the nonzero elements of W' are psi_10, psi_23,
psi_24, psi_19, psi_20 (all D4 classes of d4search.py, alternating rank 2) and psi_19 + psi_23, psi_19 + psi_24
(not D4 classes; alternating rank 4: their irreducible representations with that central character are the 16
four-dimensional rho_19 (x) rho_o (x) lambda_w, o = 23, 24).  Writes the masks of psi_10, psi_23, psi_24, psi_19,
psi_20 in the basis of the fifteen census functionals (d4fields15.json): a vector-0 prime with census pattern b has
Frobenius in ker W' iff parity(b & m) = 0 for m = m_10, m_23, m_19 (wmasks3.json).
"""
import contextlib
import io
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


def alt_rank(p):
    """rank of the alternating form (i<j coordinates 8..35 of a functional on S(v) = v v^T)"""
    B = np.zeros((8, 8), dtype=np.uint8)
    k = 8
    for i in range(8):
        for j in range(i + 1, 8):
            B[i, j] = B[j, i] = p[k]
            k += 1
    return f2rank(B)


def main():
    R = np.array([coords36(m) for m in rels])
    allf = json.loads((HERE / "d4all27.json").read_text())["fields"]
    P = {o: psi(allf[o]["rows"], allf[o]["rho"]) for o in range(27)}
    for o in range(27):
        assert P[o].tolist() == allf[o]["psi"] and not (R.dot(P[o]) % 2).any()
    keys = {P[o].tobytes(): o for o in range(27)}
    assert ((P[10] ^ P[23]) == P[24]).all() and ((P[10] ^ P[19]) == P[20]).all()
    basis = [P[10], P[23], P[19]]
    assert f2rank(np.array(basis)) == 3
    elems = {}
    for m in range(1, 8):
        v = np.bitwise_xor.reduce([basis[t] for t in range(3) if (m >> t) & 1])
        elems[m] = (keys.get(v.tobytes()), alt_rank(v))
    d4 = sorted(o for o, r in elems.values() if o is not None)
    assert d4 == [10, 19, 20, 23, 24], d4
    assert all(r == 2 for o, r in elems.values() if o is not None)
    assert sorted(r for o, r in elems.values() if o is None) == [4, 4]
    # 256 + 5 * 64 * 2^2 + 2 * 16 * 4^2 = 2048 = |Gal(E_W'/B)|
    assert 256 + 5 * 64 * 4 + 2 * 16 * 16 == 2 ** 11
    F15 = json.loads((HERE.parent / "d4fields15.json").read_text())
    Bm = np.array([psi(f["rows"], f["rho"]) for f in F15], dtype=np.uint8)
    masks = {}
    for o in (10, 23, 24, 19, 20):
        found = [m for m in range(1, 1 << 15)
                 if (np.bitwise_xor.reduce([Bm[i] for i in range(15) if (m >> i) & 1]) == P[o]).all()]
        assert len(found) == 1
        masks[str(o)] = found[0]
    old = json.loads((HERE / "wmasks.json").read_text())
    assert all(masks[k] == old[k] for k in old)
    out = HERE / "wmasks3.json"
    if out.exists():
        assert json.loads(out.read_text()) == masks
    else:
        out.write_text(json.dumps(masks) + "\n")
    print("plane3: PASS W' = span(psi_10, psi_23, psi_19): D4 classes", d4, "and two rank-4 forms; masks",
          {k: hex(v) for k, v in masks.items()})


if __name__ == "__main__":
    main()
