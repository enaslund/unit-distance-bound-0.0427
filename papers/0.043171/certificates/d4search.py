#!/usr/bin/env python3
"""All D4 quotient data (phi_1, rho) of G_B, up to GL(2,2), and the rank of their functionals.

A surjection phi_1 = (r1, r2): F_2^8 -> F_2^2 and a class rho != 0 give the linear form psi on L_2 with
psi(v^[2]) = [phi_1 v = rho] and psi([v, w]) = det(phi_1 v, phi_1 w).  A D4 quotient of G_B with
Frattini quotient phi_1 and rotation class rho exists iff psi vanishes on R_2 (the class of the central
extension inflates to zero exactly then).  psi is unchanged when (phi_1, rho) is replaced by
(g phi_1, g rho), g in GL(2,2).  Prints the number of classes, the rank of their functionals (the
dimension of gr_2 G_B is 15), and checks that the fifteen fields of d4fields15.json are among them.
"""
import contextlib
import io
import itertools
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "0.04273/certificates"))
with contextlib.redirect_stdout(io.StringIO()):
    from lie241 import rels, f2rank  # noqa: E402
sys.path.insert(0, str(HERE))
from d4fields import psi, coords36  # noqa: E402

N = 8


def main():
    R = np.array([coords36(m) for m in rels])
    vecs = [np.array([(c >> k) & 1 for k in range(N)], dtype=np.uint8) for c in range(1, 256)]
    classes = {}
    for a, b in itertools.permutations(range(255), 2):
        r1, r2 = vecs[a], vecs[b]
        if a > b:
            continue                      # unordered rows; GL(2,2) acts on the pair below
        if not ((r1 ^ r2).any()):
            continue
        for rho in ([1, 0], [0, 1], [1, 1]):
            p = psi(["".join(map(str, r1)), "".join(map(str, r2))], rho)
            if (R.dot(p) % 2).any():
                continue
            classes.setdefault(p.tobytes(), (r1, r2, rho))
    P = np.array([np.frombuffer(k, dtype=np.uint8) for k in classes])
    print("D4 classes (distinct functionals):", len(classes), " rank:", f2rank(P))
    mine = json.loads((HERE / "d4fields15.json").read_text())
    for f in mine:
        assert psi(f["rows"], f["rho"]).tobytes() in classes
    print("the 15 census fields are among them")
    return len(classes), f2rank(P)


if __name__ == "__main__":
    main()
