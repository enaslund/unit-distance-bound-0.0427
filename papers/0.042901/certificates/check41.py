#!/usr/bin/env python3
"""Cap compatibility for the single C4 cap at one prime above 41 (tower over B=Q(sqrt 241)).

Checks, using the quadratic relation span R2 of lie241 (unchanged: fourth-power
caps have no quadratic initials):
  1. 41 splits in B (two primes, norms 41).
  2. For both B-primes above 41: S(frob) is NOT in R2, so each Frobenius has
     order divisible by 4 in G_B/D3 (a C4 cap there gives relative f=4).
  3. Neither Frobenius vector equals c1 (so c1 avoids each cyclic decomposition
     span, giving K/F splitting as in construction.md section 3.6).
The capped prime is P41[1] (PARI order), vector [0,0,1,1,1,0,0,0], matching
kummer41.gp. The other B-prime above 41 stays uncapped (census f_min=4).
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
Q241 = HERE.parent.parent / "0.04273/certificates"
sys.path.insert(0, str(Q241))
import numpy as np
from lie241 import S, rels, names, f2rank, V
from census241 import KB, legendre, sqrtmod

Q = [m for m, nm in zip(rels, names) if nm != "demuskin1"]
Qm = np.array([m.flatten() for m in Q], dtype=np.uint8)
R0 = f2rank(Qm)


def in_R2(v):
    return f2rank(np.vstack([Qm, S(v).flatten()])) == R0


def main():
    assert legendre(241, 41) == 1, "41 must split in B"
    r = sqrtmod(241, 41)
    vecs = []
    for rr in (r, 41 - r):
        code = []
        for aa, b, den in KB:
            x = ((aa + b * rr) * pow(den, -1, 41)) % 41
            code.append(1 if legendre(x, 41) == -1 else 0)
        v = np.array(code, dtype=np.uint8)
        vecs.append((rr, code, v))
    # PARI kummer41.gp order: P41[1] <-> rr=6, P41[2] <-> rr=35
    assert vecs[0][1] == [0, 0, 1, 1, 1, 0, 0, 0], vecs[0][1]
    assert vecs[1][1] == [0, 0, 1, 1, 0, 1, 0, 0], vecs[1][1]
    c1 = V["c1"]
    for rr, code, v in vecs:
        assert (v != 0).any(), "Frobenius vector must be nonzero"
        assert not in_R2(v), f"S(frob41,rr={rr}) must be independent mod R2 (order>=4)"
        assert not np.array_equal(c1, v), "c1 must differ from each Frobenius vector"
        # cyclic decomposition span is {0, v}; c1 outside it gives trivial
        # intersection <c1> cap <frob> (if c1 = frob^k then c1 = 0 or v mod Frattini)
        A = np.array([v])
        assert f2rank(np.vstack([A, c1])) != f2rank(A), "c1 must avoid the decomposition span"
    print("PASS 41 splits; both Frobenius squares independent mod R2; c1 separated")
    print("capped B-prime: P41[1], vector [0,0,1,1,1,0,0,0]; other B-prime uncapped")


if __name__ == "__main__":
    main()
