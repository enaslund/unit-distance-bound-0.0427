"""C126 independent check of R5-no-c4-g4bound Sec 1 (no C4 quotient).

Stdlib only, no numpy, no lie241 import: parses the V table from
papers/0.04273/certificates/lie241.py source text, rebuilds the 22
quadratic initials as symmetric 8x8 matrices over F2 (S(v)=outer(v,v),
B(v,w)=outer(v,w)+outer(w,v)), and checks:

  A. diag(R2) has rank 8 (nullity 0), with the hand-check pins:
     x1->e2, x2->e3, tau3sq1->e4, tau3sq2->e5, tau5sq1->e6,
     tau5sq2->e7, c1^2|c0,1=[1,0], c2^2|c0,1=[1,1].
     Hence every nonzero phi in F2^8 is detected (some relator has
     sum M_ii phi_i != 0), so no surjection GB -> C4 exists
     (see corpus entry for the lambda_phi proof).
  B. R2 rank is 21 (22 rows, one relation), so the 21 quadratic
     normal generators have independent initials (deg-2 step of Sec 2).

Usage: python3 research/2026-10-muse-involution-class/code/C126/c126_no_c4_check.py
"""
import re
import sys

LIE = "papers/0.04273/certificates/lie241.py"


def f2rank(rows, ncols):
    M = [list(r) for r in rows]
    r = 0
    for c in range(ncols):
        p = None
        for i in range(r, len(M)):
            if M[i][c]:
                p = i
                break
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        for i in range(len(M)):
            if i != r and M[i][c]:
                for j in range(c, ncols):
                    M[i][j] ^= M[r][j]
        r += 1
    return r


def outer(v, w):
    return [[(a & b) for b in w] for a in v]


def mat_add(A, B):
    return [[(a ^ b) for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def S(v):
    return outer(v, v)


def B(v, w):
    return mat_add(outer(v, w), outer(w, v))


def main():
    src = open(LIE).read()
    # Parse V table: "name": [bits...]
    V = {}
    for m in re.finditer(r'"([A-Za-z0-9_^]+)"\s*:\s*\[([0-9,\s]+)\]', src):
        name = m.group(1)
        vals = [int(x) for x in m.group(2).split(",")]
        if len(vals) == 8:
            V[name] = vals
    need = ["c1", "c2", "x1", "y1", "z1", "x2", "y2", "z2",
            "t31", "p31", "t32", "p32", "t51", "p51", "t52", "p52"]
    for k in need:
        assert k in V, "missing V[%s]" % k
    print("V table parsed: %d entries" % len(V))

    rels = []
    names = []

    def add(M, nm):
        rels.append(M)
        names.append(nm)

    add(S(V["c1"]), "c1^2")
    add(S(V["c2"]), "c2^2")
    for j in ("1", "2"):
        add(mat_add(B(V["t3" + j], V["p3" + j]), S(V["t3" + j])), "tame3" + j)
        add(B(V["t5" + j], V["p5" + j]), "tame5" + j)
    for j in ("1", "2"):
        x, y, z = V["x" + j], V["y" + j], V["z" + j]
        add(mat_add(mat_add(S(y), B(x, y)), B(x, z)), "demuskin" + j)
        add(S(x), "x^2_" + j)
        add(B(x, y), "[x,y]_" + j)
        add(B(x, z), "[x,z]_" + j)
    for j in ("1", "2"):
        add(S(V["t3" + j]), "tau3sq" + j)
        add(S(V["t5" + j]), "tau5sq" + j)
        add(S(V["p3" + j]), "phi3sq" + j)
        add(S(V["p5" + j]), "phi5sq" + j)
    assert len(rels) == 22, len(rels)
    print("22 initials rebuilt: %s" % ",".join(names))

    # A. diag rank
    diags = [[M[i][i] & 1 for i in range(8)] for M in rels]
    r = f2rank(diags, 8)
    print("diag rows: rank %d nullity %d (expect 8 0)" % (r, 8 - r))
    assert r == 8
    idx = {nm: k for k, nm in enumerate(names)}
    pins = [("tau3sq1", 4), ("tau3sq2", 5), ("tau5sq1", 6),
            ("tau5sq2", 7), ("x^2_1", 2), ("x^2_2", 3)]
    for nm, c in pins:
        d = diags[idx[nm]]
        assert d[c] == 1 and sum(d) == 1, (nm, d)
    print("pins 2..7 singleton: OK")
    c1d = [diags[idx["c1^2"]][0], diags[idx["c1^2"]][1]]
    c2d = [diags[idx["c2^2"]][0], diags[idx["c2^2"]][1]]
    print("real diags on 0,1: %s %s (expect [1,0] [1,1])" % (c1d, c2d))
    assert c1d == [1, 0] and c2d == [1, 1]
    # Hand nullity: pins force phi2..7=0, then c1 forces phi0=0, c2 forces phi1=0.
    for mask in range(256):
        phi = [(mask >> i) & 1 for i in range(8)]
        if all(v == 0 for v in phi):
            continue
        hit = any(sum(d[i] * phi[i] for i in range(8)) % 2 for d in diags)
        assert hit, "undetected phi %s" % (phi,)
    print("all 255 nonzero phi detected: OK")

    # B. R2 rank 21 (flatten 8x8 to 64 bits)
    flat = [[M[i][j] & 1 for i in range(8) for j in range(8)] for M in rels]
    r2 = f2rank(flat, 64)
    print("R2 rank: %d (expect 21)" % r2)
    assert r2 == 21
    # 21 generator initials (drop demuskin1) independent
    flat21 = [f for f, nm in zip(flat, names) if nm != "demuskin1"]
    r21 = f2rank(flat21, 64)
    print("R2 without demuskin1: %d (expect 21)" % r21)
    assert r21 == 21

    print("ALL PASS")


if __name__ == "__main__":
    sys.exit(main())
