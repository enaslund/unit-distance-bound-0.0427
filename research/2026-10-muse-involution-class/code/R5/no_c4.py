"""R5: no-C4 filter (nullity 0) + g4-range premises.

1. diag(R2) over all 22 relator initials: rank 8, nullity 0.
   Hand cross-check: tame/dyadic cap squares pin phi_2..phi_7;
   real squares pin phi_0, phi_1. Hence GB has no C4 quotient
   (note R5-no-c4-g4bound section 1 for the lambda_phi proof).
2. Premises for g4 in [53,81]: R2 rank 21, R3 rows 170 -> 142
   (28 syzygies), free L4 1044, I4 (41-cap) 963.

Usage: .venv/bin/python research/2026-10-muse-involution-class/code/R5/no_c4.py
"""
import sys
import os
import io
import contextlib

sys.path.insert(0, os.path.join("papers", "0.04273", "certificates"))
with contextlib.redirect_stdout(io.StringIO()):
    import numpy as np  # noqa: E402
    from lie241 import V, S, B, n, rels, names  # noqa: E402

E = np.eye(n, dtype=np.uint8)

print("=== 1. diag(R2) nullity ===")
D = np.array([[m[i, i] % 2 for i in range(8)] for m in rels],
             dtype=np.uint8)
A = D.copy()
rr, cc = A.shape
r = 0
for c in range(cc):
    p = None
    for i in range(r, rr):
        if A[i, c]:
            p = i
            break
    if p is None:
        continue
    A[[r, p]] = A[[p, r]]
    for i in range(rr):
        if i != r and A[i, c]:
            A[i] ^= A[r]
    r += 1
print("  22 diag rows: rank %d, nullity %d (expect 8, 0)" % (r, cc - r))
assert r == 8
# hand cross-check pins
idx = {nm: k for k, nm in enumerate(names)}
pins = [("tau3sq1", 4), ("tau3sq2", 5), ("tau5sq1", 6), ("tau5sq2", 7),
        ("x^2_1", 2), ("x^2_2", 3)]
ok = all(D[idx[nm]][c] == 1 and D[idx[nm]].sum() == 1
         for nm, c in pins)
print("  cap squares pin coords 2..7:", ok)
c1d = D[idx["c1^2"]][[0, 1]].tolist()
c2d = D[idx["c2^2"]][[0, 1]].tolist()
print("  real diags on coords 0,1:", c1d, c2d, "(pin phi0, phi0+phi1)")
assert ok and c1d == [1, 0] and c2d == [1, 1]

print("=== 2. g4-range premises ===")


def encode(idx):
    p = 0
    for i in idx:
        p = p * 8 + i
    return 1 << p


def decode(bit, deg):
    idx = [0] * deg
    for j in range(deg - 1, -1, -1):
        idx[j] = bit % 8
        bit //= 8
    return idx


def bits(v):
    o = []
    while v:
        b = v.bit_length() - 1
        o.append(b)
        v ^= 1 << b
    return o


def t2m(M):
    v = 0
    for i in range(8):
        for j in range(8):
            if M[i, j] % 2:
                v |= encode((i, j))
    return v


def mul(A, da, B, db):
    v = 0
    for ba in bits(A):
        ia = decode(ba, da)
        for bb in bits(B):
            v ^= encode(tuple(ia + decode(bb, db)))
    return v


def gen(l):
    return encode((l,))


def br(A, da, B, db):
    return mul(A, da, B, db) ^ mul(B, db, A, da)


def sqm(A, da):
    return mul(A, da, A, da)


def rb(rows):
    bas = {}
    for v in rows:
        w = v
        while w:
            p = w.bit_length() - 1
            if p in bas:
                w ^= bas[p]
            else:
                bas[p] = w
                break
    return len(bas), bas


L2sp = [t2m(S(E[i])) for i in range(8)]
for i in range(8):
    for j in range(i + 1, 8):
        L2sp.append(t2m(B(E[i], E[j])))
Q2 = [t2m(m) for m, nm in zip(rels, names) if nm != "demuskin1"]
print("  R2 rank: %d (expect 21)" % rb(Q2)[0])
assert rb(Q2)[0] == 21
cub3 = []
for j in "12":
    M = t2m(B(V["y" + j], V["z" + j]))
    T = 0
    for ell in range(8):
        if V["z" + j][ell]:
            T ^= br(M, 2, gen(ell), 1)
    cub3.append(T)
R3rows = []
for q in Q2:
    for i in range(8):
        R3rows.append(br(q, 2, gen(i), 1))
R3rows += cub3
rI3, _ = rb(R3rows)
print("  R3 rows: %d rank %d syzygies %d (expect 170 142 28)"
      % (len(R3rows), rI3, len(R3rows) - rI3))
assert (len(R3rows), rI3) == (170, 142)
_, bL2 = rb(L2sp)
L2bas = list(bL2.values())
_, bL3 = rb([br(M, 2, gen(c), 1) for M in L2sp for c in range(8)])
L3bas = list(bL3.values())
free4 = [br(T, 3, gen(l), 1) for T in L3bas for l in range(8)]
free4 += [sqm(M, 2) for M in L2bas]
rF4, _ = rb(free4)
P411 = np.array([0, 0, 1, 1, 1, 0, 0, 0], dtype=np.uint8)
caps = {"f291": V["f291"], "f292": V["f292"], "P41[1]": P411}
R4base = []
for q in Q2:
    for i in range(8):
        T = br(q, 2, gen(i), 1)
        for j in range(8):
            R4base.append(br(T, 3, gen(j), 1))
for T in cub3:
    for l in range(8):
        R4base.append(br(T, 3, gen(l), 1))
for j in "12":
    R4base.append(sqm(t2m(S(V["z" + j])), 2))
    R4base.append(sqm(t2m(B(V["y" + j], V["z" + j])), 2))
R4base += [sqm(q, 2) for q in Q2]
for k, v in caps.items():
    R4base.append(sqm(t2m(S(v)), 2))
rI4, _ = rb(R4base)
print("  free L4: %d I4: %d (expect 1044 963)" % (rF4, rI4))
assert (rF4, rI4) == (1044, 963)
print("  g4 range: [%d,%d] = [1044-963-28, 1044-963]"
      % (rF4 - rI4 - 28, rF4 - rI4))
print("DONE")
