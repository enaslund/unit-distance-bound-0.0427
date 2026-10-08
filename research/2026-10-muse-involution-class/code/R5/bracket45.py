"""R5: initial-ideal bracket [., c]: L4/I4 -> L5/I5 for the 41-cap tower group.

Rebuilds C3's I4 (41-cap: base + f291, f292, P41[1]) and I5 = [I4, L1],
then computes the rank of u -> [u, c] mod I5 over a quotient basis of L4/I4,
for c = c1 and c2.

Logic (see R5-signature-threshold notes): I_d subset R_d, so
  - rank 0 PROVES the true bracket gr4 -> gr5 is zero, i.e. [D4,iota] ⊂ D6
    (every lift u in L4 has [u,c] in I5 ⊂ R5), killing the level-4 route;
  - rank > 0 is COMPATIBLE with growth but proves nothing (u may lie in
    R4, or [u,c] in R5 outside I5); proof would need exact R4/R5 (blocked
    on unrecorded relator lifts, C16).

Usage: .venv/bin/python research/2026-10-muse-involution-class/code/R5/bracket45.py
"""
import sys
import os
import io
import contextlib

sys.path.insert(0, os.path.join("papers", "0.04273", "certificates"))
with contextlib.redirect_stdout(io.StringIO()):
    import numpy as np  # noqa: E402
    from lie241 import V, S, B, rels, names, n  # noqa: E402


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
    out = []
    while v:
        b = v.bit_length() - 1
        out.append(b)
        v ^= (1 << b)
    return out


def t2_from_mat(M):
    v = 0
    for i in range(8):
        for j in range(8):
            if M[i, j] % 2:
                v |= encode((i, j))
    return v


def mul(A, da, B_, db):
    v = 0
    for ba in bits(A):
        ia = decode(ba, da)
        for bb in bits(B_):
            ib = decode(bb, db)
            v ^= encode(tuple(ia + ib))
    return v


def gen(l):
    return encode((l,))


def bracket(A, da, B_, db):
    return mul(A, da, B_, db) ^ mul(B_, db, A, da)


def square(A, da):
    return mul(A, da, A, da)


def rank_basis(rows):
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


def reduce_mod(v, bas):
    w = v
    while w:
        p = w.bit_length() - 1
        if p in bas:
            w ^= bas[p]
        else:
            return w
    return 0


E = np.eye(n, dtype=np.uint8)
Qmats = [m for m, nm in zip(rels, names) if nm != "demuskin1"]
Q2 = [t2_from_mat(m) for m in Qmats]

# free L2/L3/L4
L2sp = [t2_from_mat(S(E[i])) for i in range(8)]
for i in range(8):
    for j in range(i + 1, 8):
        L2sp.append(t2_from_mat(B(E[i], E[j])))
_, bL2 = rank_basis(L2sp)
L2bas = list(bL2.values())
free3 = [bracket(M, 2, gen(c), 1) for M in L2sp for c in range(8)]
_, b3 = rank_basis(free3)
L3bas = list(b3.values())
free4 = [bracket(T, 3, gen(l), 1) for T in L3bas for l in range(8)]
free4 += [square(M, 2) for M in L2bas]
r4f, bF4 = rank_basis(free4)
print("free L4 =", r4f)
assert r4f == 1044

# I4, 41-cap set {f291, f292, P41[1]}
P411 = np.array([0, 0, 1, 1, 1, 0, 0, 0], dtype=np.uint8)
caps = {"f291": V["f291"], "f292": V["f292"], "P41[1]": P411}
cub3 = []
for j in "12":
    M = t2_from_mat(B(V["y" + j], V["z" + j]))
    T = 0
    for l in range(8):
        if V["z" + j][l]:
            T ^= bracket(M, 2, gen(l), 1)
    cub3.append(T)


def qpow4(vec8):
    return square(t2_from_mat(S(vec8)), 2)


def qbrk2(y, z):
    return square(t2_from_mat(B(y, z)), 2)


dyad = []
for j in "12":
    dyad.append(qpow4(V["z" + j]))
    dyad.append(qbrk2(V["y" + j], V["z" + j]))
cap4 = {k: qpow4(v) for k, v in caps.items()}
R4base = []
for q in Q2:
    for i in range(8):
        T = bracket(q, 2, gen(i), 1)
        for j in range(8):
            R4base.append(bracket(T, 3, gen(j), 1))
for T in cub3:
    for l in range(8):
        R4base.append(bracket(T, 3, gen(l), 1))
R4base += dyad
R4base += [square(q, 2) for q in Q2]
three = ["f291", "f292", "P41[1]"]
rI4, bI4 = rank_basis(R4base + [cap4[k] for k in three])
print("I4 41-cap rank =", rI4, "-> L4/I4 =", r4f - rI4)
assert rI4 == 963 and r4f - rI4 == 81

# quotient basis of L4/I4
F4bas = list(bF4.values())
Q4 = []
for u in F4bas:
    if reduce_mod(u, bI4) != 0:
        Q4.append(u)
        # extend basis with the residue's pivot implicitly: re-add u
        _, bI4 = rank_basis(list(bI4.values()) + [u])
print("quotient basis size =", len(Q4))
assert len(Q4) == 81

# I5 = [I4, L1]
_, bI4b = rank_basis(R4base + [cap4[k] for k in three])
B4 = list(bI4b.values())
R5 = [bracket(u, 4, gen(l), 1) for u in B4 for l in range(8)]
rI5, bI5 = rank_basis(R5)
print("I5 41-cap rank =", rI5)
assert rI5 == 6353

# bracket ranks for c1, c2
for cn in ["c1", "c2"]:
    c = 0
    for l in range(8):
        if V[cn][l]:
            c ^= gen(l)
    imgs = [bracket(u, 4, c, 1) for u in Q4]
    rk, _ = rank_basis(list(bI5.values()) + imgs)
    print("%s: bracket rank mod I5 = %d" % (cn, rk - rI5))
print("DONE")
