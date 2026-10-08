"""R5: lifting-defect preliminaries from recorded (initials-only) data.

(i)   ker(ad2), ad2 = [., c1]: gr2 -> gr3 (D2-sources for lifting defect).
(ii)  [L3, c] mod I4 rank, c = c1, c2 (D3-source compatibility: 0 kills D3).
(iii) 28 degree-3 syzygies + which rho_i they involve (R4 position minimization).
(iv)  rank [R2, L1] in L3 (mildness relation count: 142 => cubics dependent).

Usage: .venv/bin/python research/2026-10-muse-involution-class/code/R5/liftdefect.py
"""
import sys
import os
import io
import contextlib

sys.path.insert(0, os.path.join("papers", "0.04273", "certificates"))
with contextlib.redirect_stdout(io.StringIO()):
    import numpy as np  # noqa: E402
    from lie241 import V, S, B, f2rank, n, rels, names  # noqa: E402

E = np.eye(n, dtype=np.uint8)


# ---------- tensor machinery (C3-style, big-endian bits) ----------
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
    # Full reduction: pop the lead bit; eliminate pivot bits via the basis
    # (minus its lead), keep non-pivot bits in the remainder. (A version that
    # returns at the first non-pivot lead leaves smaller pivot bits set: sound
    # for zero-tests but non-canonical residues. Fixed 2026-10-06.)
    w = v
    r = 0
    while w:
        p = w.bit_length() - 1
        w ^= (1 << p)
        if p in bas:
            w ^= (bas[p] ^ (1 << p))
        else:
            r ^= (1 << p)
    return r


Qmats = [m for m, nm in zip(rels, names) if nm != "demuskin1"]
Qnames = [nm for m, nm in zip(rels, names) if nm != "demuskin1"]
Q2 = [t2_from_mat(m) for m in Qmats]
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
_, bF4 = rank_basis(free4)
F4bas = list(bF4.values())

# R3 spanning set: 21x8 brackets + 2 cubics (lie241c.py)
R3rows = []
for qi, q in enumerate(Q2):
    for i in range(8):
        R3rows.append(bracket(q, 2, gen(i), 1))
for j in "12":
    M = t2_from_mat(B(V["y" + j], V["z" + j]))
    T = 0
    for l in range(8):
        if V["z" + j][l]:
            T ^= bracket(M, 2, gen(l), 1)
    R3rows.append(T)
rR3, bR3 = rank_basis(R3rows)
print("(iii/iv) R3 spanning rows: %d, rank: %d" % (len(R3rows), rR3))

# (iv) rank [R2, L1] alone
rB, _ = rank_basis(R3rows[:168])
print("(iv) rank [R2,L1] = %d (cubics %s)" %
      (rB, "dependent -> 28-gen minimal" if rB == rR3 else "add %d" % (rR3 - rB)))

# (iii) syzygies: nullspace of 170 x 512 matrix over F2 (numpy)
M = np.zeros((170, 512), dtype=np.uint8)
for r, v in enumerate(R3rows):
    for b in bits(v):
        ia = decode(b, 3)
        M[r, ia[0] * 64 + ia[1] * 8 + ia[2]] ^= 1
# nullspace via elimination on transpose (kernel of rows = left nullspace)
A = M.copy()
rows, cols = A.shape
pivrow = [-1] * cols
r = 0
for c in range(cols):
    piv = None
    for i in range(r, rows):
        if A[i, c]:
            piv = i
            break
    if piv is None:
        continue
    A[[r, piv]] = A[[piv, r]]
    for i in range(rows):
        if i != r and A[i, c]:
            A[i] ^= A[r]
    pivrow[c] = r
    r += 1
freen = [c for c in range(cols) if pivrow[c] == -1]
# left nullspace: y with y^T M = 0. row-reduced: pivot rows express...
# do elimination on M^T instead: null(M^T) directly
AT = M.T.copy()
rr, cc = AT.shape
piv2 = [-1] * cc
r = 0
for c in range(cc):
    piv = None
    for i in range(r, rr):
        if AT[i, c]:
            piv = i
            break
    if piv is None:
        continue
    AT[[r, piv]] = AT[[piv, r]]
    for i in range(rr):
        if i != r and AT[i, c]:
            AT[i] ^= AT[r]
    piv2[c] = r
    r += 1
free2 = [c for c in range(cc) if piv2[c] == -1]
print("(iii) syzygies: %d (expect 28)" % len(free2))
involved = set()
for f in free2:
    vec = np.zeros(cc, dtype=np.uint8)
    vec[f] = 1
    for c in range(cc):
        if piv2[c] >= 0 and AT[piv2[c], f]:
            vec[c] ^= 1
    for k in range(168):
        if vec[k]:
            involved.add(Qnames[k // 8])
    if vec[168] or vec[169]:
        involved.add("cubic")
print("(iii) rho_i involved in some syzygy (%d): %s" %
      (len(involved), sorted(involved)))

# (i) ker(ad2): gr2 basis = complement of R2 in free L2; ad2 images mod R3
_, bQ = rank_basis(Q2)
comp = []
cur = dict(bQ)
for m in L2sp:
    if reduce_mod(m, cur) != 0:
        comp.append(m)
        _, cur = rank_basis(list(cur.values()) + [m])
print("(i) gr2 basis: %d (expect 15)" % len(comp))
c1 = 0
for l in range(8):
    if V["c1"][l]:
        c1 ^= gen(l)
imgs = [reduce_mod(bracket(u, 2, c1, 1), bR3) for u in comp]
# kernel: coefficients e with sum e_i imgs_i = 0 in T3 (512-bit)
K = np.zeros((15, 512), dtype=np.uint8)
for i, v in enumerate(imgs):
    for b in bits(v):
        ia = decode(b, 3)
        K[i, ia[0] * 64 + ia[1] * 8 + ia[2]] ^= 1
rk = f2rank(K.copy())
print("(i) ad2 rank = %d, ker dim = %d (expect 8/7)" % (rk, 15 - rk))

# (ii) [L3, c] mod I4 (41-cap I4)
P411 = np.array([0, 0, 1, 1, 1, 0, 0, 0], dtype=np.uint8)
caps = {"f291": V["f291"], "f292": V["f292"], "P41[1]": P411}


def qpow4(vec8):
    return square(t2_from_mat(S(vec8)), 2)


def qbrk2(y, z):
    return square(t2_from_mat(B(y, z)), 2)


dyad = []
for j in "12":
    dyad.append(qpow4(V["z" + j]))
    dyad.append(qbrk2(V["y" + j], V["z" + j]))
cap4 = {k: qpow4(v) for k, v in caps.items()}
cub3 = []
for j in "12":
    M = t2_from_mat(B(V["y" + j], V["z" + j]))
    T = 0
    for l in range(8):
        if V["z" + j][l]:
            T ^= bracket(M, 2, gen(l), 1)
    cub3.append(T)
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
assert (rI4, len(F4bas)) == (963, 1044)
for cn in ["c1", "c2"]:
    c = 0
    for l in range(8):
        if V[cn][l]:
            c ^= gen(l)
    res = [bracket(T, 3, c, 1) for T in L3bas]
    rk, _ = rank_basis(list(bI4.values()) + res)
    print("(ii) %s: [L3,c] mod I4 rank = %d" % (cn, rk - rI4))
print("DONE")
