"""R5 genuine-word lift datum: coproduct fix, paradox resolution, one fiber cut.

1. Coproduct: X_i = x_i - 1 has DX_i = X_i(x)1+1(x)X_i+X_i(x)X_i, so
   1+V is group-like iff wt(V) <= 1 (single-bit = free generator itself).
   Corrects compat_gap.py section 2 ("iff V = 0", primitive convention).
2. C89 section-3 paradox word rebuilt with genuine YZ = (1+Y)(1+Z):
   paradox evaporates (non-genuine 1+Y+Z was the artifact).
3. Reduction fix: canonical residues; TRUE fiber ranks mod I4 =
   rank(I4 + fibers) - 963 (<= dim L4/I4 = 81). Reconciles compat_gap
   148-193 (non-canonical-residue absolute ranks, I4 leftovers incl.).
4. Genuine y1/y2 D2-words (realized D-quotient y^2 = 1 + recorded R2/R3):
   fiber-only constraint C1 + K + M(T') in I3, rank 26, consistency
   check; formal-r3 pin Fformal in Fpin + I3. U'-lemma: even
   exponent-sums kill degree-3-fiber dependence, so the cut is exact.

Usage: .venv/bin/python research/2026-10-muse-involution-class/code/R5/genuine_lift.py
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

# ---------------- bit-tensor helpers (big-endian) ----------------

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


def t1_from_vec(v8):
    v = 0
    for i in range(8):
        if int(v8[i]) % 2:
            v |= encode((i,))
    return v


def t2_from_mat(M):
    v = 0
    for i in range(8):
        for j in range(8):
            if M[i, j] % 2:
                v |= encode((i, j))
    return v


def arb2_bits(v8):
    v = 0
    for i in range(8):
        for j in range(i + 1, 8):
            if v8[i] and v8[j]:
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


def cred(v, bas):
    """Canonical residue: eliminate ALL lead bits, stash non-leads."""
    w = v
    r = 0
    while w:
        p = w.bit_length() - 1
        if p in bas:
            w ^= bas[p]
        else:
            r ^= 1 << p
            w ^= 1 << p
    return r


# ---------------- dict-Magnus to degree 3 ----------------

def emul(A, B, D=3):
    C = {}
    for m1 in A:
        for m2 in B:
            if len(m1) + len(m2) > D:
                continue
            m = m1 + m2
            C[m] = C.get(m, 0) ^ 1
            if C[m] == 0:
                del C[m]
    return C


def eadd(*As):
    C = {}
    for A in As:
        for m in A:
            C[m] = C.get(m, 0) ^ 1
            if C[m] == 0:
                del C[m]
    return C


def arb3(v8):
    g = {(): 1}
    for i in range(8):
        if int(v8[i]) % 2:
            g = emul(g, {(): 1, (i,): 1})
    return g


def pure3(v8):
    g = {(): 1}
    for i in range(8):
        if int(v8[i]) % 2:
            g = eadd(g, {(i,): 1})
    return g


def ginv3(g):
    one = {(): 1}
    a = {m: 1 for m in g if m != ()}
    a2 = emul(a, a)
    a3 = emul(a2, a)
    return eadd(one, a, a2, a3)


def gpow3(g, e):
    if e == 0:
        return {(): 1}
    if e < 0:
        return gpow3(ginv3(g), -e)
    r = {(): 1}
    for _ in range(e):
        r = emul(r, g)
    return r


def gcomm3(a, b):
    return emul(emul(a, b), emul(ginv3(a), ginv3(b)))


def deg_part(g, d):
    return {m: 1 for m in g if len(m) == d}


def t3_from_dict(d):
    v = 0
    for m in d:
        assert len(m) == 3
        v ^= encode(m)
    return v


def eval_rho_tame3(t, f, p):
    return emul(emul(emul(f, t), ginv3(f)), gpow3(t, -p))


# ================= 1. coproduct convention =================
print("=== 1. coproduct: 1+V group-like iff wt(V) <= 1 ===")
ok1 = True
for k in sorted(V.keys()):
    v = np.array(list(V[k]), dtype=np.uint8)
    wt = int(v.sum())
    # off-diagonal defect D = sum_{i<j} v_i v_j (e_ij + e_ji) in M8(F2)
    D = np.zeros((8, 8), dtype=np.uint8)
    for i in range(8):
        for j in range(i + 1, 8):
            if v[i] and v[j]:
                D[i, j] ^= 1
                D[j, i] ^= 1
    glike = not D.any()
    if glike != (wt <= 1):
        ok1 = False
        print("  MISMATCH", k)
print("  1+V group-like iff wt<=1 holds for all 19 vectors:", ok1)
print("  (single-bit 1+X_i is the free generator itself: genuine)")

# ================= L2/R2/L3/I3 =================
L2sp = [t2_from_mat(S(E[i])) for i in range(8)]
for i in range(8):
    for j in range(i + 1, 8):
        L2sp.append(t2_from_mat(B(E[i], E[j])))
rL2, bL2 = rb(L2sp)
L2bas = list(bL2.values())
Q2 = [t2_from_mat(m) for m, nm in zip(rels, names) if nm != "demuskin1"]
rR2, bR2 = rb(Q2)
R2bas = list(bR2.values())
print("L2 = %d, R2 = %d (expect 36, 21)" % (rL2, rR2))
free3 = [br(M, 2, gen(c), 1) for M in L2sp for c in range(8)]
rFL3, bFL3 = rb(free3)
cub3 = []
for j in "12":
    M = t2_from_mat(B(V["y" + j], V["z" + j]))
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
rI3, bI3 = rb(R3rows)
print("free L3 = %d, I3 = %d (expect 168, 142)" % (rFL3, rI3))

# ARB deg-2 sanity: product gives ARB2
okarb = True
for k in sorted(V.keys()):
    d2 = deg_part(arb3(V[k]), 2)
    v = 0
    for m in d2:
        v ^= encode(m)
    if v != arb2_bits(V[k]):
        okarb = False
print("ARB product deg-2 == ARB2 for all vectors:", okarb)

# ================= 2. paradox word, genuine vs non-genuine =================
print("=== 2. C89 paradox word ===")
gA = {(): 1, (0,): 1}
gB = {(): 1, (1,): 1}
gC = {(): 1, (2,): 1}
BCgen = emul(gB, gC)  # genuine (1+Y)(1+Z)
wgen = emul(gcomm3(gA, BCgen), emul(gcomm3(gA, gB), gcomm3(gA, gC)))
w1 = deg_part(wgen, 1)
w2 = deg_part(wgen, 2)
w3 = deg_part(wgen, 3)
inL3 = cred(t3_from_dict(w3), bFL3) == 0 if w3 else True
print("  genuine: |(w)1|=%d |(w)2|=%d (w)3 in L3: %s" % (len(w1), len(w2), inL3))
BCbad = {(): 1, (1,): 1, (2,): 1}  # non-genuine 1+Y+Z
wbad = emul(gcomm3(gA, BCbad), emul(gcomm3(gA, gB), gcomm3(gA, gC)))
b1 = deg_part(wbad, 1)
b2 = deg_part(wbad, 2)
b3 = deg_part(wbad, 3)
inL3b = cred(t3_from_dict(b3), bFL3) == 0 if b3 else True
print("  non-genuine 1+Y+Z: |(w)1|=%d |(w)2|=%d (w)3 in L3: %s (C89 artifact reproduced: %s)"
      % (len(b1), len(b2), inL3b, (len(b1) == 0 and len(b2) == 0 and not inL3b)))
print("  paradox resolved (genuine word has no D3-nonLie part):",
      len(w1) > 0 or len(w2) > 0 or inL3)

# ================= 3. reduction fix + fiber ranks =================
print("=== 3. TRUE fiber ranks mod I4 ===")
_, bL2b = rb(L2sp)
L2b = list(bL2b.values())
L3brows = [br(M, 2, gen(c), 1) for M in L2sp for c in range(8)]
_, bL3 = rb(L3brows)
L3bas = list(bL3.values())
free4 = [br(T, 3, gen(l), 1) for T in L3bas for l in range(8)]
free4 += [sqm(M, 2) for M in L2b]
rF4, _ = rb(free4)
P411 = np.array([0, 0, 1, 1, 1, 0, 0, 0], dtype=np.uint8)
caps = {"f291": V["f291"], "f292": V["f292"], "P41[1]": P411}


def qpow4(v8):
    return sqm(t2_from_mat(S(v8)), 2)


def qbrk2(y, z):
    return sqm(t2_from_mat(B(y, z)), 2)


dyad = []
for j in "12":
    dyad.append(qpow4(V["z" + j]))
    dyad.append(qbrk2(V["y" + j], V["z" + j]))
cap4 = {k: qpow4(v) for k, v in caps.items()}
R4base = []
for q in Q2:
    for i in range(8):
        T = br(q, 2, gen(i), 1)
        for j in range(8):
            R4base.append(br(T, 3, gen(j), 1))
for T in cub3:
    for l in range(8):
        R4base.append(br(T, 3, gen(l), 1))
R4base += dyad
R4base += [sqm(q, 2) for q in Q2]
three = ["f291", "f292", "P41[1]"]
I4rows = R4base + [cap4[k] for k in three]
rI4, bI4 = rb(I4rows)
print("  free L4 = %d, I4 = %d (expect 1044, 963)" % (rF4, rI4))
print("  I4 subset L4:", rb(free4 + I4rows)[0] == 1044)


def t1b(v8):
    v = 0
    for i in range(8):
        if int(v8[i]) % 2:
            v ^= gen(i)
    return v


for k in ["y1", "z1", "p31", "c1"]:
    W = t1b(V[k])
    rows = []
    for T in L2b:
        U = br(T, 2, W, 1)
        for l in range(8):
            rows.append(br(U, 3, gen(l), 1))
    inl4 = rb(free4 + rows)[0] == 1044
    truerank = rb(I4rows + rows)[0] - rI4
    print("  V=%-4s fibers in L4: %s  TRUE rank mod I4: %d (<=81: %s)"
          % (k, inl4, truerank, truerank <= 81))
print("  (compat_gap 148-193 were non-canonical-residue absolute ranks)")

# ================= 4. genuine y1/y2 words =================
print("=== 4. genuine D2-word fiber cut ===")
# identify 21 Q2
cands = {}
cands["real1"] = t2_from_mat(S(V["c1"]))
cands["real2"] = t2_from_mat(S(V["c2"]))
tame = [("t31", "p31", 3), ("t32", "p32", 3), ("t51", "p51", 5), ("t52", "p52", 5)]
for tk, pk, p in tame:
    e = t2_from_mat(B(V[tk], V[pk]))
    if ((p - 1) // 2) % 2:
        e ^= t2_from_mat(S(V[tk]))
    cands["tame_" + tk] = e


def deminit(j):
    x, y, z = V["x" + j], V["y" + j], V["z" + j]
    return (t2_from_mat(S(y)) ^ t2_from_mat(B(x, y)) ^ t2_from_mat(B(x, z)))


cands["rho_p2"] = deminit("2")
for j in "12":
    cands["x2_" + j] = t2_from_mat(S(V["x" + j]))
    cands["xy_" + j] = t2_from_mat(B(V["x" + j], V["y" + j]))
    cands["xz_" + j] = t2_from_mat(B(V["x" + j], V["z" + j]))
for tk, pk, _ in tame:
    cands["tau2_" + tk] = t2_from_mat(S(V[tk]))
    cands["phi2_" + pk] = t2_from_mat(S(V[pk]))
assert len(cands) == 21
qlabel = []
for q in Q2:
    hits = [kk for kk, vv in cands.items() if vv == q]
    assert len(hits) == 1
    qlabel.append(hits[0])
print("  21 Q2 identified: True")
# solve S(y1) in R2
ya = t2_from_mat(S(V["y1"]))
aug = {}
for i, q in enumerate(Q2):
    w = (q << 21) | (1 << i)
    while w:
        pp = w.bit_length() - 1
        if pp in aug:
            w ^= aug[pp]
        else:
            aug[pp] = w
            break
w = ya << 21
while w:
    pp = w.bit_length() - 1
    if pp in aug:
        w ^= aug[pp]
    else:
        break
assert w >> 21 == 0
coef = w & ((1 << 21) - 1)
used = [qlabel[i] for i in range(21) if (coef >> i) & 1]
print("  y1bar^2 uses %d initials: %s" % (len(used), sorted(used)))
assert len(used) == 9 and "rho_p2" in used

# genuine relator words on ARB lifts (all used labels except rho_p2: known shapes)
ARB = {kk: arb3(vv) for kk, vv in
       list(V.items()) + [("c1", V["c1"]), ("c2", V["c2"])]}
tame_p = {"t31": 3, "t32": 3, "t51": 5, "t52": 5}
tame_phi = {"t31": "p31", "t32": "p32", "t51": "p51", "t52": "p52"}


def rho_arb(lab):
    if lab == "real1":
        return gpow3(ARB["c1"], 2)
    if lab == "real2":
        return gpow3(ARB["c2"], 2)
    if lab.startswith("tame_"):
        tk = lab[5:]
        return eval_rho_tame3(ARB[tk], ARB[tame_phi[tk]], tame_p[tk])
    if lab.startswith("xy_"):
        jj = lab[3:]
        return gcomm3(ARB["x" + jj], ARB["y" + jj])
    if lab.startswith("xz_"):
        jj = lab[3:]
        return gcomm3(ARB["x" + jj], ARB["z" + jj])
    if lab.startswith("x2_"):
        jj = lab[3:]
        return gpow3(ARB["x" + jj], 2)
    if lab.startswith("tau2_"):
        return gpow3(ARB[lab[5:]], 2)
    if lab.startswith("phi2_"):
        return gpow3(ARB[lab[5:]], 2)
    raise AssertionError(lab)


# C1 = (y1hat^2)_3 + sum_{used != p2} (rho_i)_3, genuine ARB base
C1 = t3_from_dict(deg_part(gpow3(ARB["y1"], 2), 3))
for lab in used:
    if lab == "rho_p2":
        continue
    C1 ^= t3_from_dict(deg_part(rho_arb(lab), 3))
# K = (Wp)_3 at p2, Wp = Y^2 [X,Y] [X,Z], genuine ARB base
Wp = emul(gpow3(ARB["y2"], 2),
          emul(gcomm3(ARB["x2"], ARB["y2"]), gcomm3(ARB["x2"], ARB["z2"])))
assert len(deg_part(Wp, 1)) == 0
K = t3_from_dict(deg_part(Wp, 3))
# (Wp)_2 must equal deminit(2) (depends on deg-1 only)
wp2 = 0
for m in deg_part(Wp, 2):
    wp2 ^= encode(m)
print("  (Wp)_2 == deminit(2):", wp2 == deminit("2"))
print("  C1 in L3:", cred(C1, bFL3) == 0, " K in L3:", cred(K, bFL3) == 0)
print("  (K need not be Lie: Wp not in D3; C1+K+Fformal+M lands in I3)")

# fiber map M (base-independent linearization; ARB-base perturbation for tame)
lifts = ["i1", "i2", "t31", "p31", "t32", "p32", "t51", "p51", "t52", "p52",
         "x1", "y1", "z1", "x2", "y2", "z2"]
lvec = {"i1": V["c1"], "i2": V["c2"]}
for kk in lifts[2:]:
    lvec[kk] = V[kk]


def gmul_trip(a, b):
    a1, a2, a3 = a
    b1, b2, b3 = b
    return (a1 ^ b1,
            a2 ^ b2 ^ mul(a1, 1, b1, 1),
            a3 ^ b3 ^ mul(a1, 1, b2, 2) ^ mul(a2, 2, b1, 1))


def ginv_trip(a):
    a1, a2, a3 = a
    n1 = a1
    n2 = a2 ^ mul(a1, 1, a1, 1)
    n3 = (a3 ^ mul(a1, 1, a2, 2) ^ mul(a2, 2, a1, 1)
          ^ mul(mul(a1, 1, a1, 1), 2, a1, 1))
    return (n1, n2, n3)


def gpow_trip(a, e):
    if e == 0:
        return (0, 0, 0)
    if e < 0:
        return gpow_trip(ginv_trip(a), -e)
    r = (0, 0, 0)
    for _ in range(e):
        r = gmul_trip(r, a)
    return r


def arb_trip(v8):
    d = arb3(v8)
    t1, t2, t3 = 0, 0, 0
    for m in d:
        if len(m) == 1:
            t1 ^= encode(m)
        elif len(m) == 2:
            t2 ^= encode(m)
        elif len(m) == 3:
            t3 ^= encode(m)
    return (t1, t2, t3)


def eval_rho_trip(t, f, p):
    return gmul_trip(gmul_trip(gmul_trip(f, t), ginv_trip(f)), gpow_trip(t, -p))


tame_cross = {}
for tk in tame_p:
    pk = tame_phi[tk]
    p = tame_p[tk]
    t0, f0 = arb_trip(V[tk]), arb_trip(V[pk])
    base3 = eval_rho_trip(t0, f0, p)[2]
    ct, cp = [], []
    for fb in L2bas:
        tp = (t0[0], t0[1] ^ fb, t0[2])
        ct.append(eval_rho_trip(tp, f0, p)[2] ^ base3)
        fp = (f0[0], f0[1] ^ fb, f0[2])
        cp.append(eval_rho_trip(t0, fp, p)[2] ^ base3)
    tame_cross[tk] = (ct, cp)


def sq_cross_col(vec, fb):
    return br(t1_from_vec(vec), 1, fb, 2)


def comm_cross_cols(vecA, vecB):
    A1, B1 = t1_from_vec(vecA), t1_from_vec(vecB)
    return ([br(fb, 2, B1, 1) for fb in L2bas],
            [br(A1, 1, fb, 2) for fb in L2bas])


def r2_cross_cols(vecs):
    Xv, Yv, Zv = (t1_from_vec(v) for v in vecs)
    cx = [br(fb, 2, Yv, 1) ^ br(fb, 2, Zv, 1) for fb in L2bas]
    cy = [br(Yv, 1, fb, 2) ^ br(Xv, 1, fb, 2) for fb in L2bas]
    cz = [br(Xv, 1, fb, 2) for fb in L2bas]
    return cx, cy, cz


# LV_Wp == LV_r check (fiber cancellation in y2-word)
Xv2, Yv2 = t1_from_vec(V["x2"]), t1_from_vec(V["y2"])
Zv2 = t1_from_vec(V["z2"])
lvwx = [br(fb, 2, Yv2, 1) ^ br(fb, 2, Zv2, 1) for fb in L2bas]
lvwy = [br(Yv2, 1, fb, 2) ^ br(Xv2, 1, fb, 2) for fb in L2bas]
lvwz = [br(Xv2, 1, fb, 2) for fb in L2bas]
cx2, cy2, cz2 = r2_cross_cols((V["x2"], V["y2"], V["z2"]))
print("  LV_Wp == LV_r (y2 fiber cancellation):",
      lvwx == cx2 and lvwy == cy2 and lvwz == cz2)

M = {kk: [0] * 36 for kk in lifts}
for j, fb in enumerate(L2bas):
    M["y1"][j] ^= sq_cross_col(V["y1"], fb)
for i in range(21):
    if not (coef >> i) & 1:
        continue
    lab = qlabel[i]
    if lab == "real1":
        for j, fb in enumerate(L2bas):
            M["i1"][j] ^= sq_cross_col(V["c1"], fb)
    elif lab == "real2":
        for j, fb in enumerate(L2bas):
            M["i2"][j] ^= sq_cross_col(V["c2"], fb)
    elif lab.startswith("tame_"):
        tk = lab[5:]
        ct, cp = tame_cross[tk]
        for j in range(36):
            M[tk][j] ^= ct[j]
            M[tame_phi[tk]][j] ^= cp[j]
    elif lab == "rho_p2":
        cx, cy, cz = r2_cross_cols((V["x2"], V["y2"], V["z2"]))
        for j in range(36):
            M["x2"][j] ^= cx[j]
            M["y2"][j] ^= cy[j]
            M["z2"][j] ^= cz[j]
    elif lab.startswith("x2_"):
        jj = lab[3:]
        for j, fb in enumerate(L2bas):
            M["x" + jj][j] ^= sq_cross_col(V["x" + jj], fb)
    elif lab.startswith("xy_"):
        jj = lab[3:]
        ca, cb = comm_cross_cols(V["x" + jj], V["y" + jj])
        for j in range(36):
            M["x" + jj][j] ^= ca[j]
            M["y" + jj][j] ^= cb[j]
    elif lab.startswith("xz_"):
        jj = lab[3:]
        ca, cb = comm_cross_cols(V["x" + jj], V["z" + jj])
        for j in range(36):
            M["x" + jj][j] ^= ca[j]
            M["z" + jj][j] ^= cb[j]
    elif lab.startswith("tau2_"):
        tk = lab[5:]
        for j, fb in enumerate(L2bas):
            M[tk][j] ^= sq_cross_col(V[tk], fb)
    elif lab.startswith("phi2_"):
        pk = lab[5:]
        for j, fb in enumerate(L2bas):
            M[pk][j] ^= sq_cross_col(V[pk], fb)
    else:
        raise AssertionError(lab)

Mcols = []
for kk in lifts:
    Mcols += M[kk]
rkM = rb(list(bI3.values()) + Mcols)[0] - rI3
print("  fiber-map rank mod I3:", rkM, "(expect 26)")


def coords_in_L2bas(vec):
    aug2 = {}
    for j, b in enumerate(L2bas):
        w = (b << 36) | (1 << j)
        while w:
            pp = w.bit_length() - 1
            if pp in aug2:
                w ^= aug2[pp]
            else:
                aug2[pp] = w
                break
    w = vec << 36
    while w:
        pp = w.bit_length() - 1
        if pp in aug2:
            w ^= aug2[pp]
        else:
            break
    assert w >> 36 == 0
    return w & ((1 << 36) - 1)


bad = 0
for kk in lifts:
    for r in R2bas:
        cc = coords_in_L2bas(r)
        acc = 0
        for j in range(36):
            if (cc >> j) & 1:
                acc ^= M[kk][j]
        if cred(acc, bI3) != 0:
            bad += 1
print("  R2-kernel violations: %d / 336 (expect 0)" % bad)

# consistency: C1 + K in I3 + Im(M)?
base_rank = rb(list(bI3.values()) + Mcols)[0]
full_rank = rb(list(bI3.values()) + Mcols + [C1 ^ K])[0]
print("  C1+K consistent with Im(M) mod I3:", full_rank == base_rank)
print("  => fiber cut 240 -> %d (affine, unconditional on paper deg<=3)"
      % (240 - rkM))

# formal-r3 pin: Fpin = K + LV_r(ARB2@p2); pushforward image
ay2, az2 = arb2_bits(V["y2"]), arb2_bits(V["z2"])
LVa = (br(Yv2, 1, ay2, 2) ^ br(Xv2, 1, ay2, 2)) ^ br(Xv2, 1, az2, 2)
Fpin = K ^ LVa
fmon = []
for a in range(3):
    for b in range(3):
        for c in range(3):
            vv = [V["x2"], V["y2"], V["z2"]]
            t = 0
            for l in range(8):
                for m in range(8):
                    for nn in range(8):
                        if vv[a][l] and vv[b][m] and vv[c][nn]:
                            t ^= encode((l, m, nn))
            fmon.append(t)
rkF = rb(fmon)[0]
print("  formal-27 pushforward rank:", rkF)


def ev_bracket3(b, W, vecs):
    U = {"XY": (vecs[0], vecs[1]), "XZ": (vecs[0], vecs[2]),
         "YZ": (vecs[1], vecs[2])}[b]
    inner = t2_from_mat(B(U[0], U[1]))
    T = 0
    for ell in range(8):
        if vecs[W][ell]:
            T ^= br(inner, 2, gen(ell), 1)
    return T


nine = [ev_bracket3(b, W, (V["x2"], V["y2"], V["z2"]))
        for b in ("XY", "XZ", "YZ") for W in (0, 1, 2)]
print("  nine nested in I3:", all(cred(t, bI3) == 0 for t in nine))
fr = rb(list(bI3.values()) + fmon)[0] - rI3
fr2 = rb(list(bI3.values()) + fmon + [Fpin])[0] - rI3
print("  formal-image rank mod I3: %d; Fpin consistent: %s"
      % (fr, fr2 == fr))
print("  => formal-r3 cut 27 -> %d" % (27 - fr))
print("DONE")
