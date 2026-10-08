"""C148 independent check of R5-defect-bundle (H1a/H2/H3 + full-240 cert).

Strategy: own word algebra (P0, no author code) for the parity table;
author tensor modules for tensor values but ALL ranks/residues recomputed
with an independent LOWBIT elimination (P1-P4); own trip4 algebra with fresh
seed 148 for collection/affinity identities (P5); H1a data checks (P6).

Usage: PYTHONPATH=/tmp/pylibs python3 research/2026-10-muse-involution-class/code/C148/c148_bundle_check.py
"""
import sys
import os
import io
import contextlib
import random

sys.path.insert(0, os.path.join("research", "2026-10-muse-involution-class", "code", "R5"))
with contextlib.redirect_stdout(io.StringIO()):
    import genuine_lift as G
    import robust_defect as RD

random.seed(148)

NPASS = []
def check(name, cond):
    assert cond, "FAIL: " + name
    NPASS.append(name)
    print("  ok:", name)

# ---------------- P0: word parity (no author code) ----------------
print("== P0: occurrence / exponent-sum parity ==")

def occ(word):
    d = {}
    for lift, e in word:
        d[lift] = d.get(lift, 0) + abs(e)
    return d

def expsum(word):
    d = {}
    for lift, e in word:
        d[lift] = d.get(lift, 0) + e
    return d

def inv(word):
    return [(lift, -e) for lift, e in reversed(word)]

def comm(a, b):
    return a + b + inv(a) + inv(b)

# squares: g^2 doubles everything -> even
g = [("t", 1), ("f", -1), ("t", 3)]
sq = g + g
check("square occ even", all(v % 2 == 0 for v in occ(sq).values()))
check("square exp even", all(v % 2 == 0 for v in expsum(sq).values()))

# comms: exp-sum 0; occurrences even
a, b = [("x", 1), ("y", 2)], [("y", 1), ("z", -1)]
c = comm(a, b)
check("comm exp all 0", all(v == 0 for v in expsum(c).values()))
check("comm occ even", all(v % 2 == 0 for v in occ(c).values()))
# cap comms 2/2: single-generator comm has occ 2/2
c1 = comm([("A", 1)], [("B", 1)])
check("cap comm occ 2/2", occ(c1) == {"A": 2, "B": 2})

# tame rho = f t f^-1 t^-p, p=3,5
for p in (3, 5):
    rho = [("f", 1), ("t", 1), ("f", -1), ("t", -p)]
    o, e = occ(rho), expsum(rho)
    check("tame p=%d occ f:2 t:1+p" % p, o == {"f": 2, "t": 1 + p})
    check("tame p=%d exp f:0 t:1-p" % p, e == {"f": 0, "t": 1 - p})
    check("tame p=%d even" % p,
          all(v % 2 == 0 for v in list(o.values()) + list(e.values())))
check("tame 1+p = 4/6", [1 + p for p in (3, 5)] == [4, 6])
check("tame 1-p = -2/-4", [1 - p for p in (3, 5)] == [-2, -4])

# omega = [[y,z],z]: occ Y:4/Z:6, exp 0/0
yz = comm([("Y", 1)], [("Z", 1)])
w = comm(yz, [("Z", 1)])
check("omega occ Y:4/Z:6", occ(w) == {"Y": 4, "Z": 6})
check("omega exp 0/0", expsum(w) == {"Y": 0, "Z": 0})

# Wp = y^2 [x,y] [x,z]: occ X:4/Y:4/Z:2
Wp = ([("Y", 1), ("Y", 1)] + comm([("X", 1)], [("Y", 1)])
      + comm([("X", 1)], [("Z", 1)]))
check("Wp occ X:4/Y:4/Z:2", occ(Wp) == {"X": 4, "Y": 4, "Z": 2})
check("Wp exp X:0/Y:2/Z:0", expsum(Wp) == {"X": 0, "Y": 2, "Z": 0})
check("Wp all even", all(v % 2 == 0 for v in list(occ(Wp).values()) + list(expsum(Wp).values())))

# dyadic [y,z]^2: 4/4
q = yz + yz
check("dyadic occ 4/4", occ(q) == {"Y": 4, "Z": 4})

# products of even words stay even (syzygy inheritance)
pw = Wp + w + c1 + sq
check("product inherits even occ", all(v % 2 == 0 for v in occ(pw).values()))
check("product inherits even exp", all(v % 2 == 0 for v in expsum(pw).values()))

# occ == exp (mod 2) since -1 == +1
for word in (rho, w, c, sq, Wp):
    o, e = occ(word), expsum(word)
    for k in set(o) | set(e):
        check("mod2 agree %s" % k, (o.get(k, 0) - e.get(k, 0)) % 2 == 0)
        break  # one representative per word suffices (loop below covers all)
for word in (rho, w, c, sq, Wp):
    o, e = occ(word), expsum(word)
    assert all((o.get(k, 0) - e.get(k, 0)) % 2 == 0 for k in set(o) | set(e))
print("  ok: mod-2 lemma on all table words")

# ---------------- lowbit elimination ----------------
print("== P1: ranks (lowbit) ==")

def rb_low(rows):
    bas = {}
    for v in rows:
        w = v
        while w:
            p = (w & (-w)).bit_length() - 1
            if p in bas:
                w ^= bas[p]
            else:
                bas[p] = w
                break
    return len(bas), bas

def cred_low(v, bas):
    w = v
    r = 0
    while w:
        p = (w & (-w)).bit_length() - 1
        if p in bas:
            w ^= bas[p]
        else:
            r ^= 1 << p
            w ^= 1 << p
    return r

V, br, gen = G.V, G.br, G.gen
t1v, mul, encode = G.t1_from_vec, G.mul, G.encode
L2bas, Q2 = G.L2bas, G.Q2
lifts = G.lifts

import numpy as np
E8 = np.eye(8, dtype=np.uint8)
L2sp = [G.t2_from_mat(G.S(E8[i])) for i in range(8)]
for i in range(8):
    for j in range(i + 1, 8):
        L2sp.append(G.t2_from_mat(G.B(E8[i], E8[j])))
rL2, _ = rb_low(L2sp)
rR2, _ = rb_low(Q2)
check("L2=36 R2=21", rL2 == 36 and rR2 == 21)
free3 = [br(M, 2, gen(c), 1) for M in L2sp for c in range(8)]
rFL3, _ = rb_low(free3)
R3rows = [br(q, 2, gen(i), 1) for q in Q2 for i in range(8)] + G.cub3
rI3l, bI3l = rb_low(R3rows)
check("L3=168 I3=142", rFL3 == 168 and rI3l == 142)
# L4/I4 via author's row constructors is heavy; use author's I4 row list
# (RD.bI4 values) but re-rank with lowbit, plus free-L4 rows from G
free4 = [br(T, 3, gen(l), 1) for T in free3 for l in range(8)]
free4 += [mul(M, 2, M, 2) for M in L2sp]
rF4, _ = rb_low(free4)
check("free L4=1044", rF4 == 1044)
rI4l, bI4l = rb_low(list(RD.bI4.values()))
check("I4=963", rI4l == 963)
# [I3,L1] in I4 and [R2,L2] in I4 (folding)
_, bL3f = rb_low(free3)
L3b = list(bL3f.values())
bad = sum(1 for T in R3rows for l in range(8) if cred_low(br(T, 3, gen(l), 1), bI4l) != 0)
check("[R3,L1] in I4 (folding target)", bad == 0)
bad2 = sum(1 for r in G.R2bas for t in L2bas if cred_low(br(r, 2, t, 2), bI4l) != 0)
check("[R2,L2] in I4 756/756", bad2 == 0)

print("== P2: syzygy kernel 28 (lowbit nullspace) ==")
# kernel of F2^170 -> L3 (sum to 0 in L3, not mod I3)
basis = {}
ker = []
for e, r in enumerate(R3rows):
    w, cc = r, 1 << e
    while w:
        lb = (w & (-w)).bit_length() - 1
        if lb in basis:
            w ^= basis[lb][0]
            cc ^= basis[lb][1]
        else:
            basis[lb] = (w, cc)
            break
    if w == 0:
        ker.append(cc)
check("kernel dim 28", len(ker) == 28)
for cc in ker:
    s = 0
    for r in range(170):
        if (cc >> r) & 1:
            s ^= R3rows[r]
    check("kernel vec verifies", s == 0)
    break
for cc in ker:
    s = 0
    for r in range(170):
        if (cc >> r) & 1:
            s ^= R3rows[r]
    assert s == 0
print("  ok: all 28 kernel vecs verify")
# omega slots vacuous?
om_used = sum(1 for cc in ker if (cc >> 168) & 3)
print("  omega-using kernel vecs: %d (expect 0 in this basis)" % om_used)

print("== P3: model 4, LV(R2)=0, TOTALs 6/37 (lowbit) ==")
rM, _ = rb_low(list(bI4l.values()) + list(RD.model_corrs))
check("model span 4", rM - rI4l == 4)
# LV(R2): express each R2 basis vec in L2bas coords, apply RD.lv_s
def coords_L2bas(vec):
    aug = {}
    for j, b in enumerate(L2bas):
        w = (b << 36) | (1 << j)
        while w:
            pp = w.bit_length() - 1
            if pp in aug:
                w ^= aug[pp]
            else:
                aug[pp] = w
                break
    w = vec << 36
    while w:
        pp = w.bit_length() - 1
        if pp in aug:
            w ^= aug[pp]
        else:
            break
    assert w >> 36 == 0
    return w & ((1 << 36) - 1)

bad = tot = 0
for s in range(28):
    for kk in lifts:
        for r in G.R2bas:
            cc = coords_L2bas(r)
            acc = 0
            for j in range(36):
                if (cc >> j) & 1:
                    acc ^= RD.lv_s(s, kk, j)
            tot += 1
            if cred_low(acc, bI4l) != 0:
                bad += 1
check("LV(R2)=0 0/9408", bad == 0 and tot == 9408)
# TOTAL_214: rebuild kerM/T0 with lowbit residues
Ssel = RD.Ssel
keys = [(kk, a) for kk in lifts for a in range(15)]
M1 = {(kk, a): G.M[kk][Ssel[a]] for kk in lifts for a in range(15)}
resM = [cred_low(M1[k], bI3l) for k in keys]
basis = {}
kerM = []
for e, r in enumerate(resM):
    w, cc = r, 1 << e
    for p in sorted(basis):
        if (w >> p) & 1:
            w ^= basis[p][0]
            cc ^= basis[p][1]
    if w == 0:
        kerM.append(cc)
    else:
        lb = (w & (-w)).bit_length() - 1
        basis[lb] = (w, cc)
check("kerM 214", len(kerM) == 214)
target = cred_low(G.C1 ^ G.K, bI3l)
w, T0 = target, 0
for p in sorted(basis):
    if (w >> p) & 1:
        w ^= basis[p][0]
        T0 ^= basis[p][1]
check("T0 solves cut", w == 0)
tot_vecs = list(RD.model_corrs)
for s in range(28):
    acc = 0
    for e in range(240):
        if (T0 >> e) & 1:
            kk, a = keys[e]
            acc ^= RD.lv_s(s, kk, Ssel[a])
    tot_vecs.append(acc)
    for kv in kerM:
        acc = 0
        e = 0
        k = kv
        while k:
            if k & 1:
                kk, a = keys[e]
                acc ^= RD.lv_s(s, kk, Ssel[a])
            e += 1
            k >>= 1
        tot_vecs.append(acc)
rT, bTl = rb_low(list(bI4l.values()) + tot_vecs)
check("TOTAL_214 = 6", rT - rI4l == 6)
full = list(RD.model_corrs)
for s in range(28):
    for kk in lifts:
        for a in range(15):
            full.append(RD.lv_s(s, kk, Ssel[a]))
rF, bFl = rb_low(list(bI4l.values()) + full)
check("TOTAL_full240 = 37", rF - rI4l == 37)
# subset
out = sum(1 for v in tot_vecs if cred_low(v, bFl) != 0)
check("TOTAL_214 subset full240", out == 0)

print("== P4: ad3 escape + witness + functional (lowbit) ==")
L3rows = [br(M, 2, gen(c), 1) for M in L2sp for c in range(8)]
for cnm in ["c1", "c2"]:
    W = t1v(V[cnm])
    adv = [br(T, 3, W, 1) for T in L3rows]
    ra = rb_low(list(bI4l.values()) + adv)[0] - rI4l
    escT = rb_low(list(bTl.values()) + adv)[0] - rT
    escF = rb_low(list(bFl.values()) + adv)[0] - rF
    nwT = sum(1 for a in adv if cred_low(a, bTl) != 0)
    nwF = sum(1 for a in adv if cred_low(a, bFl) != 0)
    print("  %s: ad3=%d escT=%d escF=%d witT=%d witF=%d" % (cnm, ra, escT, escF, nwT, nwF))
    check("%s ad3 18 esc 18/18 wit 192" % cnm, ra == 18 and escT == 18 and escF == 18 and nwT == 192 and nwF == 192)
    check("%s witness row1 misses both" % cnm,
          cred_low(adv[1], bTl) != 0 and cred_low(adv[1], bFl) != 0)
# functional existence (lowbit analogue)
W1 = t1v(V["c1"])
adv1 = [br(T, 3, W1, 1) for T in L3rows]
r0 = next(rr for rr in (cred_low(a, bFl) for a in adv1) if rr != 0)
p = (r0 & (-r0)).bit_length() - 1
lam = lambda x: (cred_low(x, bFl) >> p) & 1
check("full240 functional exists", lam(adv1[1]) in (0, 1) and all(lam(v) == 0 for v in bFl.values()))
# find a witness with lam=1
found = any(lam(a) == 1 for a in adv1 if cred_low(a, bFl) != 0)
check("functional hits some witness", found)

print("== P5: trip identities + Fpin/K (fresh seed) ==")

def gmul4(a, b):
    a1, a2, a3, a4 = a
    b1, b2, b3, b4 = b
    return (a1 ^ b1,
            a2 ^ b2 ^ mul(a1, 1, b1, 1),
            a3 ^ b3 ^ mul(a1, 1, b2, 2) ^ mul(a2, 2, b1, 1),
            a4 ^ b4 ^ mul(a1, 1, b3, 3) ^ mul(a3, 3, b1, 1)
            ^ mul(a2, 2, b2, 2))

def ginv4(a):
    a1, a2, a3, a4 = a
    a12 = mul(a1, 1, a1, 1)
    return (a1, a2 ^ a12,
            a3 ^ mul(a1, 1, a2, 2) ^ mul(a2, 2, a1, 1)
            ^ mul(a12, 2, a1, 1),
            a4 ^ mul(a1, 1, a3, 3) ^ mul(a3, 3, a1, 1)
            ^ mul(a2, 2, a2, 2) ^ mul(a12, 2, a2, 2)
            ^ mul(mul(a1, 1, a2, 2), 3, a1, 1)
            ^ mul(mul(a2, 2, a1, 1), 3, a1, 1)
            ^ mul(mul(a12, 2, a1, 1), 3, a1, 1))

def gcomm4(a, b):
    return gmul4(gmul4(a, b), gmul4(ginv4(a), ginv4(b)))

# ([A,B])_3 = [(A)_2,V_B] for A in D2 (bundle H2(ii) claim)
n3 = 0
for t in range(10):
    A = (0, random.getrandbits(64), random.getrandbits(512), random.getrandbits(4096))
    B = (random.getrandbits(8), random.getrandbits(64), random.getrandbits(512), random.getrandbits(4096))
    got = gcomm4(A, B)[2]
    want = br(A[1], 2, B[0], 1)
    if got == want:
        n3 += 1
check("deg3 commutator formula 10/10", n3 == 10)

# master ([A,B])_4 formula (bundle H2(iii))
n4 = 0
for t in range(10):
    A = (0, random.getrandbits(64), random.getrandbits(512), random.getrandbits(4096))
    B = (random.getrandbits(8), random.getrandbits(64), random.getrandbits(512), random.getrandbits(4096))
    got = gcomm4(A, B)[3]
    want = (br(A[2], 3, B[0], 1) ^ br(A[1], 2, B[1], 2)
            ^ mul(br(A[1], 2, B[0], 1), 3, B[0], 1))
    if got == want:
        n4 += 1
check("master deg4 formula 10/10", n4 == 10)

# E-identity ([A,x])_4 = [(A)_3,X]+[(A)_2,X]X, no (A)_4 term
ne = 0
for t in range(10):
    A = (0, random.getrandbits(64), random.getrandbits(512), random.getrandbits(4096))
    x = random.getrandbits(8)
    X = x  # V_B for B=(x,0,0,0)? use B with only deg1
    B = (x, 0, 0, 0)
    got = gcomm4(A, B)[3]
    want = br(A[2], 3, x, 1) ^ mul(br(A[1], 2, x, 1), 3, x, 1)
    if got == want:
        ne += 1
check("E-identity 10/10", ne == 10)

# a4-cancellation: commutator deg4 independent of A4
na = 0
for t in range(10):
    A1, A2v, A3v = 0, random.getrandbits(64), random.getrandbits(512)
    B = (random.getrandbits(8), random.getrandbits(64), 0, 0)
    c1 = gcomm4((A1, A2v, A3v, random.getrandbits(4096)), B)[3]
    c2 = gcomm4((A1, A2v, A3v, random.getrandbits(4096)), B)[3]
    if c1 == c2:
        na += 1
check("a4-cancel 10/10", na == 10)

# Fpin/K: LVa outside I3, [LVa,X] outside I4 8/8
G_LVa = G.Fpin ^ G.K
check("LVa outside I3", cred_low(G_LVa, bI3l) != 0)
nout = sum(1 for l in range(8) if cred_low(br(G_LVa, 3, gen(l), 1), bI4l) != 0)
check("[LVa,X] outside I4 8/8", nout == 8)
# offsets v_s at p2 syzygies land in both TOTALs
# find p2 syzygies: kernel vecs using rho_p2 slots in AUTHOR's kernel
# RD.ker is author's kernel; qlabel per 8-block
p2s = []
for s, cc in enumerate(RD.ker):
    uses = False
    for k in range(168):
        if (cc >> k) & 1 and RD.qlabel[k // 8] == "rho_p2":
            uses = True
    if uses:
        p2s.append(s)
print("  p2 syzygies:", p2s)
assert len(p2s) == 4
for s in p2s:
    cc = RD.ker[s]
    vs = 0
    for k in range(168):
        if (cc >> k) & 1 and RD.qlabel[k // 8] == "rho_p2":
            vs ^= br(G_LVa, 3, gen(k % 8), 1)
    check("v_%d in TOTAL_214" % s, cred_low(vs, bTl) == 0)
    check("v_%d in TOTAL_full240" % s, cred_low(vs, bFl) == 0)
# repaired K-model dims + miss survives
Kcorrs = []
for s, cc in enumerate(RD.ker):
    t = RD.model_corrs[s]
    vs = 0
    for k in range(168):
        if (cc >> k) & 1 and RD.qlabel[k // 8] == "rho_p2":
            vs ^= br(G_LVa, 3, gen(k % 8), 1)
    Kcorrs.append(t ^ vs)  # strip Fpin->K at p2 slots
rK = rb_low(list(bI4l.values()) + Kcorrs)[0] - rI4l
print("  K-model span mod I4: %d" % rK)
# K-model TOTALs: A-restricted (model+T0+ker with K base) and full240
Ktots = list(Kcorrs)
for s in range(28):
    acc = 0
    for e in range(240):
        if (T0 >> e) & 1:
            kk, a = keys[e]
            acc ^= RD.lv_s(s, kk, Ssel[a])
    Ktots.append(acc)
    for kv in kerM:
        acc = 0
        e = 0
        k = kv
        while k:
            if k & 1:
                kk, a = keys[e]
                acc ^= RD.lv_s(s, kk, Ssel[a])
            e += 1
            k >>= 1
        Ktots.append(acc)
rKT, bKTl = rb_low(list(bI4l.values()) + Ktots)
print("  K-model TOTAL_214: %d" % (rKT - rI4l))
Kfull = list(Kcorrs)
for s in range(28):
    for kk in lifts:
        for a in range(15):
            Kfull.append(RD.lv_s(s, kk, Ssel[a]))
rKF, bKFl = rb_low(list(bI4l.values()) + Kfull)
print("  K-model TOTAL_full240: %d" % (rKF - rI4l))
for cnm in ["c1", "c2"]:
    W = t1v(V[cnm])
    adv = [br(T, 3, W, 1) for T in L3rows]
    escKT = rb_low(list(bKTl.values()) + adv)[0] - rKT
    escKF = rb_low(list(bKFl.values()) + adv)[0] - rKF
    check("%s K-model miss survives" % cnm, escKT == 18 and escKF == 18)

print("== P6: H1a data checks ==")
# (Wp)_2 == deminit(2) recomputed from ARB trips
Wp_trip = G.gpow3(G.ARB["y2"], 2)
Wp_trip = G.emul(Wp_trip, G.gcomm3(G.ARB["x2"], G.ARB["y2"]))
Wp_trip = G.emul(Wp_trip, G.gcomm3(G.ARB["x2"], G.ARB["z2"]))
wp2 = 0
for m in G.deg_part(Wp_trip, 2):
    wp2 ^= G.encode(m)
check("(Wp)_2 == deminit(2)", wp2 == G.deminit("2"))
# NOTE: K need not be Lie (Wp not in D3); no K-in-L3 assertion.
# LV_Wp == LV_r as MAPS (same formula; conclusion via C116 lemma, not this)
Xv2, Yv2, Zv2 = t1v(V["x2"]), t1v(V["y2"]), t1v(V["z2"])
lvwx = [br(fb, 2, Yv2, 1) ^ br(fb, 2, Zv2, 1) for fb in L2bas]
cx2, cy2, cz2 = G.r2_cross_cols((V["x2"], V["y2"], V["z2"]))
check("LV_Wp == LV_r lists", lvwx == cx2)

print("ALL PASS (%d checks)" % len(NPASS))
