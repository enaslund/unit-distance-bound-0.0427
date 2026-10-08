"""R5 collection check: complete collection through degree 4 + lift terms.

D1: master formula ([A,B])_4 = [(A)_3,V_B]+[(A)_2,(B)_2]+[(A)_2,V_B]V_B
    EXACT on random A in D2, B in D1 (full random higher parts).
D2: [R2,L2] subset I4, 756/756 (folding computationally).
D3: relator-conjugate formula EXACT per relator type (TRUE-like lifts
    with random T'/U'/T4 + random conjugator with D2/D3/D4 parts).
D4: cubic-conjugate (w^g)_4 = (w)_4 + [(w)_3,V_g] EXACT + [..,V] in I4.
D5: quartic-conjugate (Q^g)_4 = (Q)_4 EXACT (dyadic + cap).

Usage: .venv/bin/python research/2026-10-muse-involution-class/code/R5/collection_check.py
"""
import sys
import os
import io
import contextlib
import random

sys.path.insert(0, os.path.join("research", "2026-10-muse-involution-class", "code", "R5"))
with contextlib.redirect_stdout(io.StringIO()):
    import genuine_lift as G  # noqa: E402
    import robust_defect as RD  # noqa: E402

random.seed(20261006)
V = G.V
t1v, br, gen, cred, mul, encode = (G.t1_from_vec, G.br, G.gen, G.cred,
                                  G.mul, G.encode)
L2bas, bI4 = G.L2bas, RD.bI4


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


def gpow4(a, e):
    if e == 0:
        return (0, 0, 0, 0)
    if e < 0:
        return gpow4(ginv4(a), -e)
    r = (0, 0, 0, 0)
    for _ in range(e):
        r = gmul4(r, a)
    return r


def gcomm4(a, b):
    return gmul4(gmul4(a, b), gmul4(ginv4(a), ginv4(b)))


def arb3bits(v8):
    v = 0
    for i in range(8):
        for j in range(i + 1, 8):
            for k in range(j + 1, 8):
                if v8[i] and v8[j] and v8[k]:
                    v ^= encode((i, j, k))
    return v


print("=== D1: master ([A,B])_4 formula ===")
ok = True
for t in range(6):
    A = (0, random.getrandbits(64), random.getrandbits(512),
         random.getrandbits(4096))
    B = (random.getrandbits(8), random.getrandbits(64),
         random.getrandbits(512), random.getrandbits(4096))
    got = gcomm4(A, B)[3]
    want = (br(A[2], 3, B[0], 1) ^ br(A[1], 2, B[1], 2)
            ^ mul(br(A[1], 2, B[0], 1), 3, B[0], 1))
    if got != want:
        ok = False
print("  exact 6/6:", ok)
assert ok

print("=== D2: [R2,L2] in I4 ===")
bad = 0
for r in G.R2bas:
    for t in L2bas:
        if cred(br(r, 2, t, 2), bI4) != 0:
            bad += 1
print("  outside: %d/756" % bad)
assert bad == 0

lifts16 = G.lifts
lvec = {"i1": "c1", "i2": "c2"}
for kk in lifts16[2:]:
    lvec[kk] = kk


def mk(key, full=True):
    v8 = V[key]
    V1 = t1v(v8)
    T2 = 0
    for j in range(36):
        if random.getrandbits(1):
            T2 ^= L2bas[j]
    U3 = random.getrandbits(512)
    T4 = random.getrandbits(4096) if full else 0
    return (V1, G.arb2_bits(v8) ^ T2,
            arb3bits(v8) ^ mul(V1, 1, T2, 2) ^ U3, T4)


def rho(lab, L):
    if lab == "real1":
        return gpow4(L["i1"], 2)
    if lab == "real2":
        return gpow4(L["i2"], 2)
    if lab.startswith("tame_"):
        tk = lab[5:]
        p = {"t31": 3, "t32": 3, "t51": 5, "t52": 5}[tk]
        pk = {"t31": "p31", "t32": "p32", "t51": "p51", "t52": "p52"}[tk]
        return gmul4(gmul4(gmul4(L[pk], L[tk]), ginv4(L[pk])),
                     gpow4(L[tk], -p))
    if lab.startswith("xy_"):
        j = lab[3:]
        return gcomm4(L["x" + j], L["y" + j])
    if lab.startswith("xz_"):
        j = lab[3:]
        return gcomm4(L["x" + j], L["z" + j])
    if lab.startswith("x2_"):
        return gpow4(L["x" + lab[3:]], 2)
    if lab.startswith("tau2_") or lab.startswith("phi2_"):
        return gpow4(L[lab[5:]], 2)
    raise AssertionError(lab)


print("=== D3: relator-conjugate formula ===")
qlab = RD.qlabel
tested = set()
ok = True
for qi, lab in enumerate(qlab):
    if lab == "rho_p2" or lab in tested:
        continue
    tested.add(lab)
    L = {kk: mk(lvec[kk]) for kk in lifts16}
    R = rho(lab, L)
    assert R[0] == 0 and R[1] == RD.Q2[qi], lab
    gg = (random.getrandbits(8), random.getrandbits(64),
          random.getrandbits(512), random.getrandbits(4096))
    got = gcomm4(R, gg)[3]
    want = (br(R[2], 3, gg[0], 1) ^ br(R[1], 2, gg[1], 2)
            ^ mul(br(R[1], 2, gg[0], 1), 3, gg[0], 1))
    if got != want:
        ok = False
        print("  MISMATCH", lab)
print("  exact %d/%d relator types" % (len(tested) if ok else -1,
                                       len(tested)))
assert ok
# rho_p2 via r_stand (same initial)
L = {kk: mk(lvec[kk]) for kk in lifts16}
rs = gmul4(gcomm4(L["x2"], L["z2"]),
           gmul4(gcomm4(L["x2"], L["y2"]), gpow4(L["y2"], 2)))
assert rs[0] == 0 and rs[1] == G.deminit("2")
gg = (random.getrandbits(8), random.getrandbits(64),
      random.getrandbits(512), random.getrandbits(4096))
got = gcomm4(rs, gg)[3]
want = (br(rs[2], 3, gg[0], 1) ^ br(rs[1], 2, gg[1], 2)
        ^ mul(br(rs[1], 2, gg[0], 1), 3, gg[0], 1))
print("  r_stand conjugate exact:", got == want)
assert got == want

print("=== D4: cubic-conjugate ===")
ok = True
for j in "12":
    L = {kk: mk(lvec[kk]) for kk in lifts16}
    w = gcomm4(gcomm4(L["y" + j], L["z" + j]), L["z" + j])
    assert w[0] == 0 and w[1] == 0
    gg = (random.getrandbits(8), random.getrandbits(64),
          random.getrandbits(512), random.getrandbits(4096))
    conj = gmul4(gmul4(ginv4(gg), w), gg)
    if conj[3] != (w[3] ^ br(w[2], 3, gg[0], 1)):
        ok = False
    # [(w)_3, V] lands in I4 (R3-row brackets)
    if cred(br(w[2], 3, gg[0], 1), bI4) != 0:
        # (w)_3 = cubic initial; bracket in [R3,L1] subset I4?
        print("  NOTE cubic bracket outside I4?! j=", j)
        ok = False
print("  exact + I4:", ok)
assert ok

print("=== D5: quartic-conjugate invariance ===")
ok = True
L = {kk: mk(lvec[kk]) for kk in lifts16}
Qs = []
for j in "12":
    Qs.append(gpow4(L["z" + j], 4))
    Qs.append(gpow4(gcomm4(L["y" + j], L["z" + j]), 2))
P411 = (0, 0, 1, 1, 1, 0, 0, 0)
for vv in (V["f291"], V["f292"], P411):
    t1 = 0
    for i in range(8):
        if vv[i]:
            t1 ^= gen(i)
    a2 = 0
    for i in range(8):
        for jj in range(i + 1, 8):
            if vv[i] and vv[jj]:
                a2 ^= encode((i, jj))
    a3 = 0
    for i in range(8):
        for jj in range(i + 1, 8):
            for k in range(jj + 1, 8):
                if vv[i] and vv[jj] and vv[k]:
                    a3 ^= encode((i, jj, k))
    Qs.append(gpow4((t1, a2, a3, random.getrandbits(4096)), 4))
for Q in Qs:
    assert Q[0] == 0 and Q[1] == 0 and Q[2] == 0
    gg = (random.getrandbits(8), random.getrandbits(64),
          random.getrandbits(512), random.getrandbits(4096))
    conj = gmul4(gmul4(ginv4(gg), Q), gg)
    if conj[3] != Q[3]:
        ok = False
print("  (Q^g)_4 == (Q)_4 for 7 quartics:", ok)
assert ok
print("DONE")
