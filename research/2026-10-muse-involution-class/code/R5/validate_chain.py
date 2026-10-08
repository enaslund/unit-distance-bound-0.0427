"""R5 chain validation: finite-difference checks of LV-exactness (H3),
y1-derivation (H1 machinery), and R4-exhaustion slice (H2 computational).

Trip4 (t1..t4 bitvec) direct evaluation vs linearized predictions, with
RANDOM degree-2 (full L2) and degree-3 (full T3) perturbations:
 A1: Wp-linearization exact + U'-invariance + trip/dict cross-check.
 A2: syzygy (w_s)_4 == model_s + LV_s(T') exactly, U'-free (no-rho_p2).
 B: r_stand (same initial, different word) end-to-end + T'/U'-freedom.
 C: random D4-words (r_stand at rho_p2 slots) match combo prediction mod I4.
Group-like realizability irrelevant (formal polynomial identities).

Usage: .venv/bin/python research/2026-10-muse-involution-class/code/R5/validate_chain.py
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

random.seed(12345)
V = G.V
t1v, br, gen = G.t1_from_vec, G.br, G.gen
mul, encode = G.mul, G.encode
L2bas = G.L2bas
lifts16 = G.lifts
lvec = {"i1": "c1", "i2": "c2"}
for kk in lifts16[2:]:
    lvec[kk] = kk


def arb3bits(v8):
    v = 0
    for i in range(8):
        for j in range(i + 1, 8):
            for k in range(j + 1, 8):
                if v8[i] and v8[j] and v8[k]:
                    v ^= encode((i, j, k))
    return v


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
    n1 = a1
    n2 = a2 ^ a12
    n3 = a3 ^ mul(a1, 1, a2, 2) ^ mul(a2, 2, a1, 1) ^ mul(a12, 2, a1, 1)
    n4 = (a4 ^ mul(a1, 1, a3, 3) ^ mul(a3, 3, a1, 1) ^ mul(a2, 2, a2, 2)
          ^ mul(a12, 2, a2, 2) ^ mul(mul(a1, 1, a2, 2), 3, a1, 1)
          ^ mul(mul(a2, 2, a1, 1), 3, a1, 1) ^ mul(mul(a12, 2, a1, 1), 3, a1, 1))
    return (n1, n2, n3, n4)


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


def rand_T2():
    v = 0
    m = 0
    for j in range(36):
        if random.getrandbits(1):
            v ^= L2bas[j]
            m |= 1 << j
    return v, m


def mk_lift(key, T2, U3, T4=0):
    v8 = V[key]
    V1 = t1v(v8)
    A2 = G.arb2_bits(v8)
    A3 = arb3bits(v8)
    return (V1, A2 ^ T2, A3 ^ mul(V1, 1, T2, 2) ^ U3, T4)


def rand_lifts(t4=False):
    L, M = {}, {}
    for kk in lifts16:
        T2, m = rand_T2()
        T4 = random.getrandbits(4096) if t4 else 0
        L[kk] = mk_lift(lvec[kk], T2, random.getrandbits(512), T4)
        M[kk] = m
    return L, M


def arb_lifts():
    return {kk: mk_lift(lvec[kk], 0, 0) for kk in lifts16}


tame_p = {"t31": 3, "t32": 3, "t51": 5, "t52": 5}
tame_phi = {"t31": "p31", "t32": "p32", "t51": "p51", "t52": "p52"}


def rho_tame(T, Fp, p):
    return gmul4(gmul4(gmul4(Fp, T), ginv4(Fp)), gpow4(T, -p))


def rho_of(lab, L):
    if lab == "real1":
        return gpow4(L["i1"], 2)
    if lab == "real2":
        return gpow4(L["i2"], 2)
    if lab.startswith("tame_"):
        tk = lab[5:]
        return rho_tame(L[tk], L[tame_phi[tk]], tame_p[tk])
    if lab.startswith("xy_"):
        jj = lab[3:]
        return gcomm4(L["x" + jj], L["y" + jj])
    if lab.startswith("xz_"):
        jj = lab[3:]
        return gcomm4(L["x" + jj], L["z" + jj])
    if lab.startswith("x2_"):
        return gpow4(L["x" + lab[3:]], 2)
    if lab.startswith("tau2_") or lab.startswith("phi2_"):
        return gpow4(L[lab[5:]], 2)
    raise AssertionError(lab)


def omega_of(j, L):
    return gcomm4(gcomm4(L["y" + j], L["z" + j]), L["z" + j])


def wp_of(j, L):
    return gmul4(gpow4(L["y" + j], 2),
                 gmul4(gcomm4(L["x" + j], L["y" + j]),
                       gcomm4(L["x" + j], L["z" + j])))


def rstand_of(L):
    return gmul4(gcomm4(L["x2"], L["z2"]),
                 gmul4(gcomm4(L["x2"], L["y2"]), gpow4(L["y2"], 2)))


def lv_r_at(M):
    Xv, Yv, Zv = (t1v(V["x2"]), t1v(V["y2"]), t1v(V["z2"]))
    LV = 0
    for lift, role in (("x2", 0), ("y2", 1), ("z2", 2)):
        m = M[lift]
        for j in range(36):
            if (m >> j) & 1:
                fb = L2bas[j]
                if role == 0:
                    LV ^= br(fb, 2, Yv, 1) ^ br(fb, 2, Zv, 1)
                elif role == 1:
                    LV ^= br(Yv, 1, fb, 2) ^ br(Xv, 1, fb, 2)
                else:
                    LV ^= br(Xv, 1, fb, 2)
    return LV


# ---------- A1 ----------
print("=== A1: Wp linearization + trip/dict cross-check ===")
La = arb_lifts()
print("  Wp_arb trip == G.K dict:", wp_of("2", La)[2] == G.K)
assert wp_of("2", La)[2] == G.K
for trial in range(2):
    L, M = rand_lifts()
    W = wp_of("2", L)
    ok = W[2] == (G.K ^ lv_r_at(M))
    print("  trial %d: (Wp)_3 == K + LV_r(T') exact: %s" % (trial, ok))
    assert ok
print("  (U' random each trial: equality confirms U'-absence)")

# ---------- A2 ----------
print("=== A2: (w_s)_4 == model_s + LV_s(T') ===")
p2slots = {i for i, q in enumerate(G.qlabel) if q == "rho_p2"}
cand = [s for s in range(28)
        if not any((RD.ker[s] >> (q * 8 + i)) & 1
                   for q in p2slots for i in range(8))]
print("  non-rho_p2 syzygies: %d of 28" % len(cand))
for s in cand:
    L, M = rand_lifts(t4=True)
    w = (0, 0, 0, 0)
    c = RD.ker[s]
    for k in range(168):
        if (c >> k) & 1:
            nm = RD.qlabel[k // 8]
            xh = (gen(k % 8), 0, 0, 0)
            w = gmul4(w, gcomm4(rho_of(nm, L), xh))
    if (c >> 168) & 1:
        w = gmul4(w, omega_of("1", L))
    if (c >> 169) & 1:
        w = gmul4(w, omega_of("2", L))
    assert w[0] == 0 and w[1] == 0 and w[2] == 0, s
    pred = RD.model_corrs[s]
    for kk in lifts16:
        m = M[kk]
        for j in range(36):
            if (m >> j) & 1:
                pred ^= RD.lv_s(s, kk, j)
    print("  syz %d: exact: %s" % (s, w[3] == pred))
    assert w[3] == pred

# ---------- B ----------
print("=== B: r_stand end-to-end + T'/U'-freedom ===")
Fstand = rstand_of(La)[2]
print("  (r_stand)_2 == deminit(2):", rstand_of(La)[1] == G.deminit("2"))
assert rstand_of(La)[1] == G.deminit("2")
for trial in range(2):
    L, M = rand_lifts()
    rs = rstand_of(L)
    ok = rs[2] == (Fstand ^ lv_r_at(M))
    Wp = wp_of("2", L)
    Wpp = gmul4(Wp, ginv4(rs))
    ok2 = Wpp[2] == (G.K ^ Fstand)
    print("  trial %d: stand-affine: %s  y2-T'/U'-free: %s"
          % (trial, ok, ok2))
    assert ok and ok2

# ---------- C ----------
print("=== C: random D4-words match combo mod I4 ===")
Qlist = []
for j in "12":
    Qlist.append(gpow4(La["z" + j], 4))
    Qlist.append(gpow4(gcomm4(La["y" + j], La["z" + j]), 2))
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
                a2 ^= G.encode((i, jj))
    a3 = 0
    for i in range(8):
        for jj in range(i + 1, 8):
            for k in range(jj + 1, 8):
                if vv[i] and vv[jj] and vv[k]:
                    a3 ^= G.encode((i, jj, k))
    Qlist.append(gpow4((t1, a2, a3, 0), 4))
for nm in set(RD.qlabel):
    if nm != "rho_p2":
        Qlist.append(gpow4(rho_of(nm, La), 2))
# adjusted models with F_stand at rho_p2 bits
adj_models = []
for s in range(28):
    t = RD.model_corrs[s]
    c = RD.ker[s]
    for k in range(168):
        if (c >> k) & 1 and RD.qlabel[k // 8] == "rho_p2":
            t ^= br(G.Fpin ^ Fstand, 3, gen(k % 8), 1)
    adj_models.append(t)
ok = 0
for trial in range(12):
    w = (0, 0, 0, 0)
    pred = 0
    for s in range(28):
        if random.getrandbits(1):
            pred ^= adj_models[s]
            c = RD.ker[s]
            for k in range(168):
                if (c >> k) & 1:
                    nm = RD.qlabel[k // 8]
                    xh = (gen(k % 8), 0, 0, 0)
                    if nm == "rho_p2":
                        w = gmul4(w, gcomm4(rstand_of(La), xh))
                    else:
                        w = gmul4(w, gcomm4(rho_of(nm, La), xh))
            if (c >> 168) & 1:
                w = gmul4(w, omega_of("1", La))
            if (c >> 169) & 1:
                w = gmul4(w, omega_of("2", La))
    for Q in Qlist:
        if random.getrandbits(1):
            w = gmul4(w, Q)
    assert w[0] == 0 and w[1] == 0 and w[2] == 0, trial
    r = G.cred(w[3] ^ pred, RD.bI4)
    if r == 0:
        ok += 1
    print("  trial %d: D4 ok, combo match mod I4: %s" % (trial, r == 0))
    assert r == 0
print("  passed: %d/12" % ok)
print("DONE")
