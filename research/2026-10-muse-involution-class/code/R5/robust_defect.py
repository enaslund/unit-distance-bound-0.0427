"""R5 robust defect: TOTAL R4-variation over the 214-space vs ad3-image.

R4(T') = I4 + span_s(corr_s(T')), corr_s affine in T' (U'-free by
even exponent-sums). TOTAL = model-span + LV-variation over the
y1-cut 214-affine space (+ R2-direction check). If some ad3-vector
misses TOTAL, uniform lifting defect follows (C93 4a) without exact R4.

Usage: .venv/bin/python research/2026-10-muse-involution-class/code/R5/robust_defect.py
"""
import sys
import os
import io
import contextlib

sys.path.insert(0, os.path.join("research", "2026-10-muse-involution-class", "code", "R5"))
with contextlib.redirect_stdout(io.StringIO()):
    import genuine_lift as G  # noqa: E402

V, S, B = G.V, G.S, G.B
t1v, t2m = G.t1_from_vec, G.t2_from_mat
br, gen, rb, cred, mul = G.br, G.gen, G.rb, G.cred, G.mul
L2bas, Q2 = G.L2bas, G.Q2
bI3, bI4, rI4 = G.bI3, G.bI4, G.rI4
lifts = G.lifts
print("premises: I4=%d L2=%d R2=%d" % (rI4, len(L2bas), len(G.R2bas)))

# ---- D=4 dict Magnus for OM4 on ARB ----
def emul4(A, B):
    C = {}
    for m1 in A:
        for m2 in B:
            if len(m1) + len(m2) > 4:
                continue
            m = m1 + m2
            C[m] = C.get(m, 0) ^ 1
            if C[m] == 0:
                del C[m]
    return C


def eadd4(*As):
    C = {}
    for A in As:
        for m in A:
            C[m] = C.get(m, 0) ^ 1
            if C[m] == 0:
                del C[m]
    return C


def arb4(v8):
    g = {(): 1}
    for i in range(8):
        if int(v8[i]) % 2:
            g = emul4(g, {(): 1, (i,): 1})
    return g


def ginv4(g):
    one = {(): 1}
    a = {m: 1 for m in g if m != ()}
    a2 = emul4(a, a)
    a3 = emul4(a2, a)
    return eadd4(one, a, a2, a3, emul4(a3, a))


def gcomm4(a, b):
    return emul4(emul4(a, b), emul4(ginv4(a), ginv4(b)))


def t4_from_dict(d):
    v = 0
    for m in d:
        assert len(m) == 4
        v ^= G.encode(m)
    return v


# ---- syzygy kernel (tracked) ----
R3rows = []
for q in Q2:
    for i in range(8):
        R3rows.append(br(q, 2, gen(i), 1))
R3rows += G.cub3
assert len(R3rows) == 170
piv = {}
ker = []
for r, row in enumerate(R3rows):
    w, c = row, 1 << r
    for p in sorted(piv):
        if (w >> p) & 1:
            w ^= piv[p][0]
            c ^= piv[p][1]
    if w == 0:
        ker.append(c)
    else:
        lb = (w & (-w)).bit_length() - 1
        piv[lb] = (w, c)
assert len(ker) == 28
for c in ker:
    s = 0
    for r in range(170):
        if (c >> r) & 1:
            s ^= R3rows[r]
    assert s == 0
print("syzygy kernel: 28, all verify")

# ---- model F3 (ARB base, all 21 quadrics) ----
tame_p = {"t31": 3, "t32": 3, "t51": 5, "t52": 5}
tame_phi = {"t31": "p31", "t32": "p32", "t51": "p51", "t52": "p52"}
ARB = G.ARB


def rho_arb_full(lab):
    if lab == "real1":
        return G.gpow3(ARB["c1"], 2)
    if lab == "real2":
        return G.gpow3(ARB["c2"], 2)
    if lab.startswith("tame_"):
        tk = lab[5:]
        return G.eval_rho_tame3(ARB[tk], ARB[tame_phi[tk]], tame_p[tk])
    if lab.startswith("xy_"):
        jj = lab[3:]
        return G.gcomm3(ARB["x" + jj], ARB["y" + jj])
    if lab.startswith("xz_"):
        jj = lab[3:]
        return G.gcomm3(ARB["x" + jj], ARB["z" + jj])
    if lab.startswith("x2_"):
        jj = lab[3:]
        return G.gpow3(ARB["x" + jj], 2)
    if lab.startswith("tau2_"):
        return G.gpow3(ARB[lab[5:]], 2)
    if lab.startswith("phi2_"):
        return G.gpow3(ARB[lab[5:]], 2)
    raise AssertionError(lab)


F3m = {}
for lab in set(G.qlabel):
    if lab == "rho_p2":
        F3m[lab] = G.Fpin  # formal pin (ebar residual absorbed in I4)
    else:
        F3m[lab] = G.t3_from_dict(G.deg_part(rho_arb_full(lab), 3))
OM4a = {}
for j in "12":
    Y = arb4(V["y" + j])
    Z = arb4(V["z" + j])
    w = gcomm4(gcomm4(Y, Z), Z)
    OM4a[j] = t4_from_dict({m: 1 for m in w if len(m) == 4})
qlabel = G.qlabel
model_corrs = []
for c in ker:
    t = 0
    for k in range(168):
        if (c >> k) & 1:
            nm = qlabel[k // 8]
            t ^= br(F3m[nm], 3, gen(k % 8), 1)
            # E-term: ([A,x])_4 = [(A)_3,X] + [(A)_2,X]X; a_2 recorded
            t ^= mul(br(Q2[k // 8], 2, gen(k % 8), 1), 3, gen(k % 8), 1)
    if (c >> 168) & 1:
        t ^= OM4a["1"]
    if (c >> 169) & 1:
        t ^= OM4a["2"]
    model_corrs.append(t)
mspan = rb(list(bI4.values()) + model_corrs)[0] - rI4
print("ARB-base model span mod I4:", mspan)

# ---- fiber quotient subset (15 of 36) ----
Ssel = []
rest = dict(G.bR2)
for j, b in enumerate(L2bas):
    if cred(b, rest) != 0:
        Ssel.append(j)
        r = cred(b, rest)
        p = r.bit_length() - 1
        for q in list(rest):
            if (rest[q] >> p) & 1:
                rest[q] ^= r
        rest[p] = r
    if len(Ssel) == 15:
        break
assert len(Ssel) == 15
print("quot subset: 15")

# ---- M1 on quot coords + ker + particular ----
M1 = {}  # (lift,m) -> T3 bitvec
for kk in lifts:
    for a, j in enumerate(Ssel):
        M1[(kk, a)] = G.M[kk][j]
keys = [(kk, a) for kk in lifts for a in range(15)]
res = [cred(M1[k], bI3) for k in keys]
# nullspace of 240 -> residues
basis = {}
kerM = []
for e, r in enumerate(res):
    w, c = r, 1 << e
    for p in sorted(basis):
        if (w >> p) & 1:
            w ^= basis[p][0]
            c ^= basis[p][1]
    if w == 0:
        kerM.append(c)
    else:
        lb = (w & (-w)).bit_length() - 1
        basis[lb] = (w, c)
print("ker M1 dim: %d (expect 214)" % len(kerM))
assert len(kerM) == 214
# particular: solve = C1+K mod I3
target = cred(G.C1 ^ G.K, bI3)
w, c = target, 0
for p in sorted(basis):
    if (w >> p) & 1:
        w ^= basis[p][0]
        c ^= basis[p][1]
assert w == 0, "y1-cut unsolvable?!"
T0 = c
print("particular T0 found: True")

# ---- LV maps ----
tame_cross = G.tame_cross
cx2, cy2, cz2 = G.r2_cross_cols((V["x2"], V["y2"], V["z2"]))


def lv_quad(lab, lift, tj):
    """LV of relator lab deg-3 wrt lift's fiber T'=L2bas[tj]."""
    if lab in ("real1", "real2"):
        g = "i1" if lab == "real1" else "i2"
        if lift != g:
            return 0
        return br(t1v(V["c1" if g == "i1" else "c2"]), 1, L2bas[tj], 2)
    if lab.startswith("tame_"):
        tk = lab[5:]
        ct, cp = tame_cross[tk]
        if lift == tk:
            return ct[tj]
        if lift == tame_phi[tk]:
            return cp[tj]
        return 0
    if lab == "rho_p2":
        if lift == "x2":
            return cx2[tj]
        if lift == "y2":
            return cy2[tj]
        if lift == "z2":
            return cz2[tj]
        return 0
    if lab.startswith("x2_"):
        if lift != "x" + lab[3:]:
            return 0
        return br(t1v(V["x" + lab[3:]]), 1, L2bas[tj], 2)
    if lab.startswith("xy_") or lab.startswith("xz_"):
        jj = lab[3:]
        A = V["x" + jj]
        Bv = V["y" + jj] if lab.startswith("xy_") else V["z" + jj]
        Bl = ("y" if lab.startswith("xy_") else "z") + jj
        if lift == "x" + jj:
            return br(L2bas[tj], 2, t1v(Bv), 1)
        if lift == Bl:
            return br(t1v(A), 1, L2bas[tj], 2)
        return 0
    if lab.startswith("tau2_") or lab.startswith("phi2_"):
        if lift != lab[5:]:
            return 0
        return br(t1v(V[lab[5:]]), 1, L2bas[tj], 2)
    raise AssertionError(lab)


def lv_omega(j, lift, tj):
    Yv, Zv = t1v(V["y" + j]), t1v(V["z" + j])
    T = L2bas[tj]
    if lift == "y" + j:
        return br(br(T, 2, Zv, 1), 3, Zv, 1)
    if lift == "z" + j:
        return br(br(Yv, 1, T, 2), 3, Zv, 1) ^ br(br(Yv, 1, Zv, 1), 3, T, 2)
    return 0


def lv_s(s, lift, tj):
    c = ker[s]
    t = 0
    for k in range(168):
        if (c >> k) & 1:
            nm = qlabel[k // 8]
            t ^= br(lv_quad(nm, lift, tj), 3, gen(k % 8), 1)
    if (c >> 168) & 1:
        t ^= lv_omega("1", lift, tj)
    if (c >> 169) & 1:
        t ^= lv_omega("2", lift, tj)
    return t


# R2-check: LV_s(R2) in I4?
r2bad = 0
r2tot = 0
for s in range(28):
    for kk in lifts:
        for r in G.R2bas:
            # express r in L2bas coords
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
            w = r << 36
            while w:
                pp = w.bit_length() - 1
                if pp in aug:
                    w ^= aug[pp]
                else:
                    break
            assert w >> 36 == 0
            cc = w & ((1 << 36) - 1)
            acc = 0
            for j in range(36):
                if (cc >> j) & 1:
                    acc ^= lv_s(s, kk, j)
            r2tot += 1
            if cred(acc, bI4) != 0:
                r2bad += 1
print("LV(R2) outside I4: %d / %d (0 => quotient well-defined)"
      % (r2bad, r2tot))

# TOTAL: model + LV(T0) + LV(kerM) [+ LV(R2) if nonzero]
tot_vecs = list(model_corrs)
for s in range(28):
    acc = 0
    for e in range(240):
        if (T0 >> e) & 1:
            kk, a = keys[e]
            acc ^= lv_s(s, kk, Ssel[a])
    tot_vecs.append(acc)
n_ker = 0
for s in range(28):
    for kv in kerM:
        acc = 0
        e = 0
        kk = kv
        while kk:
            if kk & 1:
                lift, a = keys[e]
                acc ^= lv_s(s, lift, Ssel[a])
            e += 1
            kk >>= 1
        tot_vecs.append(acc)
        n_ker += 1
if r2bad:
    for s in range(28):
        for kk in lifts:
            for r in G.R2bas:
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
                w = r << 36
                while w:
                    pp = w.bit_length() - 1
                    if pp in aug:
                        w ^= aug[pp]
                    else:
                        break
                cc = w & ((1 << 36) - 1)
                acc = 0
                for j in range(36):
                    if (cc >> j) & 1:
                        acc ^= lv_s(s, kk, j)
                tot_vecs.append(acc)
rT, bT = rb(list(bI4.values()) + tot_vecs)
print("TOTAL dim mod I4: %d (<=81); vecs used: %d"
      % (rT - rI4, len(tot_vecs)))
rM = rb(list(bI4.values()) + model_corrs)[0] - rI4
t0vecs = tot_vecs[28:56]
rM0 = rb(list(bI4.values()) + model_corrs + t0vecs)[0] - rI4
print("  breakdown: model=%d +T0shift=%d +ker-var=%d"
      % (rM, rM0, rT - rI4))

# ---- ad3 images vs TOTAL ----
import numpy as np  # noqa: E402
E8 = np.eye(8, dtype=np.uint8)
L2sp = [t2m(S(E8[i])) for i in range(8)]
for i in range(8):
    for j in range(i + 1, 8):
        L2sp.append(t2m(B(E8[i], E8[j])))
L3rows = [br(M, 2, gen(c), 1) for M in L2sp for c in range(8)]
for cnm in ["c1", "c2"]:
    W = t1v(V[cnm])
    adv = [br(T, 3, W, 1) for T in L3rows]
    ra = rb(list(bI4.values()) + adv)[0] - rI4
    rT2 = rb(list(bT.values()) + adv)[0] - rT
    wit = None
    for idx, a in enumerate(adv):
        if cred(a, bT) != 0:
            wit = idx
            break
    print("ad3(%s): rank mod I4 = %d; outside TOTAL: %s; witness L3row %s"
          % (cnm, ra, rT2 > 0, wit))
    if wit is not None:
        # witness residue nonzero mod TOTAL; confirm in L4
        print("  witness residue mod TOTAL nonzero:",
              cred(adv[wit], bT) != 0)
# deciding functional: lam*(x) = bit-p of cred(x, bT), p = top bit of
# the c1-witness residue. Vanishes on TOTAL, =1 on witness.
W1 = t1v(V["c1"])
adv1 = [br(T, 3, W1, 1) for T in L3rows]
r0 = None
for a in adv1:
    rr = cred(a, bT)
    if rr != 0:
        r0 = rr
        break
assert r0 is not None
p = r0.bit_length() - 1
lam = lambda x: (cred(x, bT) >> p) & 1  # noqa: E731
print("deciding functional: bit %d of TOTAL-residue" % p)
print("  lam(witness)=%d lam|_TOTAL-basis all zero: %s"
      % (lam(adv1[[cred(a, bT) != 0 for a in adv1].index(True)]),
         all(lam(v) == 0 for v in bT.values())))
# certificate export (appended; results above unchanged)
import hashlib  # noqa: E402
import json  # noqa: E402
h = hashlib.sha256()
for q in sorted(bT):
    h.update(bT[q].to_bytes(512, "big"))
cert = {
    "gauge": "41-cap",
    "caps": {"f291": [int(x) for x in V["f291"]],
             "f292": [int(x) for x in V["f292"]],
             "P41[1]": [0, 0, 1, 1, 1, 0, 0, 0]},
    "I4_rank": rI4,
    "TOTAL_dim_mod_I4": rT - rI4,
    "functional_bit": p,
    "witness_L3row": 1,
    "witness_residue_hex": hex(r0),
    "TOTAL_basis_sha256": h.hexdigest(),
}
os.makedirs(".muse-scratch", exist_ok=True)
with open(".muse-scratch/R5_defect_cert.json", "w") as f:
    json.dump(cert, f, indent=1)
with open("research/2026-10-muse-involution-class/code/R5/defect_cert.json", "w") as f:
    json.dump(cert, f, indent=1)
print("cert fingerprint:", h.hexdigest()[:16], "-> scratch + tracked defect_cert.json")
print("DONE")
