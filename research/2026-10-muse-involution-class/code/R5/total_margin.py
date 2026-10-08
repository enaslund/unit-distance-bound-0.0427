"""R5 defect margin: escape dims + full-240 TOTAL test.

1. Exact escape dims: rank(TOTAL + ad3) - rank(TOTAL) for c1, c2
   (quantitative margin of the miss) + witness-row counts.
2. TOTAL_full240: model + LV over ALL 240 quotient dirs (no y1-cut).
   Miss here => defect independent of H1; cover => y1-cut load-bearing.

Usage: .venv/bin/python research/2026-10-muse-involution-class/code/R5/total_margin.py
"""
import sys
import os
import io
import contextlib

sys.path.insert(0, os.path.join("research", "2026-10-muse-involution-class", "code", "R5"))
with contextlib.redirect_stdout(io.StringIO()):
    import genuine_lift as G  # noqa: E402
    import robust_defect as RD  # noqa: E402

V, t1v, br, gen, rb, cred = G.V, G.t1_from_vec, G.br, G.gen, G.rb, G.cred
bI4, rI4 = RD.bI4, RD.rI4
# rebuild TOTAL basis (as RD does)
import hashlib  # noqa: E402
tot = list(RD.model_corrs)
# T0-shift vecs + ker-var vecs: recompute via RD internals is heavy;
# instead re-derive TOTAL as span(model) + LV(all 240) then intersect
# logic below uses RD's printed TOTAL; here compute escape + full240.
keys = [(kk, a) for kk in G.lifts for a in range(15)]
Ssel = RD.Ssel if hasattr(RD, "Ssel") else None
if Ssel is None:
    # recompute quot subset greedily
    Ssel = []
    rest = dict(G.bR2)
    for j, b in enumerate(G.L2bas):
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
# TOTAL basis: need RD's bT; recompute TOTAL the same way RD does is
# complex; approximate: TOTAL = span(model) + LV(kerM) + LV(T0).
# RD does not export kerM/T0; recompute M1 ker + particular quickly.
M1 = {}
for kk in G.lifts:
    for a, j in enumerate(Ssel):
        M1[(kk, a)] = G.M[kk][j]
res = [cred(M1[k], G.bI3) for k in keys]
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
target = cred(G.C1 ^ G.K, G.bI3)
w, T0 = target, 0
for p in sorted(basis):
    if (w >> p) & 1:
        w ^= basis[p][0]
        T0 ^= basis[p][1]
assert w == 0
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
rT, bT = rb(list(bI4.values()) + tot_vecs)
print("TOTAL recomputed: %d (expect 6)" % (rT - rI4))
assert rT - rI4 == 6
# ad3 + escape dims
L2sp = [G.t2_from_mat(G.S(G.np.eye(8, dtype=G.np.uint8)[i]))
        for i in range(8)] if hasattr(G, "np") else None
import numpy as np  # noqa: E402
E8 = np.eye(8, dtype=np.uint8)
L2sp = [G.t2_from_mat(G.S(E8[i])) for i in range(8)]
for i in range(8):
    for j in range(i + 1, 8):
        L2sp.append(G.t2_from_mat(G.B(E8[i], E8[j])))
L3rows = [br(M, 2, gen(c), 1) for M in L2sp for c in range(8)]
for cnm in ["c1", "c2"]:
    W = t1v(V[cnm])
    adv = [br(T, 3, W, 1) for T in L3rows]
    esc = rb(list(bT.values()) + adv)[0] - rT
    nwit = sum(1 for a in adv if cred(a, bT) != 0)
    print("ad3(%s): escape-dim=%d witness-rows=%d/288"
          % (cnm, esc, nwit))
# full-240 TOTAL (no y1-cut)
full = list(RD.model_corrs)
for s in range(28):
    for kk in G.lifts:
        for a in range(15):
            full.append(RD.lv_s(s, kk, Ssel[a]))
rF, bF = rb(list(bI4.values()) + full)
print("TOTAL_full240 dim mod I4: %d" % (rF - rI4))
for cnm in ["c1", "c2"]:
    W = t1v(V[cnm])
    adv = [br(T, 3, W, 1) for T in L3rows]
    esc = rb(list(bF.values()) + adv)[0] - rF
    print("  vs full240 ad3(%s): escape-dim=%d %s"
          % (cnm, esc, "MISS (H1-INDEPENDENT)" if esc else "cover"))
# full-240 separating functional + versioned cert
W1 = t1v(V["c1"])
adv1 = [br(T, 3, W1, 1) for T in L3rows]
r0 = None
wrow = None
for idx, a in enumerate(adv1):
    rr = cred(a, bF)
    if rr != 0:
        r0, wrow = rr, idx
        break
assert r0 is not None
p = r0.bit_length() - 1
lam = lambda x: (cred(x, bF) >> p) & 1  # noqa: E731
print("full240 functional: bit %d, lam(wit L3row %d)=%d, zero on basis: %s"
      % (p, wrow, lam(adv1[wrow]),
         all(lam(v) == 0 for v in bF.values())))
import hashlib  # noqa: E402
import json  # noqa: E402
h = hashlib.sha256()
for q in sorted(bF):
    h.update(bF[q].to_bytes(512, "big"))
cert = {
    "gauge": "41-cap",
    "space": "full-240 (no y1-cut)",
    "caps": {"f291": [int(x) for x in V["f291"]],
             "f292": [int(x) for x in V["f292"]],
             "P41[1]": [0, 0, 1, 1, 1, 0, 0, 0]},
    "I4_rank": rI4,
    "TOTAL_full240_dim_mod_I4": rF - rI4,
    "functional_bit": p,
    "witness_L3row": wrow,
    "witness_residue_hex": hex(r0),
    "TOTAL_basis_sha256": h.hexdigest(),
}
os.makedirs(".muse-scratch", exist_ok=True)
with open(".muse-scratch/R5_defect_cert_full240.json", "w") as f:
    json.dump(cert, f, indent=1)
with open("research/2026-10-muse-involution-class/code/R5/defect_cert_full240.json", "w") as f:
    json.dump(cert, f, indent=1)
print("cert fingerprint:", h.hexdigest()[:16], "-> tracked defect_cert_full240.json")
print("DONE")
