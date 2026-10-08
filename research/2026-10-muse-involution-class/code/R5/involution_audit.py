"""Audit both real involutions in the retained quotient Gbar_B (R5 signature direction).

Replicates the rank computations of papers/0.04273/certificates/lie241.py and
lie241c.py for c1 AND c2: rank of ad(c): L1 -> gr2 and ad(c): gr2 -> gr3
modulo relations. Conjugacy class of c in Gbar_B has size 2^(rank1+rank2):
|C| = 2^(8-rank1) * 2^(41-rank2) since D2(Gbar) is abelian of order 2^(15+26)
and D3(Gbar) is central (tower.tex proof of tw:retained-quotient(c)).

Usage: .venv/bin/python research/2026-10-muse-involution-class/code/R5/involution_audit.py
"""
import sys
import os

sys.path.insert(0, os.path.join("papers", "0.04273", "certificates"))
import numpy as np  # noqa: E402
from lie241 import V, S, B, f2rank, n, rels, names  # noqa: E402

E = np.eye(n, dtype=np.uint8)


def indep_mod(vecs, base):
    M1 = np.array([m.flatten() for m in base], dtype=np.uint8)
    M2 = np.array([m.flatten() for m in vecs] + [m.flatten() for m in base],
                  dtype=np.uint8)
    return f2rank(M2) - f2rank(M1)


# degree-1 ranks
r1 = {}
for cn in ["c1", "c2"]:
    c = V[cn]
    img = [B(c, E[i]) for i in range(n)]
    r1[cn] = indep_mod(img, rels)
    print(cn, "rank ad on L1 mod rels:", r1[cn])

# degree-2 -> 3 ranks (lie241c.py construction)
Q = [m for m, nm in zip(rels, names) if nm != "demuskin1"]


def br2(M, v):
    return (np.einsum("ij,k->ijk", M, v) + np.einsum("k,ij->kij", v, M)) % 2


def lie_bracket(u, v):
    return (np.outer(u, v) + np.outer(v, u)) % 2


R3 = [br2(r, E[k]).flatten() for r in Q for k in range(n)]
for j in "12":
    y, z = V["y" + j], V["z" + j]
    R3.append(br2(lie_bracket(y, z), z).flatten())
R3 = np.array(R3, dtype=np.uint8)
r3 = f2rank(R3)
free2 = ([S(E[i]) for i in range(n)]
         + [lie_bracket(E[i], E[j]) for i in range(n) for j in range(i + 1, n)])
Qm = np.array([m.flatten() for m in Q], dtype=np.uint8)
comp = []
cur = Qm.copy()
for m in free2:
    trial = np.vstack([cur, m.flatten()])
    if f2rank(trial) > f2rank(cur):
        cur = trial
        comp.append(m)
assert len(comp) == 15, len(comp)
for cn in ["c1", "c2"]:
    c = V[cn]
    imgs = np.array([br2(u, c).flatten() for u in comp], dtype=np.uint8)
    rk = f2rank(np.vstack([R3, imgs])) - r3
    print("%s rank ad L2->L3: %d => class 2^%d" % (cn, rk, r1[cn] + rk))
    assert (r1[cn], rk) == (7, 8), (cn, r1[cn], rk)
print("AUDIT PASS: both involutions have class exactly 2^15 in Gbar_B")
