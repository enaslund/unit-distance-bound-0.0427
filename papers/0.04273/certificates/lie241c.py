import numpy as np
from lie241 import V, S, B, f2rank, n, rels, names
E = np.eye(n, dtype=np.uint8)
# independent quadratic initials: drop demuskin1 (consequence of the others)
Q = [m for m, nm in zip(rels, names) if nm != "demuskin1"]
print("independent quadratic initials:", f2rank(np.array([m.flatten() for m in Q])), "of", len(Q))
def t3(a, b, c):  # tensor product of vectors
    return np.einsum('i,j,k->ijk', a, b, c) % 2
def br2(M, v):    # [M, v] for degree-2 tensor M, vector v : M(x)v + v(x)M
    return (np.einsum('ij,k->ijk', M, v) + np.einsum('k,ij->kij', v, M)) % 2
def lie_bracket(u, v):
    return (np.outer(u, v) + np.outer(v, u)) % 2
# free restricted Lie algebra degree 3 inside tensors
free3 = []
for a in range(n):
    for b in range(n):
        for c in range(n):
            free3.append(br2(lie_bracket(E[a], E[b]), E[c]).flatten())
    for b in range(n):
        free3.append(br2(S(E[a]), E[b]).flatten())
F3 = f2rank(np.array(free3, dtype=np.uint8))
print("free restricted Lie degree 3 dimension:", F3)
R3 = [br2(r, E[k]).flatten() for r in Q for k in range(n)]
for j in "12":
    y, z = V["y" + j], V["z" + j]
    R3.append(br2(lie_bracket(y, z), z).flatten())
R3 = np.array(R3, dtype=np.uint8)
r3 = f2rank(R3)
print("rank of cubic relation span:", r3, " -> L3 =", F3 - r3)
L1, L2 = 8, 36 - 21
print("|G/D_4 G| = 2^%d" % (L1 + L2 + F3 - r3))
# ad(c1): L2 -> L3.  basis of L2 = complement of relation span in free degree 2
free2 = [S(E[i]) for i in range(n)] + [lie_bracket(E[i], E[j]) for i in range(n) for j in range(i + 1, n)]
Qm = np.array([m.flatten() for m in Q], dtype=np.uint8)
comp = []
cur = Qm.copy()
for m in free2:
    trial = np.vstack([cur, m.flatten()])
    if f2rank(trial) > f2rank(cur):
        cur = trial
        comp.append(m)
print("complement size (should be L2=15):", len(comp))
c = V["c1"]
imgs = np.array([br2(u, c).flatten() for u in comp], dtype=np.uint8)
rank_c = f2rank(np.vstack([R3, imgs])) - r3
print("rank of ad(c1): L2 -> L3 modulo relations:", rank_c)
print("conjugacy class of c1 in G/D_4 G has size 2^%d" % (7 + rank_c))
