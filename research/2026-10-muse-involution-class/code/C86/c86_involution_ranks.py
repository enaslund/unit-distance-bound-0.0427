"""C86 independent both-involution rank check (stdlib only, no numpy, no lie241 import).

Reimplements the lie241.py/lie241c.py/involution_audit.py computations from the
recorded vector table (copied values) with own F2 linear algebra (int bitmasks).
Verifies: R2 rank 21 (L2=15), R3 rank 142 (L3=26), ad(c):L1->gr2 rank 7 and
ad(c):gr2->gr3 rank 8 for BOTH c1,c2, and separation (d) for both.
Run: python3 research/2026-10-muse-involution-class/code/C86/c86_involution_ranks.py
"""
import itertools

n = 8
V = {
    "c1": [1, 0, 1, 1, 1, 0, 1, 0], "c2": [1, 1, 0, 0, 0, 1, 0, 1],
    "x1": [0, 0, 1, 0, 0, 0, 0, 0], "y1": [1, 1, 1, 1, 0, 0, 1, 0], "z1": [1, 0, 0, 0, 0, 1, 0, 0],
    "x2": [0, 0, 0, 1, 0, 0, 0, 0], "y2": [1, 0, 0, 0, 0, 0, 0, 1], "z2": [1, 1, 1, 1, 1, 0, 0, 0],
    "t31": [0, 0, 0, 0, 1, 0, 0, 0], "p31": [1, 0, 1, 0, 0, 1, 1, 1],
    "t32": [0, 0, 0, 0, 0, 1, 0, 0], "p32": [1, 1, 1, 0, 1, 0, 1, 1],
    "t51": [0, 0, 0, 0, 0, 0, 1, 0], "p51": [0, 1, 1, 0, 0, 1, 0, 1],
    "t52": [0, 0, 0, 0, 0, 0, 0, 1], "p52": [0, 1, 0, 1, 1, 0, 1, 0],
    "f291": [0, 0, 1, 0, 0, 1, 1, 1], "f292": [0, 0, 0, 1, 1, 0, 1, 1],
    "f7": [0, 1, 1, 1, 0, 0, 0, 0],
}
E = [[1 if i == j else 0 for j in range(n)] for i in range(n)]

def f2rank_int(rows):
    basis = {}
    r = 0
    for v in rows:
        x = v
        while x:
            b = x.bit_length() - 1
            if b in basis:
                x ^= basis[b]
            else:
                basis[b] = x
                r += 1
                break
    return r

def mat_bits(M):
    """8x8 0/1 matrix -> 64-bit int, bit (i*8+j)."""
    v = 0
    for i in range(n):
        for j in range(n):
            if M[i][j] & 1:
                v |= 1 << (i * n + j)
    return v

def ten_bits(T):
    """8x8x8 0/1 tensor -> 512-bit int, bit (i*64+j*8+k)."""
    v = 0
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if T[i][j][k] & 1:
                    v |= 1 << (i * 64 + j * 8 + k)
    return v

def outer(v, w):
    return [[v[i] * w[j] & 1 for j in range(n)] for i in range(n)]

def madd(A, B):
    return [[A[i][j] ^ B[i][j] for j in range(n)] for i in range(n)]

def S(v):
    return outer(v, v)

def B(v, w):
    return madd(outer(v, w), outer(w, v))

def br2(M, v):
    # T[i,j,k] = M[i,j]v[k] + v[i]M[j,k]
    return [[[M[i][j] * v[k] ^ (v[i] * M[j][k]) for k in range(n)]
             for j in range(n)] for i in range(n)]

# ---- 22 quadratic initials (mirror lie241.py) ----
rels, names = [], []
def add(m, name):
    rels.append(m); names.append(name)

add(S(V["c1"]), "c1^2"); add(S(V["c2"]), "c2^2")
for j in "12":
    add(madd(B(V["t3" + j], V["p3" + j]), S(V["t3" + j])), "tame3" + j)
    add(B(V["t5" + j], V["p5" + j]), "tame5" + j)
for j in "12":
    x, y, z = V["x" + j], V["y" + j], V["z" + j]
    add(madd(madd(S(y), B(x, y)), B(x, z)), "demuskin" + j)
    add(S(x), "x^2_" + j)
    add(B(x, y), "[x,y]_" + j)
    add(B(x, z), "[x,z]_" + j)
for j in "12":
    add(S(V["t3" + j]), "tau3sq" + j); add(S(V["t5" + j]), "tau5sq" + j)
    add(S(V["p3" + j]), "phi3sq" + j); add(S(V["p5" + j]), "phi5sq" + j)
assert len(rels) == 22

r2 = f2rank_int([mat_bits(m) for m in rels])
print("R2 rank:", r2, "(expect 21); L2 =", 36 - r2)
assert r2 == 21

# degree-1 ad ranks for both c1, c2
for cn in ("c1", "c2"):
    c = V[cn]
    img = [mat_bits(B(c, E[i])) for i in range(n)]
    base = [mat_bits(m) for m in rels]
    rk = f2rank_int(img + base) - f2rank_int(base)
    print(cn, "ad L1->gr2 rank:", rk, "(expect 7)")
    assert rk == 7

# ---- degree 3 (mirror lie241c.py) ----
Q = [m for m, nm in zip(rels, names) if nm != "demuskin1"]
assert len(Q) == 21
R3rows = [ten_bits(br2(r, E[k])) for r in Q for k in range(n)]
for j in "12":
    y, z = V["y" + j], V["z" + j]
    R3rows.append(ten_bits(br2(B(y, z), z)))
assert len(R3rows) == 170
r3 = f2rank_int(R3rows)
print("R3 span: 170 vectors, rank", r3, "(expect 142); syzygies:", 170 - r3)
assert r3 == 142

free2 = [S(E[i]) for i in range(n)] + \
        [B(E[i], E[j]) for i in range(n) for j in range(i + 1, n)]
assert len(free2) == 36
Qbits = [mat_bits(m) for m in Q]
comp, cur = [], list(Qbits)
for m in free2:
    trial = cur + [mat_bits(m)]
    if f2rank_int(trial) > f2rank_int(cur):
        cur = trial
        comp.append(m)
print("complement size:", len(comp), "(expect 15)")
assert len(comp) == 15

for cn in ("c1", "c2"):
    c = V[cn]
    imgs = [ten_bits(br2(u, c)) for u in comp]
    rk = f2rank_int(R3rows + imgs) - r3
    print(f"{cn} ad gr2->gr3 rank: {rk} (expect 8) => class 2^{7 + rk}")
    assert rk == 8

# ---- separation (d): neither c1 nor c2 in any decomposition span ----
def vrank(vecs):
    rows = []
    for v in vecs:
        b = 0
        for i, x in enumerate(v):
            if x:
                b |= 1 << i
        rows.append(b)
    return f2rank_int(rows)

spans = {"dy1": ["x1", "y1", "z1"], "dy2": ["x2", "y2", "z2"],
         "31": ["t31", "p31"], "32": ["t32", "p32"],
         "51": ["t51", "p51"], "52": ["t52", "p52"],
         "291": ["f291"], "292": ["f292"], "7": ["f7"]}
for cn in ("c1", "c2"):
    ok = True
    for k, gens in spans.items():
        A = [V[g] for g in gens]
        if vrank(A + [V[cn]]) == vrank(A):
            ok = False
            print("  ", cn, "lies in span of", k)
    print(cn, "separated from all decomposition spans:", ok)
    assert ok
assert V["c1"] != V["c2"]
print("c1bar != c2bar ok")

print("C86 INVOLUTION RANK CHECK PASS: both classes 2^15 in Gbar_B")
