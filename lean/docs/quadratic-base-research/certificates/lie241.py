"""Degree-2 and degree-3 restricted Lie layers for the tower over B=Q(sqrt 241).

Mirrors Lemma tw:new-retained-quotient of the manuscript, with 8 generators.
Linear parts of local generators come from kummer241.gp (Hilbert symbols).
"""
import itertools
import numpy as np

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
V = {k: np.array(v, dtype=np.uint8) for k, v in V.items()}

# ---- free associative algebra model: degree-2 tensors as n x n matrices over F2 ----
# restricted Lie degree 2 embeds via e_i^[2] -> X_i X_i, [e_i,e_j] -> X_i X_j + X_j X_i
def S(v):
    return np.outer(v, v) % 2          # (sum v_i X_i)^2


def B(v, w):
    return (np.outer(v, w) + np.outer(w, v)) % 2


def rank2(mats):
    """rank over F2 of a list of n x n matrices (as vectors of length n^2)."""
    if not mats:
        return 0
    M = np.array([m.flatten() for m in mats], dtype=np.uint8)
    return f2rank(M)


def f2rank(M):
    M = M.copy() % 2
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c]:
                piv = i
                break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        r += 1
        if r == rows:
            break
    return r


# quadratic initials of all relations of degree 2
rels = []
names = []
def add(m, name):
    rels.append(m)
    names.append(name)

add(S(V["c1"]), "c1^2")
add(S(V["c2"]), "c2^2")
for j in "12":
    add((B(V["t3" + j], V["p3" + j]) + S(V["t3" + j])) % 2, "tame3" + j)   # norm 3 = 3 mod 4
    add(B(V["t5" + j], V["p5" + j]), "tame5" + j)                              # norm 5 = 1 mod 4
for j in "12":
    x, y, z = V["x" + j], V["y" + j], V["z" + j]
    add((S(y) + B(x, y) + B(x, z)) % 2, "demuskin" + j)
    add(S(x), "x^2_" + j)
    add(B(x, y), "[x,y]_" + j)
    add(B(x, z), "[x,z]_" + j)
for j in "12":
    add(S(V["t3" + j]), "tau3sq" + j)
    add(S(V["t5" + j]), "tau5sq" + j)
    add(S(V["p3" + j]), "phi3sq" + j)
    add(S(V["p5" + j]), "phi5sq" + j)

print("number of quadratic relations", len(rels))
full = [S(np.eye(n, dtype=np.uint8)[i]) for i in range(n)] + \
       [B(np.eye(n, dtype=np.uint8)[i], np.eye(n, dtype=np.uint8)[j]) for i in range(n) for j in range(i + 1, n)]
print("free degree-2 dimension", rank2(full))
R = rank2(rels)
print("rank of quadratic initials", R, " -> L2 =", rank2(full) - R)
# redundancy: dropping one demuskin row
for drop in ["demuskin1", "demuskin2"]:
    rr = rank2([m for m, nm in zip(rels, names) if nm != drop])
    print("  rank without", drop, rr)


def indep_mod(vecs, base):
    return rank2(base + vecs) - rank2(base)


# retention checks
for j in "12":
    print("dyadic", j, " degree-1 rank of x,y,z:", f2rank(np.array([V["x" + j], V["y" + j], V["z" + j]])),
          " new degree-2 directions z^2,[y,z] mod relations:", indep_mod([S(V["z" + j]), B(V["y" + j], V["z" + j])], rels))
for p in ["31", "32", "51", "52"]:
    print("tame", p, " rank(tau,phi) =", f2rank(np.array([V["t" + p], V["p" + p]])))
for f in ["f291", "f292", "f7"]:
    print("cap", f, " S(frob) independent mod relations:", indep_mod([S(V[f])], rels))

# ad(c1): v -> B(c1, v) modulo relations
c = V["c1"]
img = [B(c, np.eye(n, dtype=np.uint8)[i]) for i in range(n)]
print("rank of ad(c1) on degree 1 modulo relations:", indep_mod(img, rels))

# separation of c1 (and c2) from decomposition spans
spans = {"dy1": ["x1", "y1", "z1"], "dy2": ["x2", "y2", "z2"], "31": ["t31", "p31"], "32": ["t32", "p32"],
         "51": ["t51", "p51"], "52": ["t52", "p52"], "291": ["f291"], "292": ["f292"], "7": ["f7"]}
for cname in ["c1", "c2"]:
    ok = True
    for k, gens in spans.items():
        A = np.array([V[g] for g in gens])
        if f2rank(np.vstack([A, V[cname]])) == f2rank(A):
            ok = False
            print("  ", cname, "lies in span of", k)
    print(cname, "separated from all decomposition spans:", ok)
