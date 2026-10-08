"""The dyadic group D of order 32 (normal form x^a1 y^a2 z^a3 w^a4) and Jennings series of subgroups."""
import itertools
from functools import lru_cache

def mul(g, h):
    a1, a2, a3, a4 = g
    b1, b2, b3, b4 = h
    return ((a1 + b1) % 2, (a2 + b2) % 2, (a3 + b3) % 4, (a4 + b4 + a3 * b2) % 2)

E = (0, 0, 0, 0)
ELEMS = [(a, b, c, d) for a in range(2) for b in range(2) for c in range(4) for d in range(2)]

def inv(g):
    for h in ELEMS:
        if mul(g, h) == E:
            return h

def comm(g, h):
    return mul(mul(inv(g), inv(h)), mul(g, h))

X, Y, Z, W = (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)
assert comm(Y, Z) in (W,), comm(Y, Z)

def gen(gens):
    S = {E}
    frontier = [E]
    while frontier:
        nf = []
        for s in frontier:
            for g in gens:
                p = mul(s, g)
                if p not in S:
                    S.add(p); nf.append(p)
        frontier = nf
    return frozenset(S)

def subgroup_gen(sets):
    gens = set()
    for s in sets:
        gens |= set(s)
    return gen(list(gens) or [E])

def zassenhaus(G):
    """Zassenhaus (Jennings) filtration D_n of the group G (a frozenset), via
    D_1=G, D_n = <[D_i,D_j] (i+j>=n), D_ceil(n/2)^2>."""
    G = frozenset(G)
    Ds = {1: G}
    n = 2
    while True:
        gens = set()
        for i in range(1, n):
            j = n - i
            if j < 1: continue
            for a in Ds[i]:
                for b in Ds[max(j,1)]:
                    gens.add(comm(a, b))
        half = (n + 1) // 2
        for a in Ds[half]:
            gens.add(mul(a, a))
        Dn = gen(list(gens))
        Ds[n] = Dn
        if len(Dn) == 1:
            break
        n += 1
    return Ds

def jennings_dims(G):
    Ds = zassenhaus(G)
    dims = []
    n = 1
    import math
    while n in Ds and len(Ds[n]) > 1:
        dims.append(int(round(math.log2(len(Ds[n]) / len(Ds[n + 1])))))
        n += 1
    return dims  # dims[i] = dim gr_{i+1}

def hilbert(dims, t):
    h = 1.0
    for i, d in enumerate(dims):
        h *= (1 + t ** (i + 1)) ** d
    return h

if __name__ == "__main__":
    D = gen([X, Y, Z])
    print("|D|", len(D), "jennings", jennings_dims(D))
    # characters of D: D -> F2 via (a1,a2,a3 mod 2)
    for chi in itertools.product(range(2), repeat=3):
        if chi == (0, 0, 0): continue
        K = frozenset(g for g in D if (chi[0]*g[0] + chi[1]*g[1] + chi[2]*(g[2] % 2)) % 2 == 0)
        print("ker chi", chi, len(K), jennings_dims(K))
