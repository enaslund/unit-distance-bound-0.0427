import _paths  # noqa: F401
import sys, itertools, math

import census241 as C
from census241 import legendre, sqrtmod, KB, NORMS, D, primes_upto
delta = 0.045; t = 0.28; shadow = 2.0
def g(q):
    best = max(math.log(k+1) - delta*k*math.log(q) for k in range(0, 80))
    return best + math.log(1 - 1/q)
# primes of B (excluding S-primes 2,3,5 and 241) with Frobenius vectors
pr = []
for p in primes_upto(200000):
    if p in (2, 3, 5): continue
    if p == D:
        res = [(a*pow(den, -1, p)) % p for (a, b, den) in KB]
        pr.append((p, sum((1 << i) for i, a in enumerate(res) if legendre(a, p) == -1), 2))  # fraction 1 (e=2)
    elif legendre(D, p) == 1:
        r = sqrtmod(D, p)
        for rr in (r, p - r):
            res = [((a + b*rr)*pow(den, -1, p)) % p for (a, b, den) in KB]
            pr.append((p, sum((1 << i) for i, a in enumerate(res) if legendre(a, p) == -1), 1))
    else:
        if p*p > 200000: continue
        pr.append((p*p, sum((1 << i) for i, nm in enumerate(NORMS) if legendre(nm, p) == -1), 1))
def vec(s): return int(s[::-1], 2)
c2 = vec('11000101')
# current caps: 29a,29b,7 (u4) ~ value 0.0294 (both 29) + 0.0035 ; ignore small
vals = {}
for (N, v, kind) in pr:
    val = g(N)/2 if kind == 1 else g(N)/2   # 241 ramified: type (2,1): log F/(2) with fraction 1 -> g/2 too
    if val > 0: vals.setdefault(v, []).append((N, val))
def span(basis):
    s = {0}
    for b in basis:
        s |= {x ^ b for x in s}
    return s
best = []
vecs = list(range(1, 256))
for w in (1, 2, 3):
    seen = set()
    for basis in itertools.combinations(vecs, w):
        S = span(basis)
        if len(S) != 2**w: continue
        key = frozenset(S)
        if key in seen: continue
        seen.add(key)
        items = []
        for v in S:
            if v == 0: continue
            for (N, val) in vals.get(v, []):
                items.append((val, N, v))
        splitreal = c2 in S
        items.sort(reverse=True)
        # greedy: take primes whose val > shadow*t^2 ; first w independent cost t, rest t^2
        gain = 0.44 if splitreal else 0.0
        cost = w*t + (t*t if splitreal else 0) - (0.061 if splitreal else 0)
        taken = []
        for val, N, v in items:
            if val > shadow*t*t:
                gain += val; cost += t*t; taken.append(N)
        net = gain - shadow*cost
        best.append((net, w, [format(b, '08b')[::-1] for b in basis], splitreal, round(gain, 3), round(cost, 3), taken[:12]))
best.sort(reverse=True)
for b in best[:12]: print(b)
