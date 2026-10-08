"""C161 second-review containment checker (stdlib only, fresh seed 161).

Independent reimplementation: V parsed from lie241.py source text,
little-endian bit tensors, lowbit elimination, own trip4 + word algebra.
Checks H1a/H2/H3 containment R4(TRUE) subset TOTAL before the separator,
plus falsification probes for arbitrary conjugates.

Usage: python3 research/2026-10-muse-involution-class/code/C161/c161_containment_check.py
"""
import random
import re
import sys

SEED = 161
random.seed(SEED)

PASS = []
def check(name, cond, detail=""):
    assert cond, "FAIL %s %s" % (name, detail)
    PASS.append(name)
    print("  ok %-42s %s" % (name, detail))

# ---------------- parse V from source (no numpy) ----------------
src = open("papers/0.04273/certificates/lie241.py").read()
Vm = {}
for k, b in re.findall(r'"([a-z0-9]+)": \[([0-9,\s]+)\]', src):
    vec = [int(x) for x in b.split(",")]
    if len(vec) == 8 and k not in Vm:
        Vm[k] = vec
need = ["c1", "c2", "x1", "y1", "z1", "x2", "y2", "z2",
        "t31", "p31", "t32", "p32", "t51", "p51", "t52", "p52",
        "f291", "f292", "f7"]
assert all(k in Vm for k in need), sorted(Vm)
P411 = [0, 0, 1, 1, 1, 0, 0, 0]
print("V parsed: %d keys" % len(Vm))

# ---------------- little-endian bit tensors ----------------
def enc(idx):
    p = 0
    for k, i in enumerate(idx):
        p += i * (8 ** k)
    return 1 << p

def dec(bit, deg):
    return [(bit // (8 ** k)) % 8 for k in range(deg)]

def bits_of(v):
    o = []
    while v:
        b = (v & (-v)).bit_length() - 1
        o.append(b)
        v ^= 1 << b
    return o

def mul(A, da, B, db):
    v = 0
    for ba in bits_of(A):
        ia = dec(ba, da)
        for bb in bits_of(B):
            v ^= enc(tuple(ia + dec(bb, db)))
    return v

def gen(l):
    return enc((l,))

def br(A, da, B, db):
    return mul(A, da, B, db) ^ mul(B, db, A, da)

def sqm(A, da):
    return mul(A, da, A, da)

def t1v(v8):
    v = 0
    for i in range(8):
        if v8[i] % 2:
            v ^= gen(i)
    return v

def Sm(v8):
    # (sum v_i X_i)^2
    t = t1v(v8)
    return mul(t, 1, t, 1)

def Bm(v8, w8):
    return br(t1v(v8), 1, t1v(w8), 1)

def arb2(v8):
    v = 0
    for i in range(8):
        for j in range(i + 1, 8):
            if v8[i] and v8[j]:
                v ^= enc((i, j))
    return v

def arb3bits(v8):
    v = 0
    for i in range(8):
        for j in range(i + 1, 8):
            for k in range(j + 1, 8):
                if v8[i] and v8[j] and v8[k]:
                    v ^= enc((i, j, k))
    return v

# lowbit elimination (author uses highbit)
def rb_low(rows):
    bas = {}
    for v in rows:
        w = v
        while w:
            p = (w & (-w)).bit_length() - 1
            if p in bas:
                w ^= bas[p]
            else:
                bas[p] = w
                break
    return len(bas), bas

def cred_low(v, bas):
    w, r = v, 0
    while w:
        p = (w & (-w)).bit_length() - 1
        if p in bas:
            w ^= bas[p]
        else:
            r ^= 1 << p
            w ^= 1 << p
    return r

def rb_high(rows):
    bas = {}
    for v in rows:
        w = v
        while w:
            p = w.bit_length() - 1
            if p in bas:
                w ^= bas[p]
            else:
                bas[p] = w
                break
    return len(bas), bas

def cred_high(v, bas):
    w, r = v, 0
    while w:
        p = w.bit_length() - 1
        if p in bas:
            w ^= bas[p]
        else:
            r ^= 1 << p
            w ^= 1 << p
    return r


# ---------------- P1: ranks ----------------
print("== P1 ranks ==")
E8 = [[1 if i == j else 0 for j in range(8)] for i in range(8)]
L2sp = [Sm(E8[i]) for i in range(8)]
for i in range(8):
    for j in range(i + 1, 8):
        L2sp.append(Bm(E8[i], E8[j]))
rL2, bL2 = rb_low(L2sp)
check("L2=36", rL2 == 36, str(rL2))
L2bas = list(bL2.values())
# 21 quadrics (drop demuskin1): 2 real + 4 tame + 1 demuskin2 + 6 dyadic + 8 tame-sq
Q2 = [Sm(Vm["c1"]), Sm(Vm["c2"])]
Q2.append(Bm(Vm["t31"], Vm["p31"]) ^ Sm(Vm["t31"]))
Q2.append(Bm(Vm["t32"], Vm["p32"]) ^ Sm(Vm["t32"]))
Q2.append(Bm(Vm["t51"], Vm["p51"]))
Q2.append(Bm(Vm["t52"], Vm["p52"]))
x2, y2, z2 = Vm["x2"], Vm["y2"], Vm["z2"]
Q2.append(Sm(y2) ^ Bm(x2, y2) ^ Bm(x2, z2))  # demuskin2 = rho_p2
for j in "12":
    Q2.append(Sm(Vm["x" + j]))
    Q2.append(Bm(Vm["x" + j], Vm["y" + j]))
    Q2.append(Bm(Vm["x" + j], Vm["z" + j]))
for k in ["t31", "t32", "t51", "t52"]:
    Q2.append(Sm(Vm[k]))
for k in ["p31", "p32", "p51", "p52"]:
    Q2.append(Sm(Vm[k]))
assert len(Q2) == 21
rR2, bR2 = rb_low(Q2)
check("R2=21", rR2 == 21, str(rR2))
# all 22 (add demuskin1) still rank 21
x1, y1, z1 = Vm["x1"], Vm["y1"], Vm["z1"]
dem1 = Sm(y1) ^ Bm(x1, y1) ^ Bm(x1, z1)
r22, _ = rb_low(Q2 + [dem1])
check("22 initials rank 21", r22 == 21, str(r22))
# L3 / I3
L3rows = [br(M, 2, gen(c), 1) for M in L2sp for c in range(8)]
rL3, bL3 = rb_low(L3rows)
check("L3=168", rL3 == 168, str(rL3))
cub3 = []
for j in "12":
    M = Bm(Vm["y" + j], Vm["z" + j])
    T = 0
    for ell in range(8):
        if Vm["z" + j][ell]:
            T ^= br(M, 2, gen(ell), 1)
    cub3.append(T)
R3rows = [br(q, 2, gen(i), 1) for q in Q2 for i in range(8)] + cub3
assert len(R3rows) == 170
rI3, bI3 = rb_low(R3rows)
check("I3=142", rI3 == 142, str(rI3))
rbrack = rb_low(R3rows[:168])[0]
check("brackets=140", rbrack == 140, str(rbrack))
check("cubics add 2", rI3 - rbrack == 2)
# L4 / I4 (41-cap)
L3bas = list(bL3.values())
free4 = [br(T, 3, gen(l), 1) for T in L3bas for l in range(8)]
free4 += [sqm(M, 2) for M in L2bas]
rF4, bF4 = rb_low(free4)
check("L4=1044", rF4 == 1044, str(rF4))
R4base = []
for q in Q2:
    for i in range(8):
        T = br(q, 2, gen(i), 1)
        for j in range(8):
            R4base.append(br(T, 3, gen(j), 1))
for T in cub3:
    for l in range(8):
        R4base.append(br(T, 3, gen(l), 1))
for j in "12":
    R4base.append(sqm(Sm(Vm["z" + j]), 2))
    R4base.append(sqm(Bm(Vm["y" + j], Vm["z" + j]), 2))
R4base += [sqm(q, 2) for q in Q2]
for vv in (Vm["f291"], Vm["f292"], P411):
    R4base.append(sqm(Sm(vv), 2))
rI4, bI4 = rb_low(R4base)
check("I4=963", rI4 == 963, str(rI4))
# cross-check with highbit elimination
check("I4=963 highbit", rb_high(R4base)[0] == 963)
check("I3=142 highbit", rb_high(R3rows)[0] == 142)
# foldings
bad = sum(1 for r in Q2 for t in L2bas if cred_low(br(r, 2, t, 2), bI4) != 0)
check("[R2,L2] in I4 756", bad == 0, "%d bad" % bad)
bad3 = sum(1 for r in R3rows for l in range(8) if cred_low(br(r, 3, gen(l), 1), bI4) != 0)
check("[R3,L1] in I4 1360", bad3 == 0, "%d bad" % bad3)
# [I3,L1] subset I4 via I3 basis
I3bas = list(bI3.values())
badI = sum(1 for r in I3bas for l in range(8) if cred_low(br(r, 3, gen(l), 1), bI4) != 0)
check("[I3,L1] in I4", badI == 0, "%d bad of %d" % (badI, len(I3bas) * 8))
# S(P41) outside R2 (cap compatibility)
def in_span_low(v, bas):
    return cred_low(v, bas) == 0
check("S(P41[1]) outside R2", not in_span_low(Sm(P411), bR2))
check("S(P41[2]) outside R2",
      not in_span_low(Sm([0, 0, 1, 1, 0, 1, 0, 0]), bR2))
check("S(f291) outside R2", not in_span_low(Sm(Vm["f291"]), bR2))
check("S(f292) outside R2", not in_span_low(Sm(Vm["f292"]), bR2))

QLABEL = ["real1", "real2", "tame_t31", "tame_t32", "tame_t51",
          "tame_t52", "rho_p2", "x2_1", "xy_1", "xz_1", "x2_2",
          "xy_2", "xz_2", "tau2_t31", "tau2_t32", "tau2_t51",
          "tau2_t52", "phi2_p31", "phi2_p32", "phi2_p51", "phi2_p52"]
assert len(QLABEL) == 21

# ---------------- P2: syzygy kernel + omega vacuity ----------------
print("== P2 kernel ==")
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
check("kernel=28", len(ker) == 28, str(len(ker)))
for c in ker:
    s = 0
    for r in range(170):
        if (c >> r) & 1:
            s ^= R3rows[r]
    assert s == 0
print("  all 28 kernel vectors verify")
om = sum(1 for c in ker if (c >> 168) & 3)
check("omega vacuous 0/28", om == 0, "%d use omega" % om)
# every kernel vector has D=0 => full kernel D-free (span of basis)
# p2-slot usage
p2idx = QLABEL.index("rho_p2")
uses_p2 = [s for s in range(28)
           if any((ker[s] >> (p2idx * 8 + i)) & 1 for i in range(8))]
print("  syzygies using rho_p2 slots: %s" % uses_p2)
check("4 p2 syzygies", len(uses_p2) == 4, str(uses_p2))
nonp2 = [s for s in range(28) if s not in uses_p2]
check("24 non-p2", len(nonp2) == 24)
# all 21 Qnames occur
used_names = set()
for c in ker:
    for k in range(168):
        if (c >> k) & 1:
            used_names.add(QLABEL[k // 8])
check("all 21 Qnames occur", len(used_names) == 21, str(sorted(used_names)))

# ---------------- P3: trip4 identities (fresh seed) ----------------
print("== P3 trip identities ==")

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

def rand_trip(d1=True, d2=True, d3=True, d4=True):
    return (random.getrandbits(8) if d1 else 0,
            random.getrandbits(64) if d2 else 0,
            random.getrandbits(512) if d3 else 0,
            random.getrandbits(4096) if d4 else 0)

# D1 master: ([A,B])_4 for A in D2, B in D1, full random higher parts
n = 0
for t in range(20):
    A = (0, random.getrandbits(64), random.getrandbits(512),
         random.getrandbits(4096))
    B = rand_trip()
    got = gcomm4(A, B)[3]
    want = (br(A[2], 3, B[0], 1) ^ br(A[1], 2, B[1], 2)
            ^ mul(br(A[1], 2, B[0], 1), 3, B[0], 1))
    assert got == want, t
    n += 1
check("master 20/20", n == 20)
# exhaustive over B1 (all 256) with fixed random higher parts
A = (0, random.getrandbits(64), random.getrandbits(512),
     random.getrandbits(4096))
B234 = (random.getrandbits(64), random.getrandbits(512),
        random.getrandbits(4096))
ne = 0
for b1 in range(256):
    B = (b1, B234[0], B234[1], B234[2])
    got = gcomm4(A, B)[3]
    want = (br(A[2], 3, B[0], 1) ^ br(A[1], 2, B[1], 2)
            ^ mul(br(A[1], 2, B[0], 1), 3, B[0], 1))
    assert got == want, b1
    ne += 1
check("master exhaustive-B1 256", ne == 256)
# deg-3 identity: ([A,B])_3 = [(A)_2,V_B] for A in D2 (B_2/B_3 cancel)
# need trip3: compute via trip4 dropping deg4
def gmul3(a, b):
    return gmul4((a[0], a[1], a[2], 0), (b[0], b[1], b[2], 0))[:3]
def ginv3(a):
    return ginv4((a[0], a[1], a[2], 0))[:3]
def gcomm3(a, b):
    return gmul3(gmul3(a, b), gmul3(ginv3(a), ginv3(b)))
n3 = 0
for t in range(20):
    A = (0, random.getrandbits(64), random.getrandbits(512))
    B = (random.getrandbits(8), random.getrandbits(64),
         random.getrandbits(512))
    got = gcomm3(A, B)[2]
    assert got == br(A[1], 2, B[0], 1), t
    n3 += 1
check("deg3 identity 20/20", n3 == 20)
# E-identity corollary: ([A,x])_4 with x free generator (B=(X,0,0,0))
ne2 = 0
for t in range(16):
    A = (0, random.getrandbits(64), random.getrandbits(512),
         random.getrandbits(4096))
    x = gen(random.randrange(8))
    B = (x, 0, 0, 0)
    got = gcomm4(A, B)[3]
    want = br(A[2], 3, x, 1) ^ mul(br(A[1], 2, x, 1), 3, x, 1)
    assert got == want, t
    # no (A)_4 dependence: flip A4, same result
    A2 = (A[0], A[1], A[2], A[3] ^ 1)
    assert gcomm4(A2, B)[3] == got
    ne2 += 1
check("E-identity + a4-cancel 16/16", ne2 == 16)
# D2-D2 bracket: ([A,U])_4 = [(A)_2,(U)_2] for A,U in D2
n22 = 0
for t in range(20):
    A = (0, random.getrandbits(64), random.getrandbits(512),
         random.getrandbits(4096))
    U = (0, random.getrandbits(64), random.getrandbits(512),
         random.getrandbits(4096))
    got = gcomm4(A, U)[3]
    assert got == br(A[1], 2, U[1], 2), t
    n22 += 1
check("[D2,D2]_4 = bracket 20/20", n22 == 20)
# D3 additivity: (AB)_4 = (A)_4+(B)_4 for A,B in D3
na = 0
for t in range(10):
    A = (0, 0, random.getrandbits(512), random.getrandbits(4096))
    B = (0, 0, random.getrandbits(512), random.getrandbits(4096))
    assert gmul4(A, B)[3] == (A[3] ^ B[3]), t
    na += 1
check("D3 additivity 10/10", na == 10)
# cubic conjugate: (w^g)_4 = (w)_4 + [(w)_3,V_g] for w in D3
nc = 0
for t in range(10):
    w = (0, 0, random.getrandbits(512), random.getrandbits(4096))
    gg = rand_trip()
    conj = gmul4(gmul4(ginv4(gg), w), gg)
    assert conj[3] == (w[3] ^ br(w[2], 3, gg[0], 1)), t
    nc += 1
check("cubic-conj formula 10/10", nc == 10)
# quartic invariance: (Q^g)_4 = (Q)_4 for Q in D4
nq = 0
for t in range(10):
    Q = (0, 0, 0, random.getrandbits(4096))
    gg = rand_trip()
    conj = gmul4(gmul4(ginv4(gg), Q), gg)
    assert conj[3] == Q[3], t
    nq += 1
check("quartic invariance 10/10", nq == 10)
# inverse in D2: (A^-1)_3 = (A)_3; (A^-1)_2 = (A)_2 + (A)_1^2
ni = 0
for t in range(10):
    A = (0, random.getrandbits(64), random.getrandbits(512),
         random.getrandbits(4096))
    Ai = ginv4(A)
    assert Ai[2] == A[2] and Ai[1] == A[1], t
    ni += 1
check("D2 inverse deg2/3 10/10", ni == 10)
# tower-convention commutator (tower.tex line 28: [g,h]=g^-1 h^-1 g h);
# author's gcomm4 is a.b.a^-1.b^-1 (see P3b for the difference)
def gcommT(a, b):
    return gmul4(gmul4(ginv4(a), ginv4(b)), gmul4(a, b))

# pairing: rho^g rho^h = rho^2 [rho,g][rho,h] mod D5 (gr4 equal, tower)
npair = 0
for t in range(10):
    R = (0, random.getrandbits(64), random.getrandbits(512),
         random.getrandbits(4096))
    g = rand_trip()
    h = rand_trip()
    Rg = gmul4(gmul4(ginv4(g), R), g)
    Rh = gmul4(gmul4(ginv4(h), R), h)
    lhs = gmul4(Rg, Rh)[3]
    R2 = gmul4(R, R)
    c1 = gcommT(R, g)
    c2 = gcommT(R, h)
    rhs = gmul4(gmul4(R2, c1), c2)[3]
    assert lhs == rhs, t
    npair += 1
check("pairing rho^g rho^h 10/10", npair == 10)
# [a,bc] = [a,c][a,b][[a,b],c] exact (tower), used by C126
nabc = 0
for t in range(6):
    a = (0, random.getrandbits(64), random.getrandbits(512),
         random.getrandbits(4096))
    b = (random.getrandbits(8), 0, 0, 0)
    c = (random.getrandbits(8), 0, 0, 0)
    bc = gmul4(b, c)
    assert gcommT(a, bc) == gmul4(gmul4(gcommT(a, c), gcommT(a, b)),
                                  gcommT(gcommT(a, b), c)), t
    nabc += 1
check("[a,bc] tower exact 6/6", nabc == 6)

# P3b: commutator-convention difference (author a.b.a^-1.b^-1 vs tower)
print("== P3b conventions ==")
# D3 x D1: both agree exactly with [w3,V] (C93 S4b convention-free)
ncd = 0
for t in range(10):
    w = (0, 0, random.getrandbits(512), random.getrandbits(4096))
    gg = rand_trip()
    t4 = gcommT(w, gg)[3]
    a4 = gcomm4(w, gg)[3]
    assert t4 == br(w[2], 3, gg[0], 1) and a4 == br(w[2], 3, gg[0], 1), t
    ncd += 1
check("D3xD1 both = [w3,V] 10/10", ncd == 10)
# D2 x free-gen: tower vs author differ, but diff in I4 when (R)_2 in R2
ndiff = ndi4 = 0
for qi, q in enumerate(Q2):
    for l in range(8):
        R = (0, q, random.getrandbits(512), random.getrandbits(4096))
        X = (gen(l), 0, 0, 0)
        d = gcommT(R, X)[3] ^ gcomm4(R, X)[3]
        ndiff += 1
        if cred_low(d, bI4) == 0:
            ndi4 += 1
check("tower-author diff in I4 168/168", ndi4 == ndiff,
      "%d/%d" % (ndi4, ndiff))
# diff independent of R_3/R_4 (same [(R)_3,X] term both sides)
R = (0, Q2[0], random.getrandbits(512), random.getrandbits(4096))
X = (gen(0), 0, 0, 0)
d0 = gcommT(R, X)[3] ^ gcomm4(R, X)[3]
R2v = (R[0], R[1], R[2] ^ 1, R[3] ^ 1)
check("diff R3/R4-free", d0 == gcommT(R2v, X)[3] ^ gcomm4(R2v, X)[3])
# syzygy-level: tower-model vs author-model differ by I4 (all 28, ARB base)
# (uses F3m/modelF defined in P5 -- deferred check recorded in P5b)

# ---------------- P4: occurrence/exponent parity (own word algebra) ----------------
print("== P4 word parity ==")

def sq(a):
    return [(a, 1), (a, 1)]

def comm(a, b):
    return [(a, 1), (b, 1), (a, -1), (b, -1)]

def tame(t, f, p):
    return [(f, 1), (t, 1), (f, -1)] + [(t, -1)] * p

def omega(y, z):
    c = comm(y, z)
    ci = [(a, -e) for (a, e) in reversed(c)]
    return c + [(z, 1)] + ci + [(z, -1)]

def wp(x, y, z):
    return sq(y) + comm(x, y) + comm(x, z)

def rstand(x, y, z):
    return comm(x, z) + comm(x, y) + sq(y)

def occ_exp(w):
    occ, exp = {}, {}
    for a, e in w:
        occ[a] = occ.get(a, 0) + 1
        exp[a] = exp.get(a, 0) + e
    return occ, exp

def even_word(name, w):
    occ, exp = occ_exp(w)
    assert all(v % 2 == 0 for v in occ.values()), (name, occ)
    assert all(v % 2 == 0 for v in exp.values()), (name, exp)
    # occ == exp mod 2 always
    for a in set(occ) | set(exp):
        assert occ.get(a, 0) % 2 == exp.get(a, 0) % 2, name
    return occ, exp

o, e = even_word("square", sq("g"))
check("square occ2 exp2", o == {"g": 2} and e == {"g": 2})
o, e = even_word("comm", comm("a", "b"))
check("comm 2/2, exp 0/0", o == {"a": 2, "b": 2} and e == {"a": 0, "b": 0})
o, e = even_word("tame p=3", tame("t", "f", 3))
check("tame3 f2 t4 / exp 0,-2", o == {"f": 2, "t": 4} and e == {"f": 0, "t": -2})
o, e = even_word("tame p=5", tame("t", "f", 5))
check("tame5 f2 t6 / exp 0,-4", o == {"f": 2, "t": 6} and e == {"f": 0, "t": -4})
o, e = even_word("omega", omega("y", "z"))
check("omega Y4 Z6 exp0", o == {"y": 4, "z": 6} and e == {"y": 0, "z": 0})
o, e = even_word("Wp", wp("x", "y", "z"))
check("Wp X4 Y4 Z2", o == {"x": 4, "y": 4, "z": 2} and e == {"x": 0, "y": 2, "z": 0})
o, e = even_word("rstand", rstand("x", "y", "z"))
check("rstand X4 Y4 Z2", o == {"x": 4, "y": 4, "z": 2})
# syzygy words inherit evenness: [rho,x] doubles rho occ + 2 for x
# check on one example: rho=tame(t,f,3) inside [rho,x]
rho = tame("t", "f", 3)
brw = rho + [("x", 1)] + [(a, -e2) for (a, e2) in reversed(rho)] + [("x", -1)]
o, e = even_word("[tame,x]", brw)
check("[rho,x] even", o["t"] == 8 and o["f"] == 4 and o["x"] == 2)

# ---------------- P5: model/LV/TOTAL_full240/ad3/witness ----------------
print("== P5 full-240 ==")
LIFTS = ["i1", "i2", "t31", "p31", "t32", "p32", "t51", "p51",
         "t52", "p52", "x1", "y1", "z1", "x2", "y2", "z2"]
LVEC = {"i1": Vm["c1"], "i2": Vm["c2"]}
for kk in LIFTS[2:]:
    LVEC[kk] = Vm[kk]
TAME_P = {"t31": 3, "t32": 3, "t51": 5, "t52": 5}
TAME_PHI = {"t31": "p31", "t32": "p32", "t51": "p51", "t52": "p52"}

def arb_trip4(v8):
    return (t1v(v8), arb2(v8), arb3bits(v8), 0)

def arb_trip3(v8):
    return (t1v(v8), arb2(v8), arb3bits(v8))

def rho_trip4(lab, L):
    # L: lift -> trip4; returns trip4 of relator (non-p2)
    if lab == "real1":
        return gpow4(L["i1"], 2)
    if lab == "real2":
        return gpow4(L["i2"], 2)
    if lab.startswith("tame_"):
        tk = lab[5:]
        pk, p = TAME_PHI[tk], TAME_P[tk]
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

def rho_trip3(lab, L):
    if lab == "real1":
        a = L["i1"]
        return gmul3(a, a)
    if lab == "real2":
        a = L["i2"]
        return gmul3(a, a)
    if lab.startswith("tame_"):
        tk = lab[5:]
        pk, p = TAME_PHI[tk], TAME_P[tk]
        T, F = L[tk], L[pk]
        Fi = ginv3(F)
        # F*T*Fi*T^{-p}
        r = gmul3(gmul3(gmul3(F, T), Fi), gpow3(T, -p))
        return r
    if lab.startswith("xy_"):
        j = lab[3:]
        return gcomm3(L["x" + j], L["y" + j])
    if lab.startswith("xz_"):
        j = lab[3:]
        return gcomm3(L["x" + j], L["z" + j])
    if lab.startswith("x2_"):
        a = L["x" + lab[3:]]
        return gmul3(a, a)
    if lab.startswith("tau2_") or lab.startswith("phi2_"):
        a = L[lab[5:]]
        return gmul3(a, a)
    raise AssertionError(lab)

def gpow3(a, e):
    if e == 0:
        return (0, 0, 0)
    if e < 0:
        return gpow3(ginv3(a), -e)
    r = (0, 0, 0)
    for _ in range(e):
        r = gmul3(r, a)
    return r

ALA3 = {kk: arb_trip3(v) for kk, v in LVEC.items()}
ALA4 = {kk: arb_trip4(v) for kk, v in LVEC.items()}
# (rho_ARB)_2 == recorded Q2 for all 20 non-p2 labels
QI = {lab: Q2[i] for i, lab in enumerate(QLABEL)}
for lab in QLABEL:
    if lab == "rho_p2":
        continue
    r = rho_trip3(lab, ALA3)
    assert r[0] == 0 and r[1] == QI[lab], lab
print("  20 non-p2 (rho_ARB)_2 == recorded")
# Wp at p2
def wp_trip3(L):
    return gmul3(gmul3(L["y2"], L["y2"]),
                 gmul3(gcomm3(L["x2"], L["y2"]),
                       gcomm3(L["x2"], L["z2"])))
WpA = wp_trip3(ALA3)
DEM2 = Sm(y2) ^ Bm(x2, y2) ^ Bm(x2, z2)
check("(Wp_ARB)_2 == deminit", WpA[0] == 0 and WpA[1] == DEM2)
K = WpA[2]
# r_stand
def rstand_trip3(L):
    return gmul3(gcomm3(L["x2"], L["z2"]),
                 gmul3(gcomm3(L["x2"], L["y2"]),
                       gmul3(L["y2"], L["y2"])))
RSA = rstand_trip3(ALA3)
check("rstand_2 == deminit", RSA[0] == 0 and RSA[1] == DEM2)
FSTAND = RSA[2]
# LVa / Fpin
Xv2, Yv2, Zv2 = t1v(Vm["x2"]), t1v(Vm["y2"]), t1v(Vm["z2"])
ay2, az2 = arb2(Vm["y2"]), arb2(Vm["z2"])
LVa = br(Yv2, 1, ay2, 2) ^ br(Xv2, 1, ay2, 2) ^ br(Xv2, 1, az2, 2)
FPIN = K ^ LVa
check("LVa outside I3", cred_low(LVa, bI3) != 0)
out8 = sum(1 for l in range(8) if cred_low(br(LVa, 3, gen(l), 1), bI4) != 0)
check("[LVa,X] outside I4 8/8", out8 == 8, str(out8))
# F3m model base
F3m = {}
for lab in QLABEL:
    if lab == "rho_p2":
        F3m[lab] = FPIN
    else:
        F3m[lab] = rho_trip3(lab, ALA3)[2]
# OM4a via trip4
def omega_trip4(L, j):
    return gcomm4(gcomm4(L["y" + j], L["z" + j]), L["z" + j])
OM4 = {"1": omega_trip4(ALA4, "1")[3], "2": omega_trip4(ALA4, "2")[3]}
# model corrs (Fpin)
modelF = []
for c in ker:
    t = 0
    for k in range(168):
        if (c >> k) & 1:
            nm = QLABEL[k // 8]
            t ^= br(F3m[nm], 3, gen(k % 8), 1)
            t ^= mul(br(Q2[k // 8], 2, gen(k % 8), 1), 3, gen(k % 8), 1)
    if (c >> 168) & 1:
        t ^= OM4["1"]
    if (c >> 169) & 1:
        t ^= OM4["2"]
    modelF.append(t)
mspanF = rb_low(list(bI4.values()) + modelF)[0] - rI4
check("Fpin model span 4", mspanF == 4, str(mspanF))
# K-model (Fpin -> K at p2 slots)
vlist = []
modelK = []
for c in ker:
    t = 0
    for k in range(168):
        if (c >> k) & 1 and QLABEL[k // 8] == "rho_p2":
            t ^= br(LVa, 3, gen(k % 8), 1)
    vlist.append(t)
for s in range(28):
    modelK.append(modelF[s] ^ vlist[s])
mspanK = rb_low(list(bI4.values()) + modelK)[0] - rI4
print("  K-model span mod I4: %d" % mspanK)
check("K-model span 2", mspanK == 2, str(mspanK))

# LV machinery (own perturbation for tame)
def eval_rho3(T, F, p):
    return gmul3(gmul3(gmul3(F, T), ginv3(F)), gpow3(T, -p))

tame_cross = {}
for tk in TAME_P:
    pk, p = TAME_PHI[tk], TAME_P[tk]
    t0, f0 = ALA3[tk], ALA3[pk]
    base = eval_rho3(t0, f0, p)[2]
    ct, cp = [], []
    for fb in L2bas:
        tp = (t0[0], t0[1] ^ fb, t0[2])
        ct.append(eval_rho3(tp, f0, p)[2] ^ base)
        fp = (f0[0], f0[1] ^ fb, f0[2])
        cp.append(eval_rho3(t0, fp, p)[2] ^ base)
    tame_cross[tk] = (ct, cp)

def r2_cross(vecs):
    Xv, Yv, Zv = (t1v(v) for v in vecs)
    cx = [br(fb, 2, Yv, 1) ^ br(fb, 2, Zv, 1) for fb in L2bas]
    cy = [br(Yv, 1, fb, 2) ^ br(Xv, 1, fb, 2) for fb in L2bas]
    cz = [br(Xv, 1, fb, 2) for fb in L2bas]
    return cx, cy, cz

CX2, CY2, CZ2 = r2_cross((Vm["x2"], Vm["y2"], Vm["z2"]))
# LV_Wp == LV_r lists (same formulas; conclusion via C116 lemma)
lvwx = [br(fb, 2, Yv2, 1) ^ br(fb, 2, Zv2, 1) for fb in L2bas]
lvwy = [br(Yv2, 1, fb, 2) ^ br(Xv2, 1, fb, 2) for fb in L2bas]
lvwz = [br(Xv2, 1, fb, 2) for fb in L2bas]
check("LV_Wp lists == LV_r lists", lvwx == CX2 and lvwy == CY2 and lvwz == CZ2)

def lv_quad(lab, lift, tj):
    fb = L2bas[tj]
    if lab in ("real1", "real2"):
        g = "i1" if lab == "real1" else "i2"
        if lift != g:
            return 0
        return br(t1v(LVEC[g]), 1, fb, 2)
    if lab.startswith("tame_"):
        tk = lab[5:]
        ct, cp = tame_cross[tk]
        if lift == tk:
            return ct[tj]
        if lift == TAME_PHI[tk]:
            return cp[tj]
        return 0
    if lab == "rho_p2":
        if lift == "x2":
            return CX2[tj]
        if lift == "y2":
            return CY2[tj]
        if lift == "z2":
            return CZ2[tj]
        return 0
    if lab.startswith("x2_"):
        if lift != "x" + lab[3:]:
            return 0
        return br(t1v(LVEC["x" + lab[3:]]), 1, fb, 2)
    if lab.startswith("xy_") or lab.startswith("xz_"):
        j = lab[3:]
        A = LVEC["x" + j]
        Bl = ("y" if lab.startswith("xy_") else "z") + j
        Bv = LVEC[Bl]
        if lift == "x" + j:
            return br(fb, 2, t1v(Bv), 1)
        if lift == Bl:
            return br(t1v(A), 1, fb, 2)
        return 0
    if lab.startswith("tau2_") or lab.startswith("phi2_"):
        if lift != lab[5:]:
            return 0
        return br(t1v(LVEC[lab[5:]]), 1, fb, 2)
    raise AssertionError(lab)

def lv_omega(j, lift, tj):
    Yv, Zv = t1v(LVEC["y" + j]), t1v(LVEC["z" + j])
    T = L2bas[tj]
    if lift == "y" + j:
        return br(br(T, 2, Zv, 1), 3, Zv, 1)
    if lift == "z" + j:
        # NOTE: author's robust_defect.py passes degree 3 (not 2) for the
        # [Y,Z] factor here; that is a bug in dead code (omega vacuous).
        # Correct degree 2 verified in P6 (lv_omega exact 8/8).
        return br(br(Yv, 1, T, 2), 3, Zv, 1) ^ br(br(Yv, 1, Zv, 1), 2, T, 2)
    return 0

def lv_s(s, lift, tj):
    c = ker[s]
    t = 0
    for k in range(168):
        if (c >> k) & 1:
            t ^= br(lv_quad(QLABEL[k // 8], lift, tj), 3, gen(k % 8), 1)
    if (c >> 168) & 1:
        t ^= lv_omega("1", lift, tj)
    if (c >> 169) & 1:
        t ^= lv_omega("2", lift, tj)
    return t

# quotient subset Ssel (15 of 36)
Ssel = []
rest = dict(bR2)
for j, b in enumerate(L2bas):
    if cred_low(b, rest) != 0:
        Ssel.append(j)
        r = cred_low(b, rest)
        p = (r & (-r)).bit_length() - 1
        for q in list(rest):
            if (rest[q] >> p) & 1:
                rest[q] ^= r
        rest[p] = r
    if len(Ssel) == 15:
        break
check("Ssel=15", len(Ssel) == 15)

# LV(R2) = 0 over 28*16*21 = 9408
def coords_L2bas(vec):
    # coords in high bits (>=64) so lowbit pivots land on tensor bits
    aug = {}
    for j, b in enumerate(L2bas):
        w = b | (1 << (64 + j))
        while w:
            pp = (w & (-w)).bit_length() - 1
            if pp in aug:
                w ^= aug[pp]
            else:
                aug[pp] = w
                break
    w = vec
    while w:
        pp = (w & (-w)).bit_length() - 1
        if pp in aug:
            w ^= aug[pp]
        else:
            break
    assert w & ((1 << 64) - 1) == 0, "vec outside L2"
    return w >> 64

R2bas = list(bR2.values())
assert len(R2bas) == 21
r2coords = [coords_L2bas(r) for r in R2bas]
bad = tot = 0
for s in range(28):
    for kk in LIFTS:
        for cc in r2coords:
            acc = 0
            for j in range(36):
                if (cc >> j) & 1:
                    acc ^= lv_s(s, kk, j)
            tot += 1
            if cred_low(acc, bI4) != 0:
                bad += 1
check("LV(R2)=0 9408", bad == 0, "%d/%d bad" % (bad, tot))

# TOTAL_full240 (Fpin and K)
fullF = list(modelF)
fullK = list(modelK)
for s in range(28):
    for kk in LIFTS:
        for a in Ssel:
            fullF.append(lv_s(s, kk, a))
            fullK.append(lv_s(s, kk, a))
rFF, bFF = rb_low(list(bI4.values()) + fullF)
rFK, bFK = rb_low(list(bI4.values()) + fullK)
check("TOTAL_full240 Fpin=37", rFF - rI4 == 37, str(rFF - rI4))
print("  TOTAL_full240 K-model: %d" % (rFK - rI4))
check("TOTAL_full240 K=33", rFK - rI4 == 33, str(rFK - rI4))
check("K-TOTAL subset Fpin-TOTAL",
      all(cred_low(v, bFF) == 0 for v in fullK))
# v_s in both TOTALs (4 p2 syzygies)
nvin = sum(1 for s in uses_p2 if cred_low(vlist[s], bFF) == 0)
check("v_s in TOTAL_full240 4/4", nvin == 4, str(nvin))
# ad3 / escape / witness
L3sp = [br(M, 2, gen(c), 1) for M in L2sp for c in range(8)]
assert len(L3sp) == 288
for cnm in ["c1", "c2"]:
    W = t1v(Vm[cnm])
    adv = [br(T, 3, W, 1) for T in L3sp]
    ra = rb_low(list(bI4.values()) + adv)[0] - rI4
    escF = rb_low(list(bFF.values()) + adv)[0] - rFF
    escK = rb_low(list(bFK.values()) + adv)[0] - rFK
    nwF = sum(1 for a in adv if cred_low(a, bFF) != 0)
    assert ra == 18 and escF == 18 and escK == 18, (cnm, ra, escF, escK)
    print("  ad3(%s): rank 18 escape Fpin 18 K 18 wit-rows %d/288" % (cnm, nwF))
check("ad3 18 escape 18 both", True)
# witness row 1 = [X_0^2,X_1]
W1 = t1v(Vm["c1"])
adv1 = [br(T, 3, W1, 1) for T in L3sp]
check("L3row1 in L3", cred_low(L3sp[1], bL3) == 0)
check("L3row1 nonzero mod I3", cred_low(L3sp[1], bI3) != 0)
check("wit1 misses Fpin-TOTAL c1", cred_low(adv1[1], bFF) != 0)
W2 = t1v(Vm["c2"])
adv2 = [br(T, 3, W2, 1) for T in L3sp]
check("wit1 misses Fpin-TOTAL c2", cred_low(adv2[1], bFF) != 0)
check("wit1 misses K-TOTAL c1", cred_low(adv1[1], bFK) != 0)
check("wit1 misses K-TOTAL c2", cred_low(adv2[1], bFK) != 0)
# [R3,c] in I4 (map factors through gr3)
badrc = 0
for cnm in ["c1", "c2"]:
    W = t1v(Vm[cnm])
    for r in R3rows:
        if cred_low(br(r, 3, W, 1), bI4) != 0:
            badrc += 1
check("[R3,c] in I4 340", badrc == 0, "%d bad" % badrc)

# ---------------- P6: H3 affinity (fresh seed, own trips) ----------------
print("== P6 H3 affinity ==")

def rand_T2mask():
    m = 0
    v = 0
    for j in range(36):
        if random.getrandbits(1):
            v ^= L2bas[j]
            m |= 1 << j
    return v, m

def mk_lift4(key, T2, U3, T4=0):
    v8 = LVEC[key]
    V1 = t1v(v8)
    A2 = arb2(v8)
    A3 = arb3bits(v8)
    return (V1, A2 ^ T2, A3 ^ mul(V1, 1, T2, 2) ^ U3, T4)

def rand_lifts4(t4=True):
    L, M = {}, {}
    for kk in LIFTS:
        T2, m = rand_T2mask()
        T4 = random.getrandbits(4096) if t4 else 0
        L[kk] = mk_lift4(kk, T2, random.getrandbits(512), T4)
        M[kk] = m
    return L, M

def rstand_trip4(L):
    return gmul4(gcomm4(L["x2"], L["z2"]),
                 gmul4(gcomm4(L["x2"], L["y2"]),
                       gmul4(L["y2"], L["y2"])))

# A2: 24 non-p2 exact (random T'/U'/T4)
na2 = 0
for s in nonp2:
    L, M = rand_lifts4(t4=True)
    w = (0, 0, 0, 0)
    c = ker[s]
    for k in range(168):
        if (c >> k) & 1:
            nm = QLABEL[k // 8]
            xh = (gen(k % 8), 0, 0, 0)
            w = gmul4(w, gcomm4(rho_trip4(nm, L), xh))
    assert w[0] == 0 and w[1] == 0 and w[2] == 0, s
    pred = modelF[s]
    for kk in LIFTS:
        m = M[kk]
        for j in range(36):
            if (m >> j) & 1:
                pred ^= lv_s(s, kk, j)
    assert w[3] == pred, s
    na2 += 1
check("A2 exact 24/24", na2 == 24)
# T' additivity (no T'^2): second difference vanishes
nadd = 0
for trial in range(6):
    s = random.choice(nonp2)
    L0 = {kk: mk_lift4(kk, 0, 0, 0) for kk in LIFTS}
    La, Ma = rand_lifts4(t4=False)
    Lb, Mb = rand_lifts4(t4=False)
    # zero U' for additivity isolation (U' already shown absent)
    La = {kk: (v[0], v[1], v[2] ^ (v[2] ^ mk_lift4(kk, 0, 0, 0)[2] ^ mul(v[0], 1, v[1] ^ arb2(LVEC[kk]), 2)), 0) for kk, v in La.items()}
    # simpler: rebuild with U'=0,T4=0 from masks
    def lift_of(kk, m):
        T2 = 0
        for j in range(36):
            if (m >> j) & 1:
                T2 ^= L2bas[j]
        return mk_lift4(kk, T2, 0, 0)
    La = {kk: lift_of(kk, Ma[kk]) for kk in LIFTS}
    Lb = {kk: lift_of(kk, Mb[kk]) for kk in LIFTS}
    Mab = {kk: Ma[kk] ^ Mb[kk] for kk in LIFTS}
    Lab = {kk: lift_of(kk, Mab[kk]) for kk in LIFTS}
    def w4_of(L):
        w = (0, 0, 0, 0)
        c = ker[s]
        for k in range(168):
            if (c >> k) & 1:
                nm = QLABEL[k // 8]
                xh = (gen(k % 8), 0, 0, 0)
                w = gmul4(w, gcomm4(rho_trip4(nm, L), xh))
        return w[3]
    d2 = w4_of(La) ^ w4_of(Lb) ^ w4_of(Lab) ^ w4_of(L0)
    assert d2 == 0, (trial, s)
    nadd += 1
check("T' additivity 6/6", nadd == 6)
# E load-bearing: drop E, prediction fails
nefail = 0
for s in nonp2[:6]:
    L, M = rand_lifts4(t4=True)
    w = (0, 0, 0, 0)
    c = ker[s]
    for k in range(168):
        if (c >> k) & 1:
            nm = QLABEL[k // 8]
            xh = (gen(k % 8), 0, 0, 0)
            w = gmul4(w, gcomm4(rho_trip4(nm, L), xh))
    pred_noE = modelF[s]
    # subtract E terms
    for k in range(168):
        if (c >> k) & 1:
            pred_noE ^= mul(br(Q2[k // 8], 2, gen(k % 8), 1), 3, gen(k % 8), 1)
    for kk in LIFTS:
        m = M[kk]
        for j in range(36):
            if (m >> j) & 1:
                pred_noE ^= lv_s(s, kk, j)
    if w[3] != pred_noE:
        nefail += 1
check("E load-bearing (fails w/o E)", nefail > 0, "%d/6 fail" % nefail)
# lv_omega finite-difference (vacuous channels, validate formula anyway)
nom = 0
for j in "12":
    for trial in range(4):
        L, M = rand_lifts4(t4=True)
        got = omega_trip4(L, j)[3]
        pred = OM4[j]
        for kk in LIFTS:
            m = M[kk]
            for tj in range(36):
                if (m >> tj) & 1:
                    pred ^= lv_omega(j, kk, tj)
        # omega (w)_3 T'-free? prediction exact requires U'-absence too
        assert got == pred, (j, trial)
        nom += 1
check("lv_omega exact 8/8", nom == 8)
# B: r_stand affine + y2 T'/U'-freedom (W'' = Wp.r_stand^-1)
print("  B: r_stand pin control")
FSA = FSTAND
nok = 0
for trial in range(4):
    L3t = {}
    Mt = {}
    for kk in LIFTS:
        T2, m = rand_T2mask()
        v8 = LVEC[kk]
        L3t[kk] = (t1v(v8), arb2(v8) ^ T2,
                   arb3bits(v8) ^ mul(t1v(v8), 1, T2, 2) ^ random.getrandbits(512))
        Mt[kk] = m
    rs = rstand_trip3(L3t)
    # affine prediction: FSTAND + LV_r(M)
    pred = FSA
    for kk, role in (("x2", 0), ("y2", 1), ("z2", 2)):
        m = Mt[kk]
        for tj in range(36):
            if (m >> tj) & 1:
                pred ^= (CX2, CY2, CZ2)[role][tj]
    assert rs[2] == pred, trial
    Wp = wp_trip3(L3t)
    Dw = gmul3(Wp, ginv3(rs))
    assert Dw[0] == 0 and Dw[1] == 0, trial
    assert Dw[2] == (K ^ FSA), trial  # T'/U' cancel
    nok += 1
check("r_stand affine + W''-free 4/4", nok == 4)
check("K^FSTAND in I3 (W'' in R3)", cred_low(K ^ FSA, bI3) == 0)

# ---------------- P7: H2 arbitrary-conjugate probes ----------------
print("== P7 H2 probes ==")
# 30 = 21 quadrics + 2 cubics + 7 quartics (4 dyadic + 3 cap)
print("  30-generator census: 21 quad + 2 cubic + 7 quartic (4 dyadic+3 cap)")
# f = x.u reduction: [rho,f] = Sum a_l [rho,X_l] mod I4 (tower, then author)
# Conjugators are GROUP-LIKE to degree 2: f = x.u with x = Prod X_l^{a_l}
# and (u)_2 in L2 (random Lie combo). Non-Lie (f)_2 would put
# [(rho)_2,(f)_2] outside [R2,L2] -- outside the proof's scope (f in Fbar).
def rand_Lie2():
    v = 0
    for b in L2bas:
        if random.getrandbits(1):
            v ^= b
    return v

def rand_conj():
    a1 = random.getrandbits(8)
    x = (0, 0, 0, 0)
    for l in range(8):
        if (a1 >> l) & 1:
            x = gmul4(x, ((1 << l), 0, 0, 0))
    u = (0, rand_Lie2(), random.getrandbits(512), random.getrandbits(4096))
    return gmul4(x, u)

nredT = nredA = 0
for trial in range(12):
    lab = random.choice([q for q in QLABEL if q != "rho_p2"])
    L, M = rand_lifts4(t4=True)
    R = rho_trip4(lab, L)
    assert R[0] == 0
    f = rand_conj()
    a1 = f[0]
    # tower
    lhsT = gcommT(R, f)[3]
    rhsT = 0
    for l in range(8):
        if (a1 >> l) & 1:
            Xl = (1 << l, 0, 0, 0)
            rhsT ^= gcommT(R, Xl)[3]
    assert cred_low(lhsT ^ rhsT, bI4) == 0, ("T", trial, lab)
    nredT += 1
    # author
    lhsA = gcomm4(R, f)[3]
    rhsA = 0
    for l in range(8):
        if (a1 >> l) & 1:
            Xl = (1 << l, 0, 0, 0)
            rhsA ^= gcomm4(R, Xl)[3]
    assert cred_low(lhsA ^ rhsA, bI4) == 0, ("A", trial, lab)
    nredA += 1
check("f=x.u reduction tower 12/12", nredT == 12)
check("f=x.u reduction author 12/12", nredA == 12)
# syzygy lifts with group-like higher-part conjugators stay in corr+I4
nhc = 0
for trial in range(8):
    s = random.choice(nonp2)
    L, M = rand_lifts4(t4=True)
    w = (0, 0, 0, 0)
    c = ker[s]
    for k in range(168):
        if (c >> k) & 1:
            nm = QLABEL[k // 8]
            Xl = ((1 << (k % 8)), 0, 0, 0)
            u = (0, rand_Lie2(), random.getrandbits(512),
                 random.getrandbits(4096))
            g = gmul4(Xl, u)
            w = gmul4(w, gcommT(rho_trip4(nm, L), g))
    # gr3 must still vanish (deg-3 identity sees only gr1)
    assert w[0] == 0 and w[1] == 0 and w[2] == 0, trial
    pred = modelF[s]
    for kk in LIFTS:
        m = M[kk]
        for j in range(36):
            if (m >> j) & 1:
                pred ^= lv_s(s, kk, j)
    # tower-vs-author model diff is in I4 (P3b), so compare mod I4
    assert cred_low(w[3] ^ pred, bI4) == 0, trial
    nhc += 1
check("higher-part conjugators 8/8", nhc == 8)
# r_stand slot: [r_stand,f] reduction (p2 stand-in, same initial)
nrs = 0
for trial in range(6):
    L, M = rand_lifts4(t4=True)
    R = rstand_trip4(L)
    assert R[0] == 0 and R[1] == DEM2
    f = rand_conj()
    lhs = gcommT(R, f)[3]
    rhs = 0
    for l in range(8):
        if (f[0] >> l) & 1:
            rhs ^= gcommT(R, ((1 << l), 0, 0, 0))[3]
    assert cred_low(lhs ^ rhs, bI4) == 0, trial
    nrs += 1
check("r_stand reduction 6/6", nrs == 6)

print("ALL PASS (%d checks)" % len(PASS))
