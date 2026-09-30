#!/usr/bin/env python3
"""Finite group data for the tower over B = Q(sqrt 241) (work packages T7/T8).

Writes `UnitDistance/Sqrt241/GroupData/Data.lean`: bit masks for the
universal class-two group on F_2^8 x F_2^36, the retained model
Q_B = F_2^8 x F_2^15 (the quotient of the free quadratic layer by the span
of the 21 quadratic cut initials), the two dyadic embeddings of the order-32
group D, the dual characters, and the truncated Magnus certificates
(21 quadratic rows, a left inverse, 7 second-layer and 8 third-layer
detectors for the conjugation vector c1 = 10111010).

Every emitted number is untrusted: the Lean modules in GroupData/ check all
the properties that are used (`decide +kernel`). The script also re-checks
them in Python and stops on any failure.

Conventions (as in `lie241.py`, `construction.md` §3.4 and the plan §1.5):
* coordinate i of V = F_2^8 is the Kummer basis element alpha_i of
  [-1, eps, pi2, pi2', pi3, pi3', pi5, pi5']; a vector is a mask with bit i
  for coordinate i;
* universal quadratic layer W_U = F_2^36: bits 0..7 are the squares, bit
  8 + k is the pair (j < i) number k in lexicographic order;
* Magnus tensors: entry (i, j) of V_2 is bit 8 i + j, entry (i, j, k) of V_3
  is bit 64 i + 8 j + k.

Usage: python3 scripts/sqrt241/generate_group_data.py [--out PATH]
"""
import argparse
import itertools
import random
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
n = 8

# ---------------------------------------------------------------- input data
def m(bits):
    return sum(b << k for k, b in enumerate(bits))

VEC = {
    "c1": m([1, 0, 1, 1, 1, 0, 1, 0]), "c2": m([1, 1, 0, 0, 0, 1, 0, 1]),
    "x1": m([0, 0, 1, 0, 0, 0, 0, 0]), "y1": m([1, 1, 1, 1, 0, 0, 1, 0]), "z1": m([1, 0, 0, 0, 0, 1, 0, 0]),
    "x2": m([0, 0, 0, 1, 0, 0, 0, 0]), "y2": m([1, 0, 0, 0, 0, 0, 0, 1]), "z2": m([1, 1, 1, 1, 1, 0, 0, 0]),
    "t31": m([0, 0, 0, 0, 1, 0, 0, 0]), "p31": m([1, 0, 1, 0, 0, 1, 1, 1]),
    "t32": m([0, 0, 0, 0, 0, 1, 0, 0]), "p32": m([1, 1, 1, 0, 1, 0, 1, 1]),
    "t51": m([0, 0, 0, 0, 0, 0, 1, 0]), "p51": m([0, 1, 1, 0, 0, 1, 0, 1]),
    "t52": m([0, 0, 0, 0, 0, 0, 0, 1]), "p52": m([0, 1, 0, 1, 1, 0, 1, 0]),
    "f291": m([0, 0, 1, 0, 0, 1, 1, 1]), "f292": m([0, 0, 0, 1, 1, 0, 1, 1]),
    "f7": m([0, 1, 1, 1, 0, 0, 0, 0]),
}
CONJ = [VEC["c1"], VEC["c2"]]
TAME_T = [VEC["t31"], VEC["t32"], VEC["t51"], VEC["t52"]]
TAME_F = [VEC["p31"], VEC["p32"], VEC["p51"], VEC["p52"]]
TAME_N = [3, 3, 5, 5]
# local source generators a, b, c (reciprocity classes of -1, 5, 2); x = b, y = a, z = a c
DY_A = [VEC["y1"], VEC["y2"]]
DY_B = [VEC["x1"], VEC["x2"]]
DY_C = [VEC["y1"] ^ VEC["z1"], VEC["y2"] ^ VEC["z2"]]
DY_X, DY_Y, DY_Z = DY_B, DY_A, [a ^ c for a, c in zip(DY_A, DY_C)]
CAP = [VEC["f291"], VEC["f292"], VEC["f7"]]

def bit(v, i):
    return (v >> i) & 1

def popparity(v):
    return bin(v).count("1") & 1

# ------------------------------------------------------- universal layer (36)
PAIRS = [(j, i) for j in range(n) for i in range(j + 1, n)]
UIDX = {}
for i in range(n):
    UIDX[(i, i)] = i
for k, (j, i) in enumerate(PAIRS):
    UIDX[(i, j)] = n + k
    UIDX[(j, i)] = n + k
NU = n + len(PAIRS)  # 36

def ucocycle(v, w):
    """Lower-triangular universal cocycle: sum_{i >= j} v_i w_j e_(i,j)."""
    r = 0
    for i in range(n):
        for j in range(i + 1):
            if bit(v, i) and bit(w, j):
                r ^= 1 << UIDX[(i, j)]
    return r

def usq(v):
    return ucocycle(v, v)

def ubr(v, w):
    return ucocycle(v, w) ^ ucocycle(w, v)

def utame(t, f, N):
    return ubr(t, f) ^ (usq(t) if N % 4 == 3 else 0)

UCOCYCLE_MASKS = [[(1 << UIDX[(i, j)]) if j <= i else 0 for j in range(n)] for i in range(n)]

# the 21 quadratic cut initials, in the order of `quadraticWords`
CUT_NAMES = (["c1^2", "c2^2"] + ["tame(q%d)" % q for q in range(4)] + ["y2^2"] +
             ["x1^2", "[x1,y1]", "[x1,z1]", "x2^2", "[x2,y2]", "[x2,z2]"] +
             ["tau(q%d)^2" % q for q in range(4)] + ["phi(q%d)^2" % q for q in range(4)])
CUT_U = ([usq(c) for c in CONJ] + [utame(TAME_T[q], TAME_F[q], TAME_N[q]) for q in range(4)] +
         [usq(DY_Y[1])] +
         [usq(DY_X[0]), ubr(DY_X[0], DY_Y[0]), ubr(DY_X[0], DY_Z[0]),
          usq(DY_X[1]), ubr(DY_X[1], DY_Y[1]), ubr(DY_X[1], DY_Z[1])] +
         [usq(t) for t in TAME_T] + [usq(f) for f in TAME_F])
assert len(CUT_U) == 21

def udemuskin(P):
    x, y, z = DY_X[P], DY_Y[P], DY_Z[P]
    return usq(y) ^ ubr(x, y) ^ ubr(x, z)

# the seven presentation relator initials (c1^2, c2^2, four tame, genuine at p2)
INIT_U = CUT_U[:6] + [udemuskin(1)]

# ------------------------------------------------------------ F_2 linear algebra
def rref(rows):
    """Row reduce; returns list of (pivot, row, combo) with combo = mask of input rows."""
    basis = []  # (pivot, row, combo)
    for idx, r in enumerate(rows):
        c = 1 << idx
        for p, br, bc in basis:
            if bit(r, p):
                r ^= br
                c ^= bc
        if r:
            p = r.bit_length() - 1
            # eliminate p from existing rows (full reduction)
            nb = []
            for q, br, bc in basis:
                if bit(br, p):
                    br ^= r
                    bc ^= c
                nb.append((q, br, bc))
            basis = nb + [(p, r, c)]
    return basis

def rank(rows):
    return len(rref(rows))

def in_span(v, rows):
    return rank(rows + [v]) == rank(rows)

def weight(v):
    return bin(v).count("1")


def dual_functionals(constraints, targets, ncols, restarts=40, seed=1):
    """Functionals phi_k (masks over ncols bits) with phi_k(c) = 0 for all
    constraints c and phi_k(t_j) = delta_jk, searched for small weight
    (heuristic: randomized elimination over the dual code, then local
    improvement by annihilating vectors). Every result is verified."""
    rng = random.Random(seed)
    k = len(targets)
    best = [None] * k
    for attempt in range(restarts):
        cols = list(range(ncols))
        if attempt:
            rng.shuffle(cols)
        # reduce the constraints with pivots chosen in the column order `cols`
        basis = []  # (pivot, row)
        for r in constraints:
            for p, br in basis:
                if bit(r, p):
                    r ^= br
            if r:
                p = next(c for c in cols if bit(r, c))
                basis = [(q, br ^ r if bit(br, p) else br) for q, br in basis] + [(p, r)]
        pivots = {p for p, _ in basis}
        dual = []
        for f in range(ncols):
            if f in pivots:
                continue
            phi = 1 << f
            for p, r in basis:
                if bit(r, f):
                    phi |= 1 << p
            dual.append(phi)

        def sig(phi):
            return sum(popparity(phi & t) << j for j, t in enumerate(targets))
        rng.shuffle(dual)
        dual.sort(key=weight)
        ech = []
        zero = []
        for phi in dual:
            s = sig(phi)
            for pb, bs, bphi in ech:
                if bit(s, pb):
                    s ^= bs
                    phi ^= bphi
            if s:
                ech.append((s.bit_length() - 1, s, phi))
            else:
                zero.append(phi)
        zero.sort(key=weight)
        for j in range(k):
            s, phi = 1 << j, 0
            for pb, bs, bphi in ech:
                if bit(s, pb):
                    s ^= bs
                    phi ^= bphi
            if s:
                raise RuntimeError("targets are dependent modulo the constraints")
            improved = True
            while improved:
                improved = False
                for z in zero:
                    if weight(phi ^ z) < weight(phi):
                        phi ^= z
                        improved = True
            if best[j] is None or weight(phi) < weight(best[j]):
                best[j] = phi
    for j, phi in enumerate(best):
        for c in constraints:
            assert popparity(phi & c) == 0
        for i, t in enumerate(targets):
            assert popparity(phi & t) == (1 if i == j else 0)
    return best

# ------------------------------------------------------------ checks (lie241)
assert rank(CUT_U) == 21, "the 21 quadratic cut initials must be independent"
assert in_span(udemuskin(0), CUT_U) and in_span(udemuskin(1), CUT_U)
assert rank(INIT_U) == 7
for P in range(2):
    # z^2 and [y,z] independent modulo the relations
    assert rank(CUT_U + [usq(DY_Z[P]), ubr(DY_Y[P], DY_Z[P])]) == 23
for q in range(4):
    assert rank([TAME_T[q], TAME_F[q]]) == 2
for f in CAP:
    assert not in_span(usq(f), CUT_U)

# ------------------------------------------------------------ reduction 36 -> 15
basis = rref(CUT_U)
pivots = sorted(p for p, _, _ in basis)
free = [c for c in range(NU) if c not in pivots]
assert len(free) == 15
FIDX = {c: k for k, c in enumerate(free)}

def reduce36(v):
    for p, r, _ in basis:
        if bit(v, p):
            v ^= r
    return sum(bit(v, c) << FIDX[c] for c in free)

QUAD_COLUMNS = [reduce36(1 << j) for j in range(NU)]
# relation coefficients: e_j = sum_i coeff_i(e_j) rel_i + section(red e_j)
REL_COEFF = []
for j in range(NU):
    coeff = 0
    for p, r, c in basis:
        if p == j:
            coeff ^= c
    REL_COEFF.append(coeff)
FREE_COLUMNS = [1 << c for c in free]

def expand(masks, v):
    r = 0
    for i, mk in enumerate(masks):
        if bit(v, i):
            r ^= mk
    return r

for i, rel in enumerate(CUT_U):
    assert reduce36(rel) == 0
for j in range(NU):
    red = expand(QUAD_COLUMNS, 1 << j)
    assert expand(CUT_U, REL_COEFF[j]) ^ expand(FREE_COLUMNS, red) == 1 << j
for k in range(15):
    assert expand(QUAD_COLUMNS, FREE_COLUMNS[k]) == 1 << k

RCOCYCLE_MASKS = [[QUAD_COLUMNS[UIDX[(i, j)]] if j <= i else 0 for j in range(n)] for i in range(n)]

def rcocycle(v, w):
    return reduce36(ucocycle(v, w))

for f in CAP:
    assert rcocycle(f, f) != 0

# ------------------------------------------------------------ retained group law
def qmul(g, h):
    return (g[0] ^ h[0], g[1] ^ h[1] ^ rcocycle(g[0], h[0]))

def qinv(g):
    return (g[0], g[1] ^ rcocycle(g[0], g[0]))

def qpow(g, k):
    r = (0, 0)
    for _ in range(k):
        r = qmul(r, g)
    return r

# ------------------------------------------------------------ dyadic maps
def d_index(a, b, c, d):
    return 16 * a + 8 * b + 2 * c + d

def d_mul(g, h):
    a1, b1, c1, d1 = g
    a2, b2, c2, d2 = h
    return ((a1 + a2) % 2, (b1 + b2) % 2, (c1 + c2) % 4, (d1 + d2 + (c1 % 2) * b2) % 2)

D_ELEMS = [(a, b, c, d) for a in range(2) for b in range(2) for c in range(4) for d in range(2)]
D_GEN = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)]

def dyadic_images(P):
    X, Y, Z = (DY_X[P], 0), (DY_Y[P], 0), (DY_Z[P], 0)
    Wc = qmul(qmul(qmul(qinv(Y), qinv(Z)), Y), Z)
    img = {}
    for (a, b, c, d) in D_ELEMS:
        g = qmul(qmul(qmul(qpow(X, a), qpow(Y, b)), qpow(Z, c)), qpow(Wc, d))
        img[(a, b, c, d)] = g
    # homomorphism and injectivity checks
    for g in D_ELEMS:
        for h in D_ELEMS:
            assert img[d_mul(g, h)] == qmul(img[g], img[h])
    assert len(set(img.values())) == 32
    base = [0] * 32
    cent = [0] * 32
    for e in D_ELEMS:
        base[d_index(*e)] = img[e][0]
        cent[d_index(*e)] = img[e][1]
    # base zero iff a = b = 0 and c even
    for e in D_ELEMS:
        assert (img[e][0] == 0) == (e[0] == 0 and e[1] == 0 and e[2] % 2 == 0)
    return base, cent

DY_BASE, DY_CENT = zip(*[dyadic_images(P) for P in range(2)])

def char_masks(P):
    """Linear functionals on V (8-bit masks) dual to (x_P, y_P, z_P), lightest first."""
    gens = [DY_X[P], DY_Y[P], DY_Z[P]]
    res = []
    for j in range(3):
        cands = [mk for mk in range(1, 256)
                 if all(popparity(mk & g) == (1 if i == j else 0) for i, g in enumerate(gens))]
        res.append(min(cands, key=lambda mk: (bin(mk).count("1"), mk)))
    return res

DY_CHAR = [char_masks(P) for P in range(2)]

# ------------------------------------------------------------ presentation duals (T6 data)
# the dual masks published in TOWER_PLAN.md (T6); verified here
INIT_COORD = [4, 2, 20, 34, 524288, 1048578, 7]
for i, l in enumerate(INIT_COORD):
    for j, r in enumerate(INIT_U):
        assert popparity(l & r) == (1 if i == j else 0)

# ------------------------------------------------------------ Magnus data
def S2(v):
    r = 0
    for i in range(n):
        for j in range(n):
            if bit(v, i) and bit(v, j):
                r |= 1 << (8 * i + j)
    return r

def B2(v, w):
    r = 0
    for i in range(n):
        for j in range(n):
            if (bit(v, i) & bit(w, j)) ^ (bit(w, i) & bit(v, j)):
                r |= 1 << (8 * i + j)
    return r

def T2(v, f, N):
    return B2(v, f) ^ (S2(v) if N % 4 == 3 else 0)

def bracket3(x, Y):
    """(i,j,k) -> x_i Y_jk - Y_ij x_k over F_2."""
    r = 0
    for i in range(n):
        for j in range(n):
            for k in range(n):
                a = bit(x, i) & bit(Y, 8 * j + k)
                b = bit(Y, 8 * i + j) & bit(x, k)
                if a ^ b:
                    r |= 1 << (64 * i + 8 * j + k)
    return r

def u_to_magnus(w):
    """The injective map W_U -> V_2 (square -> (i,i), pair -> (i,j)+(j,i))."""
    r = 0
    for i in range(n):
        if bit(w, i):
            r |= 1 << (9 * i)
    for k, (j, i) in enumerate(PAIRS):
        if bit(w, n + k):
            r |= (1 << (8 * i + j)) | (1 << (8 * j + i))
    return r

ROWS = ([S2(c) for c in CONJ] + [T2(TAME_T[q], TAME_F[q], TAME_N[q]) for q in range(4)] +
        [S2(DY_Y[1])] +
        [S2(DY_X[0]), B2(DY_X[0], DY_Y[0]), B2(DY_X[0], DY_Z[0]),
         S2(DY_X[1]), B2(DY_X[1], DY_Y[1]), B2(DY_X[1], DY_Z[1])] +
        [S2(t) for t in TAME_T] + [S2(f) for f in TAME_F])
for r, u in zip(ROWS, CUT_U):
    assert r == u_to_magnus(u)
assert rank(ROWS) == 21

LEFT = dual_functionals([], ROWS, 64)
CVEC = CONJ[0]
E = [1 << i for i in range(n)]
# second layer: seven generator directions (drop e0)
BASE_INDEX = [1, 2, 3, 4, 5, 6, 7]
SECOND_TARGETS = [B2(E[i], CVEC) for i in BASE_INDEX]
SECOND = dual_functionals(ROWS, SECOND_TARGETS, 64)
# third layer
R3 = [bracket3(E[j], r) for r in ROWS for j in range(n)]
DY_CUBIC = [bracket3(DY_Z[P], B2(DY_Y[P], DY_Z[P])) for P in range(2)]
R3 = R3 + DY_CUBIC
r3 = rank(R3)
# choose eight pairs greedily with independent images modulo R3
SELECTED = []
cur = list(R3)
for (a, b) in PAIRS:
    t = bracket3(CVEC, B2(E[a], E[b]))
    if rank(cur + [t]) > rank(cur):
        cur.append(t)
        SELECTED.append((a, b))
    if len(SELECTED) == 8:
        break
assert len(SELECTED) == 8, "ad(c1) on L2 must have rank 8"
THIRD_TARGETS = [bracket3(CVEC, B2(E[a], E[b])) for (a, b) in SELECTED]
THIRD = dual_functionals(R3, THIRD_TARGETS, 512)

# ------------------------------------------------------------ Lean output
def lvec(xs):
    return "![" + ",".join(str(x) for x in xs) + "]"

def lmat(rows):
    return "![" + ",\n    ".join(lvec(r) for r in rows) + "]"

def supports2(mask):
    return [(p // 8, p % 8) for p in range(64) if bit(mask, p)]

def supports3(mask):
    return [(p // 64, (p // 8) % 8, p % 8) for p in range(512) if bit(mask, p)]

def llist2(s):
    return "[" + ",".join("(%d,%d)" % t for t in s) + "]"

def llist3(s):
    return "[" + ",".join("(%d,%d,%d)" % t for t in s) + "]"

def lsupports(lists):
    return "![" + ",\n    ".join(lists) + "]"

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", default="UnitDistance/Sqrt241/GroupData/Data.lean")
    args = ap.parse_args()
    out = ROOT / args.out
    L = []
    w = L.append
    w("-- Generated by scripts/sqrt241/generate_group_data.py — do not edit by hand.")
    w("module")
    w("")
    w("public import Mathlib.Data.Nat.Bitwise")
    w("public import Mathlib.Data.Fin.VecNotation")
    w("")
    w("@[expose] public section")
    w("set_option backward.privateInPublic true")
    w("")
    w("")
    w("/-!")
    w("# Generated finite data for the tower over `ℚ(√241)`")
    w("")
    w("Generated by `scripts/sqrt241/generate_group_data.py`; do not edit by hand.")
    w("All numbers are untrusted bit masks: every property used downstream is")
    w("checked in the other `GroupData` modules by `decide +kernel`.")
    w("")
    w("Coordinates: bit `i` of a vector mask is the Kummer coordinate `αᵢ` of")
    w("`[-1, ε, π₂, π₂', π₃, π₃', π₅, π₅']`; the universal quadratic layer has the")
    w("squares at bits `0..7` and the pairs `(j<i)` at `8 + ` lexicographic index;")
    w("Magnus tensor entry `(i,j)` is bit `8i+j` and `(i,j,k)` is bit `64i+8j+k`.")
    w("-/")
    w("")
    w("namespace UnitDistance.Sqrt241.GroupData")
    w("")
    w("/-- Complex conjugations `c₁ = 10111010`, `c₂ = 11000101`. -/")
    w("def conjMask : Fin 2 → ℕ := %s" % lvec(CONJ))
    w("/-- Tame inertia at `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`. -/")
    w("def tameInertiaMask : Fin 4 → ℕ := %s" % lvec(TAME_T))
    w("/-- Tame Frobenius lifts (fixing the Kummer class of the prime) at `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`. -/")
    w("def tameFrobeniusMask : Fin 4 → ℕ := %s" % lvec(TAME_F))
    w("/-- Norms of the tame primes. -/")
    w("def tameNorm : Fin 4 → ℕ := %s" % lvec(TAME_N))
    w("/-- Dyadic local generators `a, b, c` (classes of `-1, 5, 2`) at `𝔭₁, 𝔭₂`. -/")
    w("def dyadicAMask : Fin 2 → ℕ := %s" % lvec(DY_A))
    w("def dyadicBMask : Fin 2 → ℕ := %s" % lvec(DY_B))
    w("def dyadicCMask : Fin 2 → ℕ := %s" % lvec(DY_C))
    w("/-- The dyadic generators `x = b`, `y = a`, `z = a c`. -/")
    w("def dyadicXMask : Fin 2 → ℕ := %s" % lvec(DY_X))
    w("def dyadicYMask : Fin 2 → ℕ := %s" % lvec(DY_Y))
    w("def dyadicZMask : Fin 2 → ℕ := %s" % lvec(DY_Z))
    w("/-- Frobenius at `29₁`, `29₂` and the square of the Frobenius at the inert `7`. -/")
    w("def capMask : Fin 3 → ℕ := %s" % lvec(CAP))
    w("")
    w("/-- Lower-triangular universal cocycle on `F₂⁸ × F₂³⁶`. -/")
    w("def universalCocycleMasks : Fin 8 → Fin 8 → ℕ :=\n  %s" % lmat(UCOCYCLE_MASKS))
    w("")
    w("/-- The 21 quadratic cut initials in the universal layer (order of `quadraticWords`: %s). -/"
      % ", ".join(CUT_NAMES))
    w("def cutInitialMasks : Fin 21 → ℕ :=\n  %s" % lvec(CUT_U))
    w("/-- The seven presentation relator initials (`c₁², c₂²`, four tame, genuine at `𝔭₂`). -/")
    w("def relatorInitialMasks : Fin 7 → ℕ := %s" % lvec(INIT_U))
    w("/-- Dual functionals on the universal layer for the seven relator initials. -/")
    w("def relatorCoordinateMasks : Fin 7 → ℕ := %s" % lvec(INIT_COORD))
    w("")
    w("/-- Images of the 36 universal basis vectors in the 15 retained coordinates. -/")
    w("def quadraticColumns : Fin 36 → ℕ :=\n  %s" % lvec(QUAD_COLUMNS))
    w("/-- Coefficients (21-bit masks) of the relation part of each universal basis vector. -/")
    w("def relationCoefficientColumns : Fin 36 → ℕ :=\n  %s" % lvec(REL_COEFF))
    w("/-- The section `F₂¹⁵ → F₂³⁶`: the universal basis vector of each free coordinate. -/")
    w("def freeColumnMasks : Fin 15 → ℕ :=\n  %s" % lvec(FREE_COLUMNS))
    w("/-- Lower-triangular cocycle of the retained model on `F₂⁸ × F₂¹⁵`. -/")
    w("def retainedCocycleMasks : Fin 8 → Fin 8 → ℕ :=\n  %s" % lmat(RCOCYCLE_MASKS))
    w("")
    w("/-- Normal-form images of the 32 elements of `Dyadic.D` (indexed by `D.index`) in the retained model. -/")
    w("def dyadicBaseMasks : Fin 2 → Fin 32 → ℕ :=\n  %s" % lmat(DY_BASE))
    w("def dyadicCentralMasks : Fin 2 → Fin 32 → ℕ :=\n  %s" % lmat(DY_CENT))
    w("/-- Linear functionals on `F₂⁸` dual to `(x_P, y_P, z_P)`. -/")
    w("def dyadicCharacterMasks : Fin 2 → Fin 3 → ℕ :=\n  %s" % lmat(DY_CHAR))
    w("")
    w("/-- The 21 quadratic cut initials as Magnus tensors. -/")
    w("def quadraticRowMasks : Fin 21 → ℕ :=\n  %s" % lvec(ROWS))
    w("/-- Supports of a left inverse of the 21 rows. -/")
    w("def leftSupports : Fin 21 → List (Fin 8 × Fin 8) :=\n  %s"
      % lsupports([llist2(supports2(p)) for p in LEFT]))
    w("/-- Generators used for the second-layer conjugators. -/")
    w("def baseIndex : Fin 7 → Fin 8 := %s" % lvec(BASE_INDEX))
    w("/-- Supports of the second-layer detector (kills the rows, dual to `[e_i, c₁]`). -/")
    w("def secondSupports : Fin 7 → List (Fin 8 × Fin 8) :=\n  %s"
      % lsupports([llist2(supports2(p)) for p in SECOND]))
    w("/-- Generator pairs used for the third-layer conjugators. -/")
    w("def selectedPairs : Fin 8 → Fin 8 × Fin 8 := %s"
      % ("![" + ",".join("(%d,%d)" % pr for pr in SELECTED) + "]"))
    w("/-- Supports of the third-layer detector (kills `[e_j, row]` and the dyadic cubics). -/")
    w("def thirdSupports : Fin 8 → List (Fin 8 × Fin 8 × Fin 8) :=\n  %s"
      % lsupports([llist3(supports3(p)) for p in THIRD]))
    w("")
    w("end UnitDistance.Sqrt241.GroupData")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(L) + "\n")
    print("wrote", out)
    print("rank R3 =", r3, "; selected pairs", SELECTED)
    print("left support sizes", [bin(p).count("1") for p in LEFT])
    print("second support sizes", [bin(p).count("1") for p in SECOND])
    print("third support sizes", [bin(p).count("1") for p in THIRD])
    print("dyadic characters", DY_CHAR)
    print("relator initials", INIT_U, "coordinates", INIT_COORD)


if __name__ == "__main__":
    main()
