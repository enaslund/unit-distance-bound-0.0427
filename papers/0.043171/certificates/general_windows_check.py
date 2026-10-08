#!/usr/bin/env python3
"""Brute-force check of Lemma fw:shell-lemma for general (non-product) weights.

Works directly from the definitions of Section fw (no shell kernel, no ball expansion):
  L = unramified extension of Q_p of degree f (residue cardinality Q = p^f), modelled by the
  Galois ring GR(p^N, f) = (Z/p^N)[t]/(h(t)), h monic of degree f irreducible mod p;
  g = sum_{i<=I, j<=J} w_ij 1_{S_i x varpi^{-k} S_j} is invariant under C = O x varpi^{-k} O, so
  a point is a coset (x, y) with x = a p^{-I} (a in GR(p^I)) and y = b p^{-(J+k)} (b in GR(p^J)),
  and every coset has measure |C| = Q^k;
  Tg(z) = sum_n int_{O^x} g(z + (p^n w, p^{-n} w^{-1})) dw, the unit integral being the average over
  all units w mod p^M (M = max(I, J), which determines both coordinates of the shift modulo the
  period), with w^{-1} computed in the ring.
  Z(g)/Q^k = sum_cosets g Tg  and  A(g)/Q^k (p=2) = sum_cosets g^2.
These are compared exactly (fractions) with the shell kernel and the ball expansion of
general_windows.py, for random nonnegative, non-monotone, non-symmetric, partly zero weights.
"""
import itertools
import random
import sys
from collections import Counter
from fractions import Fraction as Q

HERE = __import__("pathlib").Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent / "0.04273/certificates"))
import env241  # noqa: E402,F401  (the publication certificate modules: interval_core, profile_certificate)
from general_windows import shell_overlap, rectangle_overlap, shell_masses  # noqa: E402


class GaloisRing:
    def __init__(self, p, f, h, N):
        # h = [h_0, ..., h_{f-1}]: t^f = -(h_0 + h_1 t + ... + h_{f-1} t^{f-1})
        self.p, self.f, self.h, self.N, self.mod = p, f, h, N, p**N

    def elements(self):
        return list(itertools.product(range(self.mod), repeat=self.f))

    def mul(self, a, b):
        f, mod = self.f, self.mod
        prod = [0] * (2 * f - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    prod[i + j] += x * y
        for d in range(2 * f - 2, f - 1, -1):          # reduce t^d, d >= f
            c = prod[d]
            if c:
                prod[d] = 0
                for l in range(f):
                    prod[d - f + l] -= c * self.h[l]
        return tuple(v % mod for v in prod[:f])

    def scale(self, a, c, mod):
        return tuple((c * v) % mod for v in a)

    def val(self, a):
        """p-adic valuation of a nonzero element (unramified: min over coordinates)."""
        best = None
        for v in a:
            v %= self.mod
            if v:
                e = 0
                while v % self.p == 0:
                    v //= self.p
                    e += 1
                best = e if best is None else min(best, e)
        return best  # None for 0

    def units(self):
        return [a for a in self.elements() if any(v % self.p for v in a)]

    def inv(self, a):
        order = (self.p**self.f - 1) * self.p**(self.f * (self.N - 1))
        result, base, e = (1,) + (0,) * (self.f - 1), a, order - 1
        while e:
            if e & 1:
                result = self.mul(result, base)
            base = self.mul(base, base)
            e >>= 1
        assert self.mul(result, a) == (1,) + (0,) * (self.f - 1)
        return result


def brute_force_overlap(p, f, h, I_, J, k, W):
    """Z(g)/Q^k and A(g)/Q^k (exponent 2) from the definitions, as exact fractions."""
    M = max(I_, J, 1)
    R = GaloisRing(p, f, h, M)
    units = R.units()
    nunits = len(units)
    Qn = p**f
    assert nunits == (Qn - 1) * Qn**(M - 1)
    inv = {u: R.inv(u) for u in units}
    modI, modJ = p**I_, p**J
    xs = list(itertools.product(range(modI), repeat=f))
    ys = list(itertools.product(range(modJ), repeat=f))

    def shell(a, top):
        v = GaloisRing(p, f, h, top).val(a) if any(a) else None
        return 0 if v is None else top - v

    sx = {a: shell(a, I_) for a in xs}
    sy = {b: shell(b, J) for b in ys}

    def g(a, b):
        return W[sx[a]][sy[b]]

    # shifts: for each n, the multiset of (da, db) with da = p^{n+I} w mod p^I, db = p^{J+k-n} w^{-1} mod p^J
    shifts = {}
    for n in range(-I_ - 2, J + k + 3):
        cnt = Counter()
        for u in units:
            if n + I_ < 0 or J + k - n < 0:
                cnt[None] += 1                       # shift leaves the support in some coordinate
                continue
            da = R.scale(u, p**(n + I_), modI)
            db = R.scale(inv[u], p**(J + k - n), modJ)
            cnt[(da, db)] += 1
        shifts[n] = cnt

    def add(a, d, mod):
        return tuple((x + y) % mod for x, y in zip(a, d))

    Z = Q(0)
    A2 = Q(0)
    for a in xs:
        for b in ys:
            ga = g(a, b)
            if ga == 0:
                continue
            A2 += ga * ga
            tg = Q(0)
            for n, cnt in shifts.items():
                s = 0
                for key, c in cnt.items():
                    if key is None:
                        continue
                    da, db = key
                    s += c * g(add(a, da, modI), add(b, db, modJ))
                tg += Q(s, nunits)
            Z += ga * tg
    return Z, A2


def random_weights(rng, n1, n2):
    W = [[Q(rng.choice([0, 0, 1, 2, 3, 5, 7, 11, 13]), rng.choice([1, 2, 3, 4, 7])) for _ in range(n2)]
         for _ in range(n1)]
    W[0][0] = Q(rng.randint(1, 9), rng.randint(1, 5))
    return W


CASES = [  # (p, f, h, I, J, k)
    (2, 1, [0], 3, 3, 0), (2, 1, [0], 3, 3, 1), (2, 1, [0], 3, 2, 2), (2, 1, [0], 4, 4, 1),
    (3, 1, [0], 3, 3, 0), (3, 1, [0], 3, 3, 2), (3, 1, [0], 2, 3, 1),
    (5, 1, [0], 2, 2, 0), (5, 1, [0], 2, 2, 1), (5, 1, [0], 2, 1, 3),
    (7, 1, [0], 2, 2, 2),
    (2, 2, [1, 1], 2, 2, 0), (2, 2, [1, 1], 2, 2, 1), (2, 2, [1, 1], 2, 2, 3),   # Q = 4, h = t^2+t+1
    (3, 2, [1, 0], 2, 2, 1),                                                      # Q = 9, h = t^2+1
    (2, 4, [1, 1, 0, 0], 1, 1, 2),                                                # Q = 16, h = t^4+t+1
]


def main():
    rng = random.Random(20261005)
    ok = 0
    for (p, f, h, I_, J, k) in CASES:
        Qn = p**f
        for trial in range(3):
            W = random_weights(rng, I_ + 1, J + 1)
            if trial == 2:   # also a symmetric product-free but monotone example
                W = [[Q(1, (i + 1) * (j + 2) + i * i * j) for j in range(J + 1)] for i in range(I_ + 1)]
            Z, A2 = brute_force_overlap(p, f, h, I_, J, k, W)
            Zs = shell_overlap(Qn, k, W)[0]
            Zr = rectangle_overlap(Qn, k, W)
            m1, m2 = shell_masses(Qn, I_ + 1), shell_masses(Qn, J + 1)
            A2s = sum((m1[i] * m2[j] * W[i][j]**2 for i in range(I_ + 1) for j in range(J + 1)), Q(0))
            status = (Z == Zs == Zr) and A2 == A2s
            ok += status
            print(f"Q={Qn:2d} (p={p},f={f}) I={I_} J={J} k={k} trial={trial}: brute Z'={Z}  shell={Zs}  "
                  f"balls={Zr}  A'(p=2) brute={A2} shell={A2s}  {'OK' if status else 'MISMATCH'}", flush=True)
            assert status
    print(f"all {ok} brute-force cases agree")


if __name__ == "__main__" and "--negative" not in sys.argv:
    main()


def negative_control():
    """A wrong kernel (Delta_ii = i m_i, dropping -Q^{i-1}; or no k+1 factor) must disagree with the brute force."""
    from fractions import Fraction as Q
    import general_windows as GW
    W = [[Q(1), Q(1, 3), Q(0)], [Q(1, 2), Q(1, 5), Q(1, 7)], [Q(0), Q(1, 11), Q(1, 13)]]
    p, f, h, I_, J, k = 3, 1, [0], 2, 2, 1
    Z, _ = brute_force_overlap(p, f, h, I_, J, k, W)
    good = GW.shell_overlap(3, k, W)[0]
    saved = GW.shell_delta
    try:
        GW.shell_delta = lambda norm, n: [[GW.shell_masses(norm, n)[min(i, j)] if i != j else i * GW.shell_masses(norm, n)[i]
                                           for j in range(n)] for i in range(n)]
        bad = GW.shell_overlap(3, k, W)[0]
    finally:
        GW.shell_delta = saved
    print("negative control: brute", Z, " correct kernel", good, " wrong Delta_ii", bad,
          " detected:", Z == good and Z != bad)
    assert Z == good and Z != bad


if __name__ == "__main__" and "--negative" in sys.argv:
    negative_control()
