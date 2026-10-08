"""C93 check: series arithmetic and Frobenius congruences for R5-quotient-repair.

Verifies (stdlib only):
- 1/(1-8t+21t^2+2t^3+7t^4) has a0..a5 = 1,8,43,174,466,-68.
- Negativity threshold: with q quartics, a5 = 44-16q, so a5<0 iff q>=3.
- Uncapped 1/(1-8t+7t^2) has all coeffs >0 (closed form (7^{n+1}-1)/6).
- Cyclotomic congruences: 13^4=28561=17 mod 32 (Frob29^4 nontrivial on mu32);
  9^2=81=1 mod 16 (Frob^4 trivial on mu16 at 29/41); 3^2=9, 5^2=25=9 mod 16
  (phi^2 nontrivial on mu16 at q,r with N=3,5); 9=1 mod 8 (phi^2 trivial on mu8).

Usage: python3 research/2026-10-muse-involution-class/code/C93/c93_quotient_repair_check.py
"""
from fractions import Fraction


def series(a2, a3, q, n):
    # 1/(1-8t+a2 t^2+a3 t^3+q t^4), exact integers
    a = [0] * (n + 1)
    a[0] = 1
    for k in range(1, n + 1):
        v = 8 * (a[k - 1] if k - 1 >= 0 else 0)
        v -= a2 * (a[k - 2] if k - 2 >= 0 else 0)
        v -= a3 * (a[k - 3] if k - 3 >= 0 else 0)
        v -= q * (a[k - 4] if k - 4 >= 0 else 0)
        a[k] = v
    return a


def main():
    # Capped P(t) = 1-8t+21t^2+2t^3+7t^4
    got = series(21, 2, 7, 5)
    assert got == [1, 8, 43, 174, 466, -68], got
    print("capped a0..a5 =", got)
    # Threshold in q
    for q, want5 in [(0, 44), (2, 12), (3, -4), (6, -52), (7, -68)]:
        g = series(21, 2, q, 5)
        assert g[5] == 44 - 16 * q == want5, (q, g[5])
    print("threshold a5 = 44-16q: q>=3 gives a5<0")
    # Uncapped 1/(1-8t+7t^2): closed form (7^{n+1}-1)/6 > 0
    u = series(7, 0, 0, 10)
    for n, v in enumerate(u):
        assert v == (7 ** (n + 1) - 1) // 6 > 0, (n, v)
    print("uncapped coeffs >0 through a10:", u[:6], "...")
    # Frobenius congruences
    assert pow(13, 4, 32) == 17, pow(13, 4, 32)
    assert pow(13, 4) == 28561 and 28561 % 32 == 17
    assert pow(29, 4, 16) == 1 and pow(29, 4, 32) == 17
    assert 41 % 16 == 9 and pow(41, 2, 16) == 1
    assert pow(3, 2, 16) == 9 and pow(5, 2, 16) == 9  # nontrivial on mu16
    assert pow(3, 2, 8) == 1 and pow(5, 2, 8) == 1  # trivial on mu8
    assert pow(9, 2, 16) == 1  # Frob^4 trivial on mu16
    print("congruences: 13^4=17 mod32; 3^2=5^2=9 mod16; 9^2=1 mod16; 41=9 mod16")
    print("C93 CHECK PASS")


if __name__ == "__main__":
    main()
