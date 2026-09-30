#!/usr/bin/env python3
"""Short exact-rational upper bound for the deleted conductor-13 L-value.

This uses a deliberately coarse finite-sum inequality and a period-tail bound;
it is independent of genus13_lvalue_interval.py's log/exp interval routine.
"""

from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
PERIOD = (1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, 1, 0)
PRIMES = (2, 3, 5, 7, 11, 13, 17)
PRIME_CHI = (-1, 1, -1, -1, -1, 0, 1)
SOURCE_HASHES = {
    "lean-formalization/UnitDistance/GenusDirichletConductorsRun20260920.lean":
        "da1f113fb627a0e64651d1b5998f453f7d0e452771ea0a1f18ada752ca9b3a77",
    "lean-formalization/UnitDistance/GenusLunaRun20260922ConductorThirteen.lean":
        "110cc2883052d0cfa0a18f048c809a91154365cf31039e34a0c8c04e83694950",
}


def source_binding() -> str:
    present = [((ROOT / rel).is_file()) for rel in SOURCE_HASHES]
    if any(present) and not all(present):
        raise RuntimeError("partial pinned Lean source set")
    if not any(present):
        return "embedded period/source hashes only; Lean source files absent"
    for rel, expected in SOURCE_HASHES.items():
        actual = sha256((ROOT / rel).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError(f"pinned source hash changed: {rel}")
    genus_src = (ROOT / next(iter(SOURCE_HASHES))).read_text()
    primitive_src = (ROOT / list(SOURCE_HASHES)[1]).read_text()
    if "def primeQuadraticCharacter" not in genus_src:
        raise RuntimeError("quadratic-character definition anchor missing")
    if "conductorThirteen_primitive_apply" not in primitive_src:
        raise RuntimeError("primitive character identification anchor missing")
    return "both pinned Lean sources and binding anchors matched"


def finite_sum_upper(n_cut: int) -> F:
    """Bound sum_{n<=N} chi(n)n^-s above using exp(-x)>=1-x."""
    total = F(0)
    for n in range(1, n_cut + 1):
        chi = PERIOD[(n - 1) % 13]
        if chi == 1:
            # n^-s <= 1/n because s > 1.
            total += F(1, n)
        elif chi == -1:
            # log(n) <= n-1 and e^-x >= 1-x for x >= 0 imply
            # n^-s >= (1/n)(1-(n-1)/12000).
            total += -F(1, n) + F(n - 1, 12000 * n)
    return total


def correction_upper() -> F:
    """Upper-bound product (1-chi(p)p^-s) over selected primes."""
    product = F(1)
    for p, chi in zip(PRIMES, PRIME_CHI):
        if chi == -1:
            # p^-s < 1/p.
            factor = 1 + F(1, p)
        elif chi == 1:
            # log(p) <= p-1 and e^-x >= 1-x give this lower bound on p^-s,
            # hence an upper bound on 1-p^-s.
            factor = 1 - F(1, p) + F(p - 1, 12000 * p)
        else:
            factor = F(1)
        product *= factor
    return product


def chi13(a: int) -> int:
    a %= 13
    if a == 0:
        return 0
    return 1 if pow(a, 6, 13) == 1 else -1


def main() -> None:
    if sum(PERIOD) != 0:
        raise RuntimeError("period does not have mean zero")
    partials = []
    running = 0
    for chi in PERIOD:
        running += chi
        partials.append(running)
    if max(map(abs, partials)) != 2:
        raise RuntimeError("unexpected period partial-sum bound")
    if tuple(chi13(n) for n in range(1, 14)) != PERIOD:
        raise RuntimeError("period does not match the quadratic character mod 13")
    if tuple(chi13(p) for p in PRIMES) != PRIME_CHI:
        raise RuntimeError("selected-prime character values do not match mod 13")

    corr = correction_upper()
    result = None
    for k in range(1, 65):
        n_cut = 13 * k
        primitive_upper = finite_sum_upper(n_cut) + F(2, n_cut + 1)
        deleted_upper = primitive_upper * corr
        if deleted_upper < 1:
            result = (k, n_cut, primitive_upper, deleted_upper)
            break
    if result is None:
        raise RuntimeError("no successful cutoff found through 13*64")
    k, n_cut, primitive_upper, deleted_upper = result
    if deleted_upper <= 0 or primitive_upper <= 0:
        raise RuntimeError("nonpositive bound")
    binding = source_binding()
    print(f"source binding: {binding}")
    print(f"period: {PERIOD}")
    print(f"selected primes: {PRIMES}")
    print(f"selected chi values: {PRIME_CHI}")
    print(f"cutoff N=13*k: {n_cut} (k={k})")
    print(f"finite sum upper: {finite_sum_upper(n_cut)}")
    print(f"period tail absolute upper: 2/{n_cut + 1}")
    print(f"primitive L upper: {primitive_upper}")
    print(f"selected correction upper: {corr}")
    print(f"deleted value upper: {deleted_upper}")
    print(f"strict margin below 1: {1 - deleted_upper}")
    print("conclusion: deleted/common-level value < 1")
    print("scope: exact rational upper bound only; no Lean interval or manuscript row allowance")


if __name__ == "__main__":
    main()
