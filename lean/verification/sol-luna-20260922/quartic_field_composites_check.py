#!/usr/bin/env python3
"""Check every unramified coefficient through 981 from quartic root counts.

The selected mixed quadratic row has degree two.  For good p, point counts
give Tr(Frob_p) and Tr(Frob_p^2), hence the p and p^2 Euler coefficients.
Multiplicativity then determines every coefficient whose prime factors are
good.  This compares that independently reconstructed sequence with the
pinned row, leaving ramified Euler factors and the global Artin identity open.
"""

from __future__ import annotations

import hashlib
import json
from math import isqrt
from pathlib import Path

import numerics_hecke_coeff_check as coefficient_check
import quartic_field_trace_check as field_check


FIELD_CHECK_SHA256 = "58c56d92ce43839d191df20fc7d0264135aff6c91f8d7415e4b6593dcb2e6b72"
OUT = field_check.HERE / "quartic_field_composites_check.json"


def roots_at_prime(p: int, a: int, b: int, c: int) -> tuple[int, int]:
    roots_q = sum((u * u - a) % p == 0 for u in range(p))
    roots_k = sum((u**4 + b * u * u + c) % p == 0 for u in range(p))
    return roots_q, roots_k


def local_coefficients(p: int, limit: int, a: int, b: int, c: int) -> tuple[int, int | None]:
    roots_q, roots_k = roots_at_prime(p, a, b, c)
    trace = roots_k - roots_q
    if p * p > limit:
        return trace, None
    nonsquare = next((d for d in range(2, p) if pow(d, (p - 1) // 2, p) == p - 1), None)
    if nonsquare is None:
        raise ValueError(f"No quadratic nonresidue at p={p}")
    roots_q2, roots_k2 = field_check.roots_over_quadratic_extension(p, nonsquare, a, b, c)
    trace2 = roots_k2 - roots_q2
    if (trace * trace + trace2) % 2:
        raise ValueError(f"Nonintegral p^2 coefficient at p={p}")
    return trace, (trace * trace + trace2) // 2


def factor_good(n: int, local: dict[int, tuple[int, int | None]]) -> int | None:
    """Return the multiplicative Euler coefficient; None means bad support."""
    if n == 1:
        return 1
    value = 1
    for p in sorted(local):
        ap, ap2 = local[p]
        if p * p > n and n > 1:
            break
        if n % p:
            continue
        n //= p
        if n % p == 0:
            n //= p
            if n % p == 0 or ap2 is None:
                raise ValueError(f"Unexpected exponent at p={p}")
            value *= ap2
        else:
            value *= ap
    if n > 1:
        factor = local.get(n)
        if factor is None:
            return None
        value *= factor[0]
    return value


def check() -> dict[str, object]:
    if not __debug__:
        raise RuntimeError("Assertions are required; run without Python -O")
    if field_check.digest(Path(field_check.__file__)) != FIELD_CHECK_SHA256:
        raise ValueError("Quartic field source hash changed")
    row, sector, full_source_compared = field_check.source_bound_row()
    if (sector["mask"], sector["dimension"], row["twist"], row["N"]) != (1586, 2, -1, 981):
        raise ValueError("Unexpected row")
    a = int(sector["base_radicands"][0])
    x, y = map(int, sector["eta_coefficients"][:2])
    twist = int(row["twist"])
    b = -2 * twist * x
    c = twist * twist * (x * x - a * y * y)
    if (a, b, c) != (-35, 34, 429):
        raise ValueError("Unexpected quartic/quadratic polynomials")
    # For u = twist*(x+y*sqrt(a)) in Q(sqrt(a)), N(u)=c=429 is not a
    # rational square. Thus u is not a square in that quadratic field and
    # the displayed quartic is irreducible over Q.
    if not (a < 0 and y != 0 and c > 0 and isqrt(c) ** 2 != c):
        raise ValueError("Quartic irreducibility witness failed")
    limit = int(row["N"])
    coefficients = coefficient_check.rank2_first(row, sector, limit)
    vector = [(0, 0), *(tuple(v) for v in coefficients)]
    vector_hash = hashlib.sha256(json.dumps(vector).encode()).hexdigest()
    if vector_hash != row["signed_coefficients_sha256"]:
        raise ValueError("Pinned complete-vector hash differs")

    primes = field_check.primes_through(limit)
    local = {p: local_coefficients(p, limit, a, b, c)
             for p in primes if p not in field_check.RAMIFIED}
    checked = skipped = prime_cases = square_cases = composite_cases = 0
    for n in range(1, limit + 1):
        if any(n % p == 0 for p in field_check.RAMIFIED):
            skipped += 1
            continue
        predicted = factor_good(n, local)
        if predicted is None:
            raise ValueError(f"Unfactored unramified n={n}")
        if coefficients[n - 1] != [predicted, 0]:
            raise ValueError(f"Field-derived coefficient mismatch at n={n}")
        checked += 1
        if n in local:
            prime_cases += 1
        elif any(p * p == n for p in local):
            square_cases += 1
        elif n > 1:
            composite_cases += 1
    if checked + skipped != limit or prime_cases < 100 or square_cases != 5:
        raise ValueError("Unramified coverage count is inconsistent")
    result = {
        "status": "pass",
        "scope": "All n<=981 supported on primes outside 2,3,5,7,11,13, reconstructed from quartic/quadratic root-count traces at p and p^2 and Euler multiplicativity; no ramified factors or global Artin identity.",
        "field_checker_sha256": FIELD_CHECK_SHA256,
        "coefficient_helper_sha256": field_check.COEFFICIENT_HELPER_SHA256,
        "complete_vector_sha256": vector_hash,
        "full_research_sources_compared": full_source_compared,
        "quartic_irreducibility_witness": "Norm_Q(sqrt(-35))/Q(u)=429 is nonsquare",
        "checked_unramified_coefficients": checked,
        "skipped_ramified_support": skipped,
        "prime_cases": prime_cases,
        "square_cases": square_cases,
        "composite_cases": composite_cases,
    }
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
