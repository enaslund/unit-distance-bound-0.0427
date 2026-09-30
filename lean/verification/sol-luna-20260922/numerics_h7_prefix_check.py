#!/usr/bin/env python3
"""Recompute the H7 finite census prefix using a plain Eratosthenes sieve.

This intentionally does not import the manuscript census checker, PARI/GP,
or any certificate code.  The pinned prefix file supplies the field forms,
retained predicates, and the comparison bins; primes and character states are
recomputed here from their finite-field definitions.
"""

from __future__ import annotations

import hashlib
import json
from math import isqrt
from pathlib import Path


HERE = Path(__file__).resolve().parent
DATA = HERE / "numerics_h7_census_prefix.txt"
DATA_SHA256 = "fafbdaff49c1317d2606df81ca886fea6fb01200b4da7d490e7550bb84b342b3"
LEAN_ROOT = HERE.parents[1]
UPSTREAM_SOURCE = HERE / "numerics_h7_census_source.py"
UPSTREAM_SOURCE_SHA256 = "3bf8a7af2e4b9d219e9ddc6f35631333fa67dc283291b0c1040332a1487be493"
REPLAY_RECORD = LEAN_ROOT / "verification/external-zeta-20260922/analytic-replay-20260922.json"
MODULUS = 120120
DENOMINATOR = 10**30


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_data() -> tuple[dict[str, object], list[tuple[int, int, int, int, int]], list[tuple[int, ...]]]:
    digest = sha256(DATA)
    if digest != DATA_SHA256:
        raise AssertionError(f"prefix data hash mismatch: {digest}")
    lines = DATA.read_text().splitlines()
    if lines[0] != "NONABELIAN_DYADIC_H7_CENSUS_V1" or lines[-1] != "END":
        raise AssertionError("unexpected prefix file framing")
    meta: dict[str, object] = {}
    fields: list[tuple[int, int, int, int, int]] = []
    bins: list[tuple[int, ...]] = []
    for line in lines[1:-1]:
        key, *values = line.split()
        vals = tuple(map(int, values))
        if key == "field":
            if vals[0] != len(fields) or len(vals) != 6:
                raise AssertionError("malformed field row")
            fields.append(vals[1:])
        elif key == "bin":
            if len(vals) != 8:
                raise AssertionError("malformed bin row")
            bins.append(vals)
        else:
            if key in meta:
                raise AssertionError(f"duplicate metadata row {key}")
            meta[key] = vals[0] if len(vals) == 1 else vals
    return meta, fields, bins


def primes_below(limit: int) -> bytearray:
    """Byte array sieve; entry p is true exactly for primes p < limit."""
    prime = bytearray(b"\x01") * limit
    prime[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit - 1) + 1):
        if prime[p]:
            start = p * p
            prime[start:limit:p] = b"\x00" * (((limit - 1 - start) // p) + 1)
    return prime


def sqrt_mod_prime(a: int, p: int) -> int:
    """Tonelli-Shanks square root for odd prime p; raises if nonsquare."""
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        raise AssertionError(f"radicand {a} is nonsquare modulo {p}")
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, probe = 1, t * t % p
        while probe != 1:
            probe = probe * probe % p
            i += 1
            if i >= m:
                raise AssertionError("Tonelli-Shanks failed")
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    if r * r % p != a:
        raise AssertionError("invalid square root")
    return r


def main() -> None:
    meta, fields, expected_bins = parse_data()
    source_hash = sha256(UPSTREAM_SOURCE)
    if source_hash != UPSTREAM_SOURCE_SHA256:
        raise AssertionError(f"upstream census source hash mismatch: {source_hash}")
    replay_record = json.loads(REPLAY_RECORD.read_text())
    recorded_source_hash = replay_record["analytic_replay"]["independent_census_prefix"]["source_sha256"][
        "nonabelian-dyadic-lower-bound/research/h7-census.py"
    ]
    if recorded_source_hash != source_hash:
        raise AssertionError("replay record does not bind to the bundled upstream census source")
    limit = int(meta["limit"])
    if (limit, int(meta["modulus"]), int(meta["denominator"])) != (10_000_000, MODULUS, DENOMINATOR):
        raise AssertionError("unexpected census parameters")
    if len(fields) != 17:
        raise AssertionError(f"expected 17 quadratic forms, found {len(fields)}")
    for A, B, x, y, z in fields:
        if x * x - A * y * y != B * z * z:
            raise AssertionError("a stored norm identity failed")

    completed = tuple(map(int, meta["completed_linear_masks"]))
    full = tuple(map(int, meta["union_linear_masks"]))
    order = tuple(map(int, meta["predicate_order"]))
    if order != completed + full:
        raise AssertionError("predicate order does not concatenate completed and full masks")
    prime_residues = {
        r for r in range(1, MODULUS, 8)
        if all(pow(r % ell, (ell - 1) // 2, ell) == 1 for ell in (3, 5, 7, 11, 13))
    }
    if len(prime_residues) != int(meta["residue_classes"]):
        raise AssertionError("genus residue class count mismatch")

    # Independently regenerate prime flags and the finite-field classification.
    prime = primes_below(limit)
    edges: list[tuple[int, int]] = []
    lo = 13
    while lo < limit:
        hi = min(limit, max(lo + 1, (1001 * lo + 999) // 1000))
        edges.append((lo, hi))
        lo = hi
    edge_index = 0
    rows = [[hi, 0, 0, 0, 0, 0, 0, 0] for _, hi in edges]
    hits = [0] * len(order)
    genus_count = full_count = completed_count = 0

    for p in range(17, limit):
        if not prime[p] or p % MODULUS not in prime_residues:
            continue
        genus_count += 1
        state = 0
        for i, (A, B, x, y, z) in enumerate(fields):
            root = sqrt_mod_prime(A, p)
            value = pow((x + y * root) % p, (p - 1) // 2, p)
            conjugate = pow((x - y * root) % p, (p - 1) // 2, p)
            if value not in (1, p - 1) or conjugate != value:
                raise AssertionError(f"bad quadratic character evaluation at p={p}, field={i}")
            if value == p - 1:
                state |= 1 << i
        first_hit = next((j for j, mask in enumerate(order) if (mask & state).bit_count() & 1), None)
        if first_hit is None:
            continue
        hits[first_hit] += 1
        full_count += 1
        done = first_hit < len(completed)
        if done:
            completed_count += 1
        # The archived census convention advances only when p > hi, so a
        # prime exactly at a shared endpoint belongs to the preceding bin.
        while p > edges[edge_index][1]:
            edge_index += 1
        lo, hi = edges[edge_index]
        row = rows[edge_index]
        reciprocal = DENOMINATOR // p
        row[1] += 1
        row[2] += reciprocal
        row[3 if done else 5] += 1
        row[4 if done else 6] += reciprocal

    actual_bins = [
        (lo, hi, row[1], row[2], row[3], row[4], row[5], row[6])
        for (lo, hi), row in zip(edges, rows)
        if row[1]
    ]
    expected = [tuple(map(int, row)) for row in expected_bins]
    if actual_bins != expected:
        for i, (actual, wanted) in enumerate(zip(actual_bins, expected)):
            if actual != wanted:
                raise AssertionError(f"first differing nonempty bin {i}: computed {actual}, recorded {wanted}")
        raise AssertionError(f"bin row count differs: computed {len(actual_bins)}, recorded {len(expected)}")
    if hits != list(meta["predicate_first_hits"]):
        raise AssertionError("predicate-first-hit vector differs")
    counts = (genus_count, full_count, completed_count, full_count - completed_count)
    recorded = tuple(int(meta[k]) for k in ("genus_split_count", "full_count", "completed_count", "complement_count"))
    if counts != recorded:
        raise AssertionError(f"counts differ: computed {counts}, recorded {recorded}")

    print("PASS independent H7 census-prefix recomputation")
    print(f"data_sha256={DATA_SHA256}")
    print(f"upstream_source_sha256={UPSTREAM_SOURCE_SHA256}")
    print(f"replay_record_sha256={sha256(REPLAY_RECORD)}")
    print(f"prime_range=[17,{limit}); genus_split_primes={genus_count}")
    print(f"field_character_evaluations={genus_count * len(fields)}")
    print(f"first_hit_predicates={len(order)}; matching_nonempty_bins={len(expected)}")
    print(f"full={full_count}; completed={completed_count}; complement={full_count-completed_count}")
    print("comparison=every bin endpoint, count, reciprocal sum, class split, and first-hit count matched")


if __name__ == "__main__":
    main()
