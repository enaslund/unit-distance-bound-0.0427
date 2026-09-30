#!/usr/bin/env python3
"""Independent H7 census replay around 1e7--1e8 plus one distant bin.

This checker uses a byte segmented sieve, modular Legendre-symbol tests, and
ordinary finite-field arithmetic.  It imports no census producer or existing
prefix checker.  The pinned 1e12 census is only the comparison table.
"""

from __future__ import annotations

import hashlib
import json
from math import isqrt
from pathlib import Path


HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
RESEARCH = PROJECT.parent
RESEARCH_TABLE = RESEARCH / "publication/nonabelian-dyadic-lower-bound/research/h7-census-1000000000000.txt"
PACKAGED_TABLE = HERE / "numerics_h7_census_full.txt"
TABLE = RESEARCH_TABLE if RESEARCH_TABLE.is_file() else PACKAGED_TABLE
CENSUS_SOURCE = RESEARCH / "publication/nonabelian-dyadic-lower-bound/research/h7-census.py"
EULER_RECEIPT = HERE / "euler-source.json"
PREFIX_DATA = HERE / "numerics_h7_census_prefix.txt"
OUT = HERE / "h7_census_suffix_check.json"

TABLE_SHA256 = "43669734971ae82bdf2980bbacd869a65224fe3cececb121cf2fbc14936813f2"
CENSUS_SOURCE_SHA256 = "3bf8a7af2e4b9d219e9ddc6f35631333fa67dc283291b0c1040332a1487be493"
EULER_RECEIPT_SHA256 = "4f01e9ae1f0f79f6575955745c1bdf6ce349a03b6990e2e4189a5205426088af"
PREFIX_DATA_SHA256 = "fafbdaff49c1317d2606df81ca886fea6fb01200b4da7d490e7550bb84b342b3"
MODULUS = 120_120
DENOMINATOR = 10**30
TABLE_LIMIT = 10**12
SUFFIX_LOW = 10**7
SUFFIX_HIGH = 10**8
DISTANT_TARGET = 10**10


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def require_hash(path: Path, expected: str, label: str) -> str:
    actual = sha256(path)
    if actual != expected:
        raise ValueError(f"{label} SHA-256 mismatch: {actual}")
    return actual


def parse_census(path: Path) -> tuple[dict[str, object], list[tuple[int, ...]]]:
    lines = path.read_text().splitlines()
    if not lines or lines[0] != "NONABELIAN_DYADIC_H7_CENSUS_V1" or lines[-1] != "END":
        raise ValueError("unexpected full-census framing")
    metadata: dict[str, object] = {}
    bins: list[tuple[int, ...]] = []
    fields: list[tuple[int, ...]] = []
    for line in lines[1:-1]:
        key, *tokens = line.split()
        vals = tuple(map(int, tokens))
        if key == "bin":
            if len(vals) != 8:
                raise ValueError("malformed census bin")
            bins.append(vals)
        elif key == "field":
            if len(vals) != 6 or vals[0] != len(fields):
                raise ValueError("malformed or reordered field row")
            fields.append(vals[1:])
        else:
            if key in metadata:
                raise ValueError(f"duplicate census metadata: {key}")
            metadata[key] = vals[0] if len(vals) == 1 else vals
    metadata["fields"] = fields
    return metadata, bins


def parse_prefix(path: Path) -> tuple[dict[str, object], list[tuple[int, ...]]]:
    lines = path.read_text().splitlines()
    if not lines or lines[0] != "NONABELIAN_DYADIC_H7_CENSUS_V1" or lines[-1] != "END":
        raise ValueError("unexpected prefix framing")
    metadata: dict[str, object] = {}
    bins: list[tuple[int, ...]] = []
    for line in lines[1:-1]:
        key, *tokens = line.split()
        vals = tuple(map(int, tokens))
        if key == "bin":
            if len(vals) != 8:
                raise ValueError("malformed prefix bin")
            bins.append(vals)
        elif key != "field":
            if key in metadata:
                raise ValueError(f"duplicate prefix metadata: {key}")
            metadata[key] = vals[0] if len(vals) == 1 else vals
    return metadata, bins


def prime_flags(limit: int) -> bytearray:
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p * p : limit + 1 : p] = b"\x00" * ((limit - p * p) // p + 1)
    return flags


def segmented_primes(lo: int, hi: int):
    """Yield every prime in the inclusive integer interval [lo, hi]."""
    if lo > hi:
        return
    marked = bytearray(b"\x01") * (hi - lo + 1)
    base_flags = prime_flags(isqrt(hi))
    for q in (q for q in range(2, len(base_flags)) if base_flags[q]):
        first = max(q * q, ((lo + q - 1) // q) * q)
        if first <= hi:
            marked[first - lo : hi - lo + 1 : q] = b"\x00" * ((hi - first) // q + 1)
    for i, flag in enumerate(marked):
        n = lo + i
        if flag and n >= 2:
            yield n


def sqrt_mod_prime(a: int, p: int) -> int:
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        raise ValueError(f"expected square {a} modulo p={p}")
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
                raise ValueError("Tonelli-Shanks failed")
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    if r * r % p != a:
        raise ValueError("Tonelli-Shanks returned an invalid root")
    return r


def geometric_bins(stop_at: int) -> list[tuple[int, int]]:
    edges = []
    lo = 13
    while lo < stop_at:
        hi = min(TABLE_LIMIT, max(lo + 1, (1001 * lo + 999) // 1000))
        edges.append((lo, hi))
        if hi >= stop_at:
            break
        lo = hi
    return edges


def containing_bin(edges: list[tuple[int, int]], x: int) -> int:
    # Census assignment uses p > previous_hi, so each bin has support (lo,hi].
    for i, (_, hi) in enumerate(edges):
        if hi >= x:
            return i
    raise ValueError(f"no generated census bin contains {x}")


def empty_row(edge: tuple[int, int]) -> tuple[int, ...]:
    return (*edge, 0, 0, 0, 0, 0, 0)


def main() -> None:
    if not __debug__:
        raise RuntimeError("Assertions are required; do not run Python with -O")
    hash_table = require_hash(TABLE, TABLE_SHA256, "pinned 1e12 census table")
    census_source_available = CENSUS_SOURCE.is_file()
    hash_source = (
        require_hash(CENSUS_SOURCE, CENSUS_SOURCE_SHA256, "H7 census source")
        if census_source_available else CENSUS_SOURCE_SHA256
    )
    hash_euler = require_hash(EULER_RECEIPT, EULER_RECEIPT_SHA256, "Euler source receipt")
    hash_prefix = require_hash(PREFIX_DATA, PREFIX_DATA_SHA256, "independent 1e7 prefix")
    meta, stored_bins = parse_census(TABLE)
    euler = json.loads(EULER_RECEIPT.read_text())
    bound = euler["source_sha256"]
    if bound.get("nonabelian-dyadic-lower-bound/research/h7-census-1000000000000.txt") != hash_table:
        raise ValueError("Euler receipt does not bind to the pinned 1e12 table")
    if bound.get("nonabelian-dyadic-lower-bound/research/h7-census.py") != hash_source:
        raise ValueError("Euler receipt does not bind to the pinned census source")
    if (int(meta["limit"]), int(meta["modulus"]), int(meta["denominator"])) != (
        TABLE_LIMIT, MODULUS, DENOMINATOR
    ):
        raise ValueError("unexpected table limit/modulus/reciprocal denominator")
    fields = [tuple(map(int, row)) for row in meta["fields"]]
    if len(fields) != 17:
        raise ValueError(f"expected 17 field predicates, found {len(fields)}")
    for A, B, x, y, z in fields:
        if x * x - A * y * y != B * z * z:
            raise ValueError("a stored norm identity failed")
    completed = tuple(map(int, meta["completed_linear_masks"]))
    full = tuple(map(int, meta["union_linear_masks"]))
    order = tuple(map(int, meta["predicate_order"]))
    if len(completed) != 7 or len(full) != 12 or order != completed + full:
        raise ValueError("unexpected completed/full predicate data")
    allowed = {
        r for r in range(1, MODULUS, 8)
        if all(pow(r % ell, (ell - 1) // 2, ell) == 1 for ell in (3, 5, 7, 11, 13))
    }
    if len(allowed) != int(meta["residue_classes"]) or len(allowed) != 180:
        raise ValueError("genus-split residue-class count differs")

    edges = geometric_bins(DISTANT_TARGET)
    low_bin = containing_bin(edges, SUFFIX_LOW)
    high_bin = containing_bin(edges, SUFFIX_HIGH)
    distant_bin = containing_bin(edges, DISTANT_TARGET)
    if high_bin < low_bin:
        raise ValueError("bad suffix boundary-bin order")
    groups = [(low_bin, high_bin), (distant_bin, distant_bin)]
    target_indices = sorted({i for first, last in groups for i in range(first, last + 1)})
    expected_by_edge: dict[tuple[int, int], tuple[int, ...]] = {}
    for row in stored_bins:
        edge = (row[0], row[1])
        if edge in expected_by_edge:
            raise ValueError(f"duplicate full-census bin {edge}")
        expected_by_edge[edge] = row
    actual_by_index = {i: [0, 0, 0, 0, 0, 0] for i in target_indices}
    hits = [0] * len(order)
    genus_split = selected_full = selected_completed = 0
    partial_first_bin = [0, 0, 0, 0, 0, 0]
    prefix_meta, prefix_bins = parse_prefix(PREFIX_DATA)
    if int(prefix_meta["limit"]) != SUFFIX_LOW or int(prefix_meta["denominator"]) != DENOMINATOR:
        raise ValueError("prefix boundary-check metadata differs")
    prefix_boundary = next((row for row in prefix_bins if row[1] == SUFFIX_LOW), None)
    first_edge = edges[low_bin]
    if prefix_boundary is None or prefix_boundary[0] != first_edge[0]:
        raise ValueError("prefix file lacks the expected partial lower-boundary bin")

    def consume_segment(first: int, last: int) -> None:
        nonlocal genus_split, selected_full, selected_completed
        lo, hi = edges[first][0] + 1, edges[last][1]
        local_edges = edges[first : last + 1]
        edge_pos = 0
        for p in segmented_primes(lo, hi):
            if p % MODULUS not in allowed:
                continue
            genus_split += 1
            state = 0
            for i, (A, B, x, y, z) in enumerate(fields):
                root = sqrt_mod_prime(A, p)
                value = pow((x + y * root) % p, (p - 1) // 2, p)
                conjugate = pow((x - y * root) % p, (p - 1) // 2, p)
                if value not in (1, p - 1) or conjugate != value:
                    raise ValueError(f"bad form evaluation at p={p}, field={i}")
                if value == p - 1:
                    state |= 1 << i
            first_hit = next(
                (j for j, mask in enumerate(order) if (mask & state).bit_count() & 1), None
            )
            if first_hit is None:
                continue
            hits[first_hit] += 1
            selected_full += 1
            is_completed = first_hit < len(completed)
            if is_completed:
                selected_completed += 1
            while p > local_edges[edge_pos][1]:
                edge_pos += 1
            bin_index = first + edge_pos
            row = actual_by_index[bin_index]
            reciprocal = DENOMINATOR // p
            row[0] += 1
            row[1] += reciprocal
            row[2 if is_completed else 4] += 1
            row[3 if is_completed else 5] += reciprocal
            if first == low_bin and p <= SUFFIX_LOW:
                partial_first_bin[0] += 1
                partial_first_bin[1] += reciprocal
                partial_first_bin[2 if is_completed else 4] += 1
                partial_first_bin[3 if is_completed else 5] += reciprocal

    for first, last in groups:
        consume_segment(first, last)

    matches = []
    empty_matches = 0
    for i in target_indices:
        edge = edges[i]
        recorded = expected_by_edge.get(edge, empty_row(edge))
        row = actual_by_index[i]
        computed = (edge[0], edge[1], *row)
        if computed != recorded:
            raise ValueError(f"census suffix mismatch at bin {edge}: computed {computed}, recorded {recorded}")
        if row[0] == 0:
            empty_matches += 1
        matches.append({"lo": edge[0], "hi": edge[1], "census_row": list(computed)})

    expected_prefix = tuple(map(int, prefix_boundary))
    computed_prefix = (first_edge[0], SUFFIX_LOW, *partial_first_bin)
    if computed_prefix != expected_prefix:
        raise ValueError(
            f"partial 1e7 boundary differs from independent prefix: {computed_prefix} != {expected_prefix}"
        )

    suffix_indices = list(range(low_bin, high_bin + 1))
    complete_suffix = [
        i for i in suffix_indices
        if edges[i][0] >= SUFFIX_LOW and edges[i][1] < SUFFIX_HIGH
    ]
    boundary_suffix = [i for i in suffix_indices if i not in complete_suffix]
    distant_edge = edges[distant_bin]
    selected_expected = sum(actual_by_index[i][0] for i in target_indices)
    selected_completed_expected = sum(actual_by_index[i][2] for i in target_indices)
    selected_complement_expected = sum(actual_by_index[i][4] for i in target_indices)
    if selected_full != selected_expected or selected_completed != selected_completed_expected:
        raise ValueError("aggregate selected counts do not equal regenerated bin totals")
    if selected_full - selected_completed != selected_complement_expected:
        raise ValueError("aggregate complement count does not equal regenerated bin totals")

    result = {
        "status": "PASS independent finite-field suffix/bin replay",
        "scope": "Independent replay of complete H7 census bins touching [1e7,1e8), plus one complete bin containing 1e10; compares counts, reciprocal floors, and completed/complement splits against the pinned 1e12 table.",
        "source_sha256": {
            "suffix_checker": sha256(Path(__file__)),
            "h7_census_table": hash_table,
            "h7_census_source": hash_source,
            "euler_source_receipt": hash_euler,
            "independent_1e7_prefix": hash_prefix,
        },
        "table_path": str(TABLE),
        "census_source_file_available": census_source_available,
        "table_limit": TABLE_LIMIT,
        "reciprocal_denominator": DENOMINATOR,
        "suffix_requested": [SUFFIX_LOW, SUFFIX_HIGH],
        "suffix_bins_including_boundaries": [edges[low_bin], edges[high_bin]],
        "suffix_boundary_bins_straddle_requested_range": [edges[i] for i in boundary_suffix],
        "complete_bins_inside_requested_suffix_count": len(complete_suffix),
        "complete_bins_inside_requested_suffix": [edges[i] for i in complete_suffix],
        "complete_bins_including_suffix_boundaries_count": len(suffix_indices),
        "distant_complete_bin_containing_1e10": list(distant_edge),
        "all_compared_bins_count": len(target_indices),
        "matched_nonempty_bins": len(matches) - empty_matches,
        "matched_empty_bins": empty_matches,
        "matched_bins": matches,
        "partial_lower_boundary_prefix_crosscheck": {
            "bin": [first_edge[0], SUFFIX_LOW],
            "computed": list(computed_prefix),
            "recorded": list(expected_prefix),
            "matches": True,
        },
        "genus_split_primes_in_sieved_segments": genus_split,
        "selected_full_count_in_sieved_segments": selected_full,
        "selected_completed_count_in_sieved_segments": selected_completed,
        "selected_complement_count_in_sieved_segments": selected_full - selected_completed,
        "first_hit_counts_in_sieved_segments": hits,
        "segmented_sieve_intervals_inclusive": [
            [edges[first][0] + 1, edges[last][1]] for first, last in groups
        ],
        "predicate_field_count": len(fields),
        "predicate_order_count": len(order),
        "modulus_residue_classes": len(allowed),
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "matched_bins" and k != "complete_bins_inside_requested_suffix"}, indent=2))


if __name__ == "__main__":
    main()
