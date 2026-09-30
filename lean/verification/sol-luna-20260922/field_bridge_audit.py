#!/usr/bin/env python3
"""Check the literal Lean nineteen-radical field against the manuscript table.

This deliberately does not import the manuscript's certificate code. It reads
the selected Challenge and the published TeX, reconstructs the relevant
squareclasses and quadratic forms from those two sources, and uses integer
arithmetic throughout.
"""

from __future__ import annotations

import hashlib
import json
import re
import tarfile
from math import isqrt
from pathlib import Path


HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
RESEARCH = PROJECT.parent
CHALLENGE = PROJECT / "ChallengeZeta.lean"
MANUSCRIPT = RESEARCH / "publication/unit-distance-1.0418235/sections/retained-field.tex"
if not MANUSCRIPT.is_file():
    MANUSCRIPT = PROJECT / "docs/manuscript/sections/retained-field.tex"
ARCHIVE = PROJECT / "dist/conditional-20260922/conditional-source-08.tar.gz"
CENSUS_PREFIX = HERE / "numerics_h7_census_prefix.txt"
CENSUS_PREFIX_SHA256 = "fafbdaff49c1317d2606df81ca886fea6fb01200b4da7d490e7550bb84b342b3"
EULER_CERTIFICATE = RESEARCH / "publication/unit-distance-1.0418235/certificates/euler.json"
if not EULER_CERTIFICATE.is_file():
    EULER_CERTIFICATE = HERE / "euler-source.json"
CHALLENGE_SHA256 = "9e0b573c7a89624c8494d38306576428cedd9a1aca109586b724c552965a227a"
MANUSCRIPT_SHA256 = "dfdd48ba5a2445c94cc8a27b86463a6ece86dc46f57c6eeabff78d5470bdf50d"
EULER_SHA256 = "4f01e9ae1f0f79f6575955745c1bdf6ce349a03b6990e2e4189a5205426088af"


def lean_array(source: str, name: str, size: int) -> tuple[int, ...]:
    match = re.search(
        rf"\bdef\s+{name}\s*:\s*Fin\s+{size}\s*→\s*[^:]+?:=\s*!\[([^]]+)\]",
        source,
    )
    if match is None:
        raise ValueError(f"Lean array {name} not found")
    result = tuple(int(item.strip()) for item in match.group(1).split(","))
    if len(result) != size:
        raise ValueError(f"Lean array {name} has {len(result)} entries, expected {size}")
    return result


def tex_catalog(source: str) -> tuple[tuple[int, int, int, int, int], ...]:
    block = source.split(r"\label{ar:norm-table}", 1)[1].split(r"\end{array}", 1)[0]
    rows: list[tuple[int, int, int, int, int]] = []
    for line in block.splitlines():
        match = re.fullmatch(
            r"\s*(\d+)\s*&\s*(-?\d+)\s*&\s*(\d+)\s*&\s*(-?\d+)\s*&\s*(-?\d+)\s*&\s*(\d+)(?:\\\\)?\s*",
            line,
        )
        if match:
            index, a, b, x, y, z = map(int, match.groups())
            if index != len(rows):
                raise ValueError(f"Unexpected catalog row index {index}")
            rows.append((a, b, x, y, z))
    if len(rows) != 17:
        raise ValueError(f"Found {len(rows)} manuscript catalog rows, expected 17")
    return tuple(rows)


def tex_words(source: str, letter: str) -> tuple[int, ...]:
    match = re.search(rf"\\mathcal {letter}&=\(([^)]*)\)", source)
    if match is None:
        raise ValueError(f"Manuscript word list {letter} not found")
    return tuple(int(item.strip()) for item in match.group(1).split(","))


def squareclass_mask(n: int, basis: tuple[int, ...]) -> int:
    if n == 0:
        raise ValueError("Zero has no squareclass")
    mask = int(n < 0)
    n = abs(n)
    for i, prime in enumerate(basis[1:], 1):
        exponent = 0
        while n % prime == 0:
            n //= prime
            exponent += 1
        if exponent % 2:
            mask |= 1 << i
    if n != 1:
        raise ValueError(f"Unsupported prime in squareclass: residual {n}")
    return mask


def basis_product(mask: int, basis: tuple[int, ...]) -> int:
    result = 1
    for i, value in enumerate(basis):
        if mask >> i & 1:
            result *= value
    return result


def quadratic_values(a_mask: int, b_mask: int) -> int:
    """128-bit truth table of v ↦ χ_A(v)χ_B(v) on F₂⁷."""
    result = 0
    for v in range(128):
        if (a_mask & v).bit_count() % 2 and (b_mask & v).bit_count() % 2:
            result |= 1 << v
    return result


def form_coordinates(values: int) -> int:
    """Recover seven square and 21 cross coordinates from evaluations."""
    coefficients = 0
    for i in range(7):
        coefficients |= ((values >> (1 << i)) & 1) << i
    column = 7
    for i in range(7):
        for j in range(i + 1, 7):
            cross = (
                ((values >> ((1 << i) | (1 << j))) & 1)
                ^ ((values >> (1 << i)) & 1)
                ^ ((values >> (1 << j)) & 1)
            )
            coefficients |= cross << column
            column += 1
    return coefficients


def span_basis(vectors: tuple[int, ...]) -> dict[int, int]:
    pivots: dict[int, int] = {}
    for vector in vectors:
        while vector:
            pivot = vector.bit_length() - 1
            if pivot in pivots:
                vector ^= pivots[pivot]
            else:
                pivots[pivot] = vector
                break
    return pivots


def in_span(vector: int, pivots: dict[int, int]) -> bool:
    while vector:
        pivot = vector.bit_length() - 1
        if pivot not in pivots:
            return False
        vector ^= pivots[pivot]
    return True


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def primes_through(limit: int) -> tuple[int, ...]:
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p * p : limit + 1 : p] = b"\x00" * ((limit - p * p) // p + 1)
    return tuple(p for p in range(2, limit + 1) if flags[p])


def check() -> dict[str, object]:
    if not __debug__:
        raise RuntimeError("Python assertions are required; do not run with -O")
    lean = CHALLENGE.read_text()
    tex = MANUSCRIPT.read_text()
    assert sha256(CHALLENGE) == CHALLENGE_SHA256
    assert sha256(MANUSCRIPT) == MANUSCRIPT_SHA256
    archive_compared = ARCHIVE.is_file()
    if archive_compared:
        with tarfile.open(ARCHIVE, "r:gz") as sealed:
            for member, local in (
                ("unit-distance-zeta/ChallengeZeta.lean", CHALLENGE),
                ("unit-distance-zeta/docs/manuscript/sections/retained-field.tex", MANUSCRIPT),
            ):
                file = sealed.extractfile(member)
                if file is None or file.read() != local.read_bytes():
                    raise ValueError(f"Archive 08 differs from working source: {member}")
    basis = lean_array(lean, "rationalRadicands", 7)
    assert basis == (-1, 2, 3, 5, 7, 11, 13)
    masks = lean_array(lean, "rootMasks", 17)
    xs = lean_array(lean, "catalogX", 17)
    ys = lean_array(lean, "catalogY", 17)
    lean_words = lean_array(lean, "wordMasks", 12)
    catalog = tex_catalog(tex)
    completed_words = tex_words(tex, "A")
    retained_words = tex_words(tex, "B")
    assert len(completed_words) == 7
    assert lean_words == retained_words
    if sha256(CENSUS_PREFIX) != CENSUS_PREFIX_SHA256:
        raise ValueError("Independent census prefix data hash changed")
    census_lines = CENSUS_PREFIX.read_text().splitlines()
    census_rows = []
    census_completed = census_retained = census_order = None
    for line in census_lines:
        tokens = line.split()
        if not tokens:
            continue
        if tokens[0] == "field":
            index, *row = map(int, tokens[1:])
            if index != len(census_rows):
                raise ValueError("Census field rows are out of order")
            census_rows.append(tuple(row))
        elif tokens[0] == "completed_linear_masks":
            census_completed = tuple(map(int, tokens[1:]))
        elif tokens[0] == "union_linear_masks":
            census_retained = tuple(map(int, tokens[1:]))
        elif tokens[0] == "predicate_order":
            census_order = tuple(map(int, tokens[1:]))
    assert tuple(census_rows) == catalog
    assert census_completed == completed_words
    assert census_retained == retained_words
    assert census_order == completed_words + retained_words

    catalog_truth = []
    for i, (a, b, x, y, z) in enumerate(catalog):
        assert basis_product(masks[i], basis) == a, (i, "radicand mask")
        assert (xs[i], ys[i]) == (x, y), (i, "catalog coefficients")
        assert x * x - a * y * y == b * z * z, (i, "norm identity")
        catalog_truth.append(quadratic_values(masks[i], squareclass_mask(b, basis)))

    def word_truth(word: int) -> int:
        if word < 0 or word >= 1 << len(catalog_truth):
            raise ValueError(f"Catalog word outside 17-bit range: {word}")
        value = 0
        for i, truth in enumerate(catalog_truth):
            if word >> i & 1:
                value ^= truth
        return value

    def word_form(word: int) -> int:
        return form_coordinates(word_truth(word))

    completed_forms = tuple(word_form(word) for word in completed_words)
    retained_forms = tuple(word_form(word) for word in retained_words)
    printed_hex = re.findall(r"\\texttt\{([0-9a-f]+)\}", tex)
    assert tuple(f"{form:x}" for form in completed_forms + retained_forms) == tuple(printed_hex[:19])
    completed_basis = span_basis(completed_forms)
    retained_basis = span_basis(retained_forms)
    assert len(completed_basis) == 7
    assert len(retained_basis) == 12
    assert all(in_span(form, retained_basis) for form in completed_forms)

    # Independent prime-list check for the order-four correction. The
    # completed field has residue degree two at a nonzero genus Frobenius
    # vector when all seven completed quadratic forms vanish there; one
    # nonvanishing retained form forces degree four in the full field.
    completed_truth = tuple(word_truth(word) for word in completed_words)
    retained_truth = tuple(word_truth(word) for word in retained_words)
    order_four = []
    for p in primes_through(10000):
        if p in (2, 3, 5, 7, 11, 13, 17):
            continue
        v = 0
        for i, radicand in enumerate(basis):
            symbol = pow(radicand % p, (p - 1) // 2, p)
            if symbol == p - 1:
                v |= 1 << i
            elif symbol != 1:
                raise ValueError(f"Unexpected Legendre value for p={p}, i={i}")
        if v and all(not (form >> v) & 1 for form in completed_truth) and any(
            (form >> v) & 1 for form in retained_truth
        ):
            order_four.append(p)
    euler = json.loads(EULER_CERTIFICATE.read_bytes())
    assert sha256(EULER_CERTIFICATE) == EULER_SHA256
    assert order_four == euler["retained_forced_primes"]
    assert len(order_four) == 45

    return {
        "status": "pass",
        "challenge_sha256": sha256(CHALLENGE),
        "manuscript_field_section_sha256": sha256(MANUSCRIPT),
        "archive08_sha256": sha256(ARCHIVE) if archive_compared else None,
        "archive08_byte_comparison_performed": archive_compared,
        "archive08_inputs_equal_working_sources": archive_compared,
        "sealed_archive08_source_hashes_match": True,
        "census_prefix_sha256": sha256(CENSUS_PREFIX),
        "census_prefix_forms_and_predicates_equal_sources": True,
        "euler_certificate_sha256": sha256(EULER_CERTIFICATE),
        "order_four_primes_recomputed": len(order_four),
        "order_four_prime_list_equal_certificate": True,
        "checked_norm_rows": len(catalog),
        "lean_retained_words_equal_manuscript": True,
        "quadratic_form_hex_equal_manuscript": True,
        "completed_form_rank": len(completed_basis),
        "retained_form_rank": len(retained_basis),
        "completed_form_span_inside_retained": True,
        "scope": "Literal field-data and finite quadratic-form cross-check only; no zeta bound or field-degree proof.",
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
