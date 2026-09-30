#!/usr/bin/env python3
"""Independent direct-kernel interval check for H6 mask 1586, twist -1.

This evaluates the quadratic AFE's exponential-integral weights directly with
Arb's generalized exponential integral, rather than using the manuscript's
Taylor-grid kernel implementation.  The omitted coefficient tail is bounded
from |a_n| <= d_2(n) <= 2 sqrt(n) and elementary exponential inequalities.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
from fractions import Fraction as Q
from pathlib import Path
import sys

import flint
from flint import arb, ctx


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
FIXTURE = HERE / "numerics_afe_one_factor_fixture.json"
FIXTURE_SHA256 = "3d05b2be40b3392bf48022b57d352ebeb6c0f48dc288944fba77becc108b7505"
RESEARCH = ROOT / "publication/nonabelian-dyadic-lower-bound/research"
AFE_RECORD = RESEARCH / "h7-inherited-euler-12000.json"
MOMENTS = RESEARCH / "h6-low-degree-moments-1586.json"
ARITHMETIC = RESEARCH / "h6-low-degree-arithmetic.json"
COEFFICIENT_CHECKER = HERE / "numerics_hecke_coeff_check.py"

SOURCE_HASHES = {
    "h7-inherited-euler-12000.json": "b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f",
    "h6-low-degree-arithmetic.json": "b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771",
    "h6-low-degree-moments-1586.json": "a7e65537a05389f11115a8cf64c186ead6b1dc4973a8c5f862f31a34fdeb40f1",
    "h6-low-degree-euler.py": "9fdee8fe5bd9fcbc90c9b28ccbdd0ec5066d49b8b52757ee3f20cc89af707f38",
    "nonpositive-afe.py": "8d6b82b12f7de4a3d53feccde8aaffe0d0fbdf4b623c1447af6ea68ed399cba7",
    "next-dyadic-h5-single.py": "f9a97f5c41485914e9700a5efcebb9df0ffdbc834a56a666b994d397ab3a3ba6",
    "numerics_hecke_coeff_check.py": "3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329",
    "numerics_hecke_family_fixture.json": "5fd9c83deb0fcdef56d314657ae8e1c7408c5508e652834e32cdabc3de234200",
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def enc(x: arb) -> dict[str, str | int]:
    m, e = x.upper().man_exp()
    return {"mantissa": str(m), "exponent": int(e), "display": x.str(35, radius=True)}


def endpoint(record: dict[str, object]) -> arb:
    r = record["upper"]
    return arb(int(r["mantissa"])) * arb(2) ** int(r["exponent"])


def interval_from_enclosure(record: dict[str, object]) -> arb:
    def exact(which: str) -> arb:
        value = record[which]
        return arb(int(value["mantissa"])) * arb(2) ** int(value["exponent"])
    return exact("lower").union(exact("upper"))


def source_rows(record: dict[str, object]) -> tuple[dict[str, object], dict[str, object]]:
    if sha(FIXTURE) != FIXTURE_SHA256:
        raise AssertionError("AFE fixture hash mismatch")
    fixture = json.loads(FIXTURE.read_text())
    if fixture.get("schema") != "unit-distance-one-factor-afe-fixture-v1":
        raise AssertionError("unexpected one-factor AFE fixture schema")
    if fixture.get("source_sha256") != SOURCE_HASHES:
        raise AssertionError("one-factor AFE fixture source bindings changed")
    paths = {
        "h7-inherited-euler-12000.json": AFE_RECORD,
        "h6-low-degree-arithmetic.json": ARITHMETIC,
        "h6-low-degree-moments-1586.json": MOMENTS,
        "h6-low-degree-euler.py": RESEARCH / "h6-low-degree-euler.py",
        "nonpositive-afe.py": ROOT / "publication/five-prime-lower-bound/research/nonpositive-afe.py",
        "next-dyadic-h5-single.py": ROOT / "publication/six-dimensional-lower-bound/research/next-dyadic-h5-single.py",
        "numerics_hecke_coeff_check.py": COEFFICIENT_CHECKER,
        "numerics_hecke_family_fixture.json": HERE / "numerics_hecke_family_fixture.json",
    }
    for name, path in paths.items():
        if path.is_file() and sha(path) != SOURCE_HASHES[name]:
            raise AssertionError(f"changed pinned source {name}")
    for required in (COEFFICIENT_CHECKER, HERE / "numerics_hecke_family_fixture.json"):
        if not required.is_file():
            raise FileNotFoundError(f"standalone dependency missing: {required.name}")

    printed = fixture["printed_afe"]
    fixture_row = fixture["row"]
    for key in ("conductor", "N"):
        if fixture_row.get(key) != printed.get(key):
            raise AssertionError(f"fixture row {key} differs from printed AFE selection")
    if printed.get("bad_euler_denominators") != fixture_row.get("bad_euler_denominators"):
        raise AssertionError("fixture bad Euler factors differ from the selected row")
    if printed.get("coefficient_vector_sha256") != fixture_row.get("signed_coefficients_sha256"):
        raise AssertionError("fixture coefficient hash differs from the selected row")
    if AFE_RECORD.is_file():
        source = json.loads(AFE_RECORD.read_text())
        if source["sigma"] != fixture["sigma"]:
            raise AssertionError("AFE sigma differs from the fixture")
        source_sector = next(s for s in source["sectors"] if s["mask"] == fixture["mask"])
        if source_sector["dimension"] != fixture["sector"]["dimension"]:
            raise AssertionError("AFE source sector dimension differs from fixture")
        row = next(r for r in source_sector["rows"] if r["twist"] == fixture["twist"])
        for key in ("kind", "status", "conductor", "N", "rankin_beta",
                    "log_abs_L_S_upper", "removed_modulus_upper", "A_finite", "B_finite"):
            if row.get(key) != printed.get(key):
                raise AssertionError(f"pinned printed row field {key} differs from fixture")
    else:
        row = printed
    if MOMENTS.is_file():
        moments = json.loads(MOMENTS.read_text())
        source_moment_row = next(r for r in moments["rows"] if r["twist"] == fixture["twist"])
        for key, value in fixture_row.items():
            if source_moment_row.get(key) != value:
                raise AssertionError(f"coefficient row field {key} differs from pinned moments")
    if ARITHMETIC.is_file():
        arithmetic = json.loads(ARITHMETIC.read_text())
        source_sector = next(s for s in arithmetic["sectors"] if s["mask"] == fixture["mask"])
        for key, value in fixture["sector"].items():
            if source_sector.get(key) != value:
                raise AssertionError(f"coefficient sector field {key} differs from pinned arithmetic")
    fixture["source_mode"] = "full research tables verified" if all(
        p.is_file() for p in (AFE_RECORD, MOMENTS, ARITHMETIC)) else "compact source-hash-bound fixture"
    return fixture, row


def load_coefficients(row: dict[str, object], sector: dict[str, object], nmax: int) -> list[int]:
    if sha(COEFFICIENT_CHECKER) != SOURCE_HASHES["numerics_hecke_coeff_check.py"]:
        raise AssertionError("independent coefficient checker hash changed")
    spec = importlib.util.spec_from_file_location("pinned_independent_hecke", COEFFICIENT_CHECKER)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load the pinned independent coefficient checker")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    complex_coefficients = module.rank2_first(row, sector, nmax)
    if any(im != 0 for _, im in complex_coefficients):
        raise AssertionError("the selected quadratic coefficients are unexpectedly nonreal")
    coefficients = [int(re) for re, _ in complex_coefficients]
    full = [(0, 0), (1, 0), *[(int(re), int(im)) for re, im in complex_coefficients[1:]]]
    actual = hashlib.sha256(json.dumps(full).encode()).hexdigest()
    if actual != row["signed_coefficients_sha256"]:
        raise AssertionError("recomputed complete coefficient vector hash mismatch")
    return coefficients


def quadratic_tail_bounds(s: arb, q: int, nmax: int) -> tuple[arb, arb]:
    """Bound both tails using the direct integral kernels and d2(n)<=2sqrt(n)."""
    t = 2 * arb.pi() / arb(q).sqrt()
    delta = s - 1
    m = nmax + 1
    x0 = t * m
    if not (x0 > delta and t > 0):
        raise AssertionError("elementary exponential tail requires tn > sigma-1")
    prefactor = t**s / s.gamma()
    geometric = 1 / (1 - (-t).exp())
    exp_start = (-x0).exp()
    sqrt_m = arb(m).sqrt()
    # I_s(x)<=exp(-x)/(x-delta); I_(1-s)(x)<=exp(-x)/x.
    primary = prefactor * 2 * exp_start * geometric / (
        t * sqrt_m * (1 - delta / x0))
    dual = prefactor * 2 * exp_start * geometric / (t * sqrt_m)
    return primary, dual


def main() -> None:
    if not __debug__:
        raise RuntimeError("Python assertions are required")
    fixture, printed = source_rows({})
    ctx.prec = 256
    s_fraction = Q(fixture["sigma"])
    s = arb(s_fraction.numerator) / s_fraction.denominator
    q, nmax = int(fixture["row"]["conductor"]), int(fixture["row"]["N"])
    coeff = load_coefficients(fixture["row"], fixture["sector"], nmax)
    t = 2 * arb.pi() / arb(q).sqrt()
    delta = s - 1
    prefactor = t**s / s.gamma()

    # The Mellin transform of Gamma(s+z)/Gamma(s) reduces in degree two to
    # I_b(x)=integral_1^infinity u^(b-1) exp(-x*u) du=E_(1-b)(x).
    # Arb's generalized exponential integral encloses each weight directly.
    primary_sum = arb(0)
    dual_sum = arb(0)
    for n, a_n in enumerate(coeff, start=1):
        x = t * n
        primary_sum += a_n * x.expint(1 - s)
        dual_sum += a_n * x.expint(s)
    primary = prefactor * primary_sum
    dual = prefactor * dual_sum
    source_a = interval_from_enclosure(fixture["printed_afe"]["A_finite"]["real"])
    source_b = interval_from_enclosure(fixture["printed_afe"]["B_finite"]["real"])
    finite_intervals_overlap = (
        primary.lower() <= source_a.upper() and source_a.lower() <= primary.upper()
        and dual.lower() <= source_b.upper() and source_b.lower() <= dual.upper())
    if not finite_intervals_overlap:
        raise AssertionError("direct expint finite sums do not overlap the printed AFE finite sums")
    primary_tail, dual_tail = quadratic_tail_bounds(s, q, nmax)
    l_bound = abs(primary).upper() + abs(dual).upper() + primary_tail.upper() + dual_tail.upper()

    bad_multiplier = arb(1)
    for ptext, polynomial in fixture["row"]["bad_euler_denominators"].items():
        z = (-(s * arb(int(ptext)).log())).exp()
        factor = arb(0)
        for re, im in reversed(polynomial):
            if int(im) != 0:
                raise AssertionError(f"bad local factor at p={ptext} is nonreal")
            factor = factor * z + int(re)
        if not factor > 0:
            raise AssertionError(f"bad Euler denominator is not positive at p={ptext}")
        bad_multiplier *= factor

    removed_upper = (l_bound * bad_multiplier.upper()).upper()
    log_upper = removed_upper.log().upper()
    printed_upper = endpoint(fixture["printed_afe"]["log_abs_L_S_upper"])
    comparison = bool(log_upper <= printed_upper)
    result = {
        "status": "PASS independent direct-kernel upper" if comparison else "computed upper exceeds printed allowance",
        "sigma": str(s_fraction), "mask": 1586, "twist": -1, "degree": 2,
        "conductor": q, "N": nmax, "precision_bits": 256,
        "python_flint_version": flint.__version__, "flint_version": flint.__FLINT_VERSION__,
        "source_mode": fixture["source_mode"],
        "coefficient_vector_sha256": fixture["row"]["signed_coefficients_sha256"],
        "primary_finite": enc(primary), "dual_finite": enc(dual),
        "finite_intervals_overlap_printed": bool(finite_intervals_overlap),
        "primary_tail_upper": enc(primary_tail.upper()), "dual_tail_upper": enc(dual_tail.upper()),
        "L_upper": enc(l_bound), "bad_multiplier_upper": enc(bad_multiplier.upper()),
        "log_L_S_upper": enc(log_upper),
        "printed_log_L_S_upper": fixture["printed_afe"]["log_abs_L_S_upper"],
        "comparison_below_printed_allowance": comparison,
        "method": "direct Arb expint weights plus elementary d2(n)<=2sqrt(n) exponential tail bounds",
        "scope": "phase-free AFE bound conditional on the row identity, conductor, bad factors, unit-modulus root number, and |a_n|<=d2(n) for all n",
    }
    print(json.dumps(result, indent=2))
    if not comparison:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
