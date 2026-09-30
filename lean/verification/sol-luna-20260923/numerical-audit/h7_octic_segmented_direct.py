#!/usr/bin/env python3
"""Independent segmented moment replay of H7 mask 1824, twist +1.

The default pilot mode checks a prefix of frozen bins. Use --full for all
360,720,360 integers only after allocating the guarded numerical slot.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import shlex
import subprocess
import tempfile
import time
from copy import deepcopy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
RESEARCH = ROOT / "publication/nonabelian-dyadic-lower-bound/research"
ARITHMETIC = RESEARCH / "octic-arithmetic-h7-274.json"
FROZEN_MOMENTS = RESEARCH / "h7-octic-moments-1824.json"
FROZEN_MOMENTS_SOURCE = RESEARCH / "h7-octic-moments.py"
SPARSE_SOURCE = RESEARCH / "octic-sparse-moments.cpp"
TAIL_SOURCE = RESEARCH / "octic-sparse-tail.py"
SEGMENTED_SOURCE = Path(__file__).with_name("h7_octic_segmented.cpp")
OUTPUT = Path(__file__).with_name("h7_octic_segmented_direct.json")
EXPECTED_HASHES = {
    ARITHMETIC.name: "2c8d752f6206b6793b37d91ca9ad343b6c3c4ff92f61fed9ade9e307f0013836",
    FROZEN_MOMENTS.name: "e61657ff8a8d112f1ac76941264bc74b98a2f30b8ed0d3c0fbf953a21b0f128d",
    FROZEN_MOMENTS_SOURCE.name: "429283aa8a909d554438da03c7c1edb6a4d62309809c4d0366c49ce9402d5e2c",
    SPARSE_SOURCE.name: "e886396848f72df09a78d3124de6cb1f08056dbdac644b630adf1354404bd755",
    TAIL_SOURCE.name: "293ebc05500c0c8557f8bc76e3c8fd3b0b3857b440e3648866288ce45cf20e85",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_moments_module():
    spec = importlib.util.spec_from_file_location("frozen_octic_moment_helpers", FROZEN_MOMENTS_SOURCE)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def row_bins_text(row: dict, selected_bins: list[dict], cutoff: int) -> str:
    lines = [
        "JOINT_AFE_BINS_V1",
        "degree 20",
        "multiplier 1",
        "conductors 1",
        f"conductor {row['conductor']} {cutoff} {len(selected_bins)}",
    ]
    for b in selected_bins:
        lines.append(f"bin {b['index']} {b['lo']} {b['hi']} {b['midpoint']}")
    lines += ["end_conductor", "END", ""]
    return "\n".join(lines)


def source_hashes() -> dict[str, str]:
    paths = (Path(__file__), ARITHMETIC, FROZEN_MOMENTS, FROZEN_MOMENTS_SOURCE,
             SPARSE_SOURCE, TAIL_SOURCE, SEGMENTED_SOURCE)
    return {str(path.relative_to(ROOT)): sha256(path) for path in paths}


def compile_core(target: Path) -> tuple[list[str], subprocess.CompletedProcess[str]]:
    cmd = shlex.split(os.environ.get("CXX", "g++")) + [
        "-std=c++17", "-O3", *shlex.split(os.environ.get("CPPFLAGS", "")),
        str(SEGMENTED_SOURCE), *shlex.split(os.environ.get("MOMENT_LDFLAGS", "-lgmpxx -lgmp")),
        "-o", str(target),
    ]
    completed = subprocess.run(cmd, check=True, capture_output=True, text=True)
    return cmd, completed


def main() -> None:
    if not __debug__:
        raise RuntimeError("This checker requires Python assertions; do not run with python -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="all frozen bins through N=360720360")
    parser.add_argument("--pilot-bins", type=int, default=256, help="pilot prefix length; ignored with --full")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    started = time.monotonic()

    for path in (ARITHMETIC, FROZEN_MOMENTS, FROZEN_MOMENTS_SOURCE, SPARSE_SOURCE, TAIL_SOURCE):
        assert sha256(path) == EXPECTED_HASHES[path.name], (str(path), sha256(path))
    arithmetic = json.loads(ARITHMETIC.read_text())
    sector = deepcopy(next(s for s in arithmetic["sectors"] if s["mask"] == 1824))
    assert len(sector["rows"]) == 2
    row = next(r for r in sector["rows"] if r["twist"] == 1)
    assert row["conductor"] == 208190684989647360000
    assert row["gamma"] == [0, 0, 0, 0, 1, 1, 1, 1] and row["root_number"] == 1
    assert row["quartic_exponent"] == 0 and row["factor_multiplicity"] == 1
    sector["rows"] = [row]

    frozen_sector = json.loads(FROZEN_MOMENTS.read_text())
    assert frozen_sector["mask"] == 1824 and frozen_sector["degree"] == 20
    reference = next(r for r in frozen_sector["rows"] if r["twist"] == 1)
    assert reference["N"] == 360720360 and reference["nonzero_coefficients"] == 548127
    assert len(reference["bins"]) == 544
    for key in ("conductor", "gamma", "root_number", "bad_euler_denominators", "first128_complex_coefficients"):
        assert reference[key] == row[key], ("frozen/arithmetic row binding", key)
    if args.full:
        selected_bins = reference["bins"]
        cutoff = reference["N"]
        mode = "full"
    else:
        assert 1 <= args.pilot_bins <= len(reference["bins"])
        selected_bins = reference["bins"][:args.pilot_bins]
        cutoff = selected_bins[-1]["hi"]
        assert cutoff >= 128
        mode = "pilot"

    moments = load_moments_module()
    metadata = moments.metadata(sector)
    bin_layout = row_bins_text(row, selected_bins, cutoff)
    with tempfile.TemporaryDirectory(prefix="h7-octic-segmented-") as tmp_name:
        tmp = Path(tmp_name)
        (tmp / "metadata.txt").write_text(metadata)
        (tmp / "bins.txt").write_text(bin_layout)
        binary = tmp / "h7_octic_segmented"
        compile_command = []
        try:
            compile_command, compile_result = compile_core(binary)
        except subprocess.CalledProcessError as exc:
            failure = {
                "status": "FAIL segmented C++ compile",
                "mode": mode,
                "sector_mask": 1824,
                "twist": 1,
                "conductor": row["conductor"],
                "N_checked": cutoff,
                "bins_requested": len(selected_bins),
                "compile_command": exc.cmd,
                "returncode": exc.returncode,
                "stdout": exc.stdout,
                "stderr": exc.stderr,
                "source_sha256": source_hashes(),
                "metadata_sha256": hashlib.sha256(metadata.encode()).hexdigest(),
                "bin_layout_sha256": hashlib.sha256(bin_layout.encode()).hexdigest(),
            }
            args.output.write_text(json.dumps(failure, indent=2) + "\n")
            raise
        binary_sha256 = sha256(binary)
        try:
            proc = subprocess.run([str(binary), str(tmp / "metadata.txt"), str(tmp / "bins.txt")],
                                  capture_output=True, text=True, check=True)
        except subprocess.CalledProcessError as exc:
            failure = {
                "status": "FAIL segmented C++ process",
                "mode": mode,
                "sector_mask": 1824,
                "twist": 1,
                "conductor": row["conductor"],
                "N_checked": cutoff,
                "bins_requested": len(selected_bins),
                "compile_command": compile_command,
                "binary_sha256": binary_sha256,
                "returncode": exc.returncode,
                "stdout_sha256": hashlib.sha256((exc.stdout or "").encode()).hexdigest(),
                "stdout_prefix": (exc.stdout or "")[:10000],
                "stderr": exc.stderr,
                "compiler_stdout": compile_result.stdout,
                "compiler_stderr": compile_result.stderr,
                "source_sha256": source_hashes(),
                "metadata_sha256": hashlib.sha256(metadata.encode()).hexdigest(),
                "bin_layout_sha256": hashlib.sha256(bin_layout.encode()).hexdigest(),
            }
            args.output.write_text(json.dumps(failure, indent=2) + "\n")
            raise

    try:
        replay = moments.parse(proc.stdout, sector)
    except Exception as exc:
        failure = {
            "status": "FAIL segmented output parse",
            "mode": mode,
            "sector_mask": 1824,
            "twist": 1,
            "conductor": row["conductor"],
            "N_checked": cutoff,
            "bins_requested": len(selected_bins),
            "parse_exception": f"{type(exc).__name__}: {exc}",
            "binary_sha256": binary_sha256,
            "compile_command": compile_command,
            "compiler_stdout": compile_result.stdout,
            "compiler_stderr": compile_result.stderr,
            "raw_output_sha256": hashlib.sha256(proc.stdout.encode()).hexdigest(),
            "raw_output_prefix": proc.stdout[:10000],
            "stderr": proc.stderr,
            "source_sha256": source_hashes(),
            "metadata_sha256": hashlib.sha256(metadata.encode()).hexdigest(),
            "bin_layout_sha256": hashlib.sha256(bin_layout.encode()).hexdigest(),
        }
        args.output.write_text(json.dumps(failure, indent=2) + "\n")
        raise
    got = replay["rows"][0]
    mismatches = []
    if not (got["twist"] == 1 and got["conductor"] == row["conductor"]):
        mismatches.append({"check": "row identity", "direct": [got["twist"], got["conductor"]], "expected": [1, row["conductor"]]})
    if got["N"] != cutoff:
        mismatches.append({"check": "cutoff", "direct": got["N"], "expected": cutoff})
    frozen_count = sum(b["count"] for b in selected_bins)
    if got["nonzero_coefficients"] != frozen_count:
        mismatches.append({"check": "nonzero coefficient count", "direct": got["nonzero_coefficients"], "expected": frozen_count})
    compare_fields = ("index", "lo", "hi", "midpoint", "mass", "count", "moments", "imag_moments", "absolute_moments")
    for actual, expected in zip(got["bins"], selected_bins):
        for key in compare_fields:
            if actual[key] != expected[key] and len(mismatches) < 50:
                mismatches.append({"check": key, "bin": expected["index"], "direct": actual[key], "expected": expected[key]})
        if not (len(actual["moments"]) == len(actual["absolute_moments"]) == 21):
            mismatches.append({"check": "moment vector length", "bin": expected["index"]})
    if len(got["bins"]) != len(selected_bins):
        mismatches.append({"check": "bin count", "direct": len(got["bins"]), "expected": len(selected_bins)})
    if got["first128_complex_coefficients"] != row["first128_complex_coefficients"]:
        mismatches.append({"check": "first128 coefficients", "direct": got["first128_complex_coefficients"],
                           "expected": row["first128_complex_coefficients"]})

    result = {
        "status": (f"PASS {mode} independent segmented coefficient and exact moment replay"
                   if not mismatches else f"FAIL {mode} independent segmented coefficient/moment comparison"),
        "scope": "one actual H7 mixed-octic row; no AFE endpoint or global H claim",
        "mode": mode,
        "sector_mask": 1824,
        "twist": 1,
        "degree": 8,
        "gamma": row["gamma"],
        "root_number": row["root_number"],
        "conductor": row["conductor"],
        "sigma": "6001/6000",
        "N_checked": cutoff,
        "frozen_full_N": reference["N"],
        "bins_checked": len(selected_bins),
        "full_bins": len(reference["bins"]),
        "nonzero_coefficients_checked": got["nonzero_coefficients"],
        "frozen_full_nonzero_coefficients": reference["nonzero_coefficients"],
        "moment_degree": 20,
        "exact_signed_and_absolute_moments_per_bin": 21,
        "all_bad_euler_denominators_bound_to_arithmetic_row": True,
        "first128_coefficients_match": not any(m["check"] == "first128 coefficients" for m in mismatches),
        "all_selected_bins_match": not any(m["check"] not in ("first128 coefficients", "row identity", "cutoff", "nonzero coefficient count") for m in mismatches),
        "mismatches": mismatches,
        "source_sha256": source_hashes(),
        "compile_command": compile_command,
        "compiler_stdout": compile_result.stdout,
        "compiler_stderr": compile_result.stderr,
        "binary_sha256": binary_sha256,
        "metadata_sha256": hashlib.sha256(metadata.encode()).hexdigest(),
        "bin_layout_sha256": hashlib.sha256(bin_layout.encode()).hexdigest(),
        "raw_output_sha256": hashlib.sha256(proc.stdout.encode()).hexdigest(),
        "stderr": proc.stderr,
        "seconds_including_python_and_core_compile": time.monotonic() - started,
        "method": "blockwise prime-factor remainder scan with one-byte twisted prime-code table; no dense coefficient vector; exact GMP bin accumulation; separate from the frozen producer's recursive support enumerator",
        "assumptions_and_limits": [
            "The arithmetic row and its bad-prime Euler factors are hash-pinned inputs; this checker does not prove the representation identification, conductor, gamma/root data, or functional equation.",
            "The replay checks finite coefficients/moments only and does not prove the global |a_n|<=d_8(n) bound or H.",
            "The streaming prime-code calculation uses the pinned source's exact arithmetic helpers and matching prime-classification formulas; segmented coefficient factorization and full bin accumulation are separate.",
            "The frozen bin fixture is the comparison target and is not independently regenerated here.",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"], "bins", result["bins_checked"], "N", cutoff, "nonzero", got["nonzero_coefficients"])
    if mismatches:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
