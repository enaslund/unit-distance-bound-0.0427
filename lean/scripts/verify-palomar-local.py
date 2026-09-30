#!/usr/bin/env python3
"""Run pinned Palomar execution code on an unpublished, hash-checked archive.

Local preparation replaces ONLY remote submission intake. The imported
verifier's execute function, dependency authentication/download, confinement,
canonical Challenge build, and Comparator invocation are unmodified.
This creates no Palomar submission and is not an official mechanical report.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import tomllib

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
POLICY_PIN = "3561d237dcc4b28482558ad28a64d767d7cc8615"


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            h.update(chunk)
    return h.hexdigest()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def now():
    return datetime.now(timezone.utc).isoformat()


def git(tree, *args):
    return subprocess.check_output(
        ["git", "-c", "core.hooksPath=/dev/null", "-C", str(tree), *args],
        text=True).strip()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--archive", type=Path, required=True)
    p.add_argument("--work-dir", type=Path, required=True)
    p.add_argument("--report", type=Path, required=True)
    p.add_argument("--policy-tree", type=Path, required=True)
    for tool in ("comparator", "lean4export", "landrun", "nanoda"):
        p.add_argument("--" + tool, type=Path, required=True)
    p.add_argument("--licensee", type=Path,
                   help="Bundler executable using the pinned policy Gemfile.lock")
    p.add_argument("--execution-budget-seconds", type=int, default=19800)
    args = p.parse_args()
    work, output, policy = (x.resolve() for x in
                            (args.work_dir, args.report, args.policy_tree))
    archive = args.archive.resolve(strict=True)
    if work.exists() or output.exists():
        p.error("Use new work/report paths; earlier evidence is never overwritten")
    if not 1 <= args.execution_budget_seconds <= 19800:
        p.error("Execution budget must be between 1 and the standard 19800 seconds")
    if git(policy, "rev-parse", "HEAD") != POLICY_PIN:
        p.error("Wrong PalomarSubmission revision")
    if git(policy, "status", "--porcelain", "--untracked-files=no"):
        p.error("Pinned verifier has tracked source modifications")
    sys.path.insert(0, str(policy))
    from scripts import verify_submission as verifier
    from scripts.submission_contract import load_formalization_metadata, normalized_provenance
    from scripts.verification_profile import check_host

    profile = verifier.VERIFICATION_PROFILE
    if profile["id"] != "palomar-standard-v1":
        p.error("This runner records only the standard profile")
    work.mkdir(parents=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    source = work / "source"
    log = output.with_suffix(".log")
    started = time.monotonic()
    receipt = {
        "schema": "unit-distance-local-palomar-execution-v1",
        "scope": "Unpublished local archive; unmodified pinned Palomar execution code. "
                 "Local preparation is not remote intake. No official report or editorial review.",
        "started_at": now(), "state": "running", "passed": False,
        "archive_sha256": digest(archive), "archive": str(archive),
        "palomar_submission_commit": POLICY_PIN,
        "work_directory": str(work), "execution_log": str(log),
        "remote_submission": False, "official_palomar_report": False,
        "license_detector_performed": False,
        "policy_files": {str(path.relative_to(policy)): digest(path) for path in
                         sorted(policy.glob("scripts/*.py"))},
        "tools": {name: {"path": str(getattr(args, name).resolve(strict=True)),
                         "sha256": digest(getattr(args, name))}
                  for name in ("comparator", "lean4export", "landrun", "nanoda")},
    }
    save(output, receipt)
    spec = importlib.util.spec_from_file_location("zeta_archive_verifier",
                                                   ROOT / "scripts/verify-zeta-candidate.py")
    archive_verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(archive_verifier)
    try:
        snapshot = archive_verifier.extract(archive, source)
        receipt["source_snapshot_sha256"] = digest(source / "SOURCE_SNAPSHOT.json")
        receipt["project_build_outputs_initially_absent"] = not (source / ".lake").exists()
        if not receipt["project_build_outputs_initially_absent"]:
            raise ValueError("Archive unexpectedly includes build state")
        receipt["observed_host"] = check_host(profile, work)
        metadata = load_formalization_metadata(source / "formalization.yaml")
        receipt["metadata_contract_passed"] = True
        normalized_provenance(metadata)
        lakefiles = [source / name for name in ("lakefile.toml", "lakefile.lean")
                     if (source / name).exists()]
        if len(lakefiles) != 1 or lakefiles[0].is_symlink():
            raise ValueError("Expected one regular Lakefile")
        if lakefiles[0].name == "lakefile.toml":
            tomllib.loads(lakefiles[0].read_text())
        config_path = source / "comparator-zeta.json"
        config = verifier.load_comparator_config(config_path)
        license_path = verifier.repository_license_file(source)
        receipt["license"] = {"file": license_path.name, "sha256": digest(license_path),
                              "declared": metadata["project"]["license"]}
        if args.licensee:
            detected = verifier.detect_spdx_identifier(license_path, args.licensee.resolve())
            receipt["license"]["detected"] = detected
            receipt["license_detector_performed"] = True
            if detected != metadata["project"]["license"]:
                raise ValueError("License declaration and detector disagree")
        toolchain = (source / "lean-toolchain").read_text().strip()
        verifier.supported_toolchain(toolchain)
        lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
        version = toolchain.split(":")[-1].removeprefix("v")
        if f"version {version}," not in lean_version:
            raise ValueError("The Lean executable does not match the submitted toolchain")
        receipt["lean_version"] = lean_version
        packages = verifier.manifest_packages(source)
        receipt["manifest_packages"] = packages
        git(source, "init", "--quiet")
        git(source, "add", ".")
        git(source, "-c", "user.name=Local verification", "-c",
            "user.email=local-verification@invalid", "commit", "--quiet", "--no-gpg-sign",
            "-m", "Local verification snapshot; not published")
        verifier.validate_preservable_git_checkout(source, "local source archive")
        verifier.reject_committed_build_artifacts(source)
        size = verifier.tree_size(source)
        if size > verifier.MAX_SOURCE_BYTES:
            raise ValueError("Source exceeds the Palomar size limit")
        mechanical = work / "local-execution.json"
        initial = {
            "schema_version": 1, "status": "pending", "stage": "locally-prepared",
            "phase": "local-preparation", "checked_at": now(), "errors": [], "warnings": [],
            "local_only": True, "official_palomar_report": False,
            "verification_profile": verifier.verification_profile_evidence(),
            "source": {"kind": "unpublished-local-archive", "commit": git(source, "rev-parse", "HEAD"),
                       "archive_sha256": digest(archive), "bytes": size},
            "lakefile": {"path": lakefiles[0].name, "sha256": digest(lakefiles[0])},
            "lean_toolchain": toolchain, "lean_toolchain_path": "lean-toolchain",
            "challenge": {"module": config["challenge_module"]},
            "solution": {"module": config["solution_module"]},
            "comparator": {"path": config_path.name, "sha256": digest(config_path), **config},
        }
        save(mechanical, initial)
        receipt["local_execution_report"] = str(mechanical)
        receipt["source_commit"] = initial["source"]["commit"]
        receipt["source_bytes"] = size
        pins = profile["trusted_tools"]
        command = [sys.executable, str(policy / "scripts/verify_submission.py"), "execute",
                   "--work-dir", str(work), "--output", str(mechanical),
                   "--workflow-url", "local-only:not-an-official-palomar-report",
                   "--execution-budget-seconds", str(args.execution_budget_seconds)]
        for name in ("comparator", "lean4export", "landrun", "nanoda"):
            command.extend(["--" + name, str(getattr(args, name).resolve(strict=True))])
        for name in ("comparator", "landrun", "nanoda"):
            command.extend(["--" + name + "-commit", pins[name + "_commit"]])
        receipt["command"] = command
        receipt["execution_budget_seconds"] = args.execution_budget_seconds
        save(output, receipt)
        env = dict(os.environ)
        for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "PALOMAR_JOB_STARTED_AT",
                     "MATHLIB_CACHE_DIR", "MATHLIB_CACHE_GET_URL", "LAKE_PKG_URL_MAP"):
            env.pop(name, None)
        # Work is on disk, outside /tmp (the verifier uses PrivateTmp).
        env["TMPDIR"] = str(work / "tmp")
        (work / "tmp").mkdir()
        print("Starting pinned local execution; log " + str(log), flush=True)
        with log.open("x") as stream:
            result = subprocess.run(command, env=env, stdout=stream, stderr=subprocess.STDOUT)
        receipt["execution_exit_code"] = result.returncode
        receipt["execution_report"] = json.loads(mechanical.read_text())
        archive_verifier.check_sources(source, snapshot)
        receipt["sources_unchanged"] = True
        for name, tool in receipt["tools"].items():
            if digest(tool["path"]) != tool["sha256"]:
                raise ValueError("Tool changed during execution: " + name)
        receipt["tools_unchanged"] = True
        if result.returncode != 0 or receipt["execution_report"]["status"] != "pass":
            raise RuntimeError("Pinned execution did not pass; see local execution report")
        receipt.update(state="passed", passed=True)
    except Exception as error:
        receipt.update(state="failed", error=f"{type(error).__name__}: {error}")
        mechanical = work / "local-execution.json"
        if mechanical.is_file():
            receipt["execution_report"] = json.loads(mechanical.read_text())
    finally:
        if log.is_file():
            receipt["execution_log_sha256"] = digest(log)
        receipt.update(finished_at=now(), seconds=round(time.monotonic() - started, 3))
        save(output, receipt)
    print(json.dumps({key: receipt[key] for key in ("state", "passed", "seconds")}), flush=True)
    return 0 if receipt["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
