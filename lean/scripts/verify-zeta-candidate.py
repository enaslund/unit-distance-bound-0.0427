#!/usr/bin/env python3
"""Validate a selected archive, then rebuild its project proofs from source.

Pinned public dependency artifacts may be reused. No project proof artifact
is copied. Comparator and independent kernel replay are separate checks.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parent.parent


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            h.update(chunk)
    return h.hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def extract(archive, destination):
    entries = {}
    previous = ""
    with tarfile.open(archive, "r:gz") as stream:
        for member in stream:
            name = PurePosixPath(member.name)
            if (not member.isfile() or name.is_absolute() or ".." in name.parts
                    or len(name.parts) < 2 or name.parts[0] != "unit-distance-zeta"
                    or member.name <= previous):
                raise ValueError(f"Invalid archive member: {member.name}")
            previous = member.name
            relative = PurePosixPath(*name.parts[1:]).as_posix()
            expected_mode = 0o755 if relative.startswith("scripts/") else 0o644
            if (member.mode != expected_mode or member.mtime != 0 or member.uid != 0
                    or member.gid != 0 or member.uname or member.gname):
                raise ValueError(f"Noncanonical archive attributes: {member.name}")
            data = stream.extractfile(member).read()
            if len(data) != member.size:
                raise ValueError(f"Truncated member: {member.name}")
            entries[relative] = data
    snapshot = json.loads(entries.pop("SOURCE_SNAPSHOT.json"))
    observed = {name: {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
                for name, data in entries.items()}
    if observed != snapshot:
        raise ValueError("Archive source manifest mismatch")
    if sum(map(len, entries.values())) > 500 * 1024 * 1024:
        raise ValueError("Source size exceeds inspected policy limit")
    for name, data in entries.items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        path.chmod(0o755 if name.startswith("scripts/") else 0o644)
    write_json(destination / "SOURCE_SNAPSHOT.json", snapshot)
    return snapshot


def check_sources(destination, snapshot):
    for name, expected in snapshot.items():
        path = destination / name
        if path.is_symlink() or not path.is_file() or digest(path) != expected["sha256"]:
            raise ValueError(f"Captured source changed: {name}")


def selected_file(destination, value):
    """Resolve an explicitly selected regular archive member, never a host path."""
    relative = PurePosixPath(value)
    if (relative.is_absolute() or not relative.parts or ".." in relative.parts
            or str(relative) != value or "\\" in value):
        raise ValueError(f"Noncanonical selected archive path: {value}")
    path = destination / value
    if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(destination.resolve()):
        raise ValueError(f"Missing regular selected archive file: {value}")
    return path


def dependencies(cache, manifest):
    result = []
    for package in json.loads(manifest.read_text())["packages"]:
        if package["type"] != "git" or len(package["rev"]) != 40:
            raise ValueError("Expected public Git dependency pinned to a full SHA")
        tree = cache / package["name"]
        revision = subprocess.check_output(["git", "-C", str(tree), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(tree), "status", "--porcelain", "--untracked-files=no"], text=True)
        if revision != package["rev"] or dirty.strip():
            raise ValueError(f"Dependency revision/source mismatch: {package['name']}")
        result.append({"name": package["name"], "revision": revision, "url": package["url"]})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--work-dir", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--comparator-config", default="comparator-zeta.json",
                        help="selected comparator path inside the archive")
    parser.add_argument("--exporter", default="scripts/export-zeta-candidate.py",
                        help="sealed deterministic exporter path inside the archive")
    parser.add_argument("--audit-script", default="verification/ZetaAudit.lean",
                        help="imported audit path for the optional fresh-build mode")
    parser.add_argument("--policy-tree", type=Path,
                        default=ROOT / ".cache/upstream/PalomarSubmission-current-20260923-pinned",
                        help="exact PalomarSubmission checkout for the archive metadata contract")
    parser.add_argument("--policy-revision", required=True,
                        help="exact PalomarSubmission commit expected by check-metadata.py")
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--timeout", type=int, default=19800)
    args = parser.parse_args()
    if args.threads < 1 or args.timeout < 1:
        parser.error("Positive threads and timeout required")
    work, report = args.work_dir.resolve(), args.report.resolve()
    if work.exists() or report.exists():
        raise SystemExit("Refusing to overwrite earlier verification work or evidence")
    work.mkdir(parents=True)
    destination = work / "unit-distance-zeta"
    started = time.monotonic()
    result = {"started_at": now(), "passed": False, "state": "running", "checks": [],
              "archive": str(args.archive.resolve()), "archive_sha256": digest(args.archive),
              "policy_tree": str(args.policy_tree.resolve()),
              "policy_revision": args.policy_revision,
              "work_directory": str(work), "selected_configuration": args.comparator_config,
              "selected_exporter": args.exporter, "selected_audit_script": args.audit_script,
              "mode": "archive-only" if args.check_only else "fresh-project-source-build",
              "timeout_seconds": args.timeout, "threads": args.threads,
              "scope": (
                  "Local source archive and pinned metadata contract only. No Lean build, axiom audit, or independent kernel replay."
                  if args.check_only else
                  "Local source archive, pinned metadata contract, fresh project proof build and imported axiom audit. Independent kernel replay is separate."
              ) + " The fixed zeta inequality is not verified.",
              "remote_submission": False}
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        env.pop(key, None)
    env.update(PATH=str(ROOT / ".toolchain/bin") + os.pathsep + env.get("PATH", ""),
               LEAN_NUM_THREADS=str(args.threads), LAKE_NO_CACHE="true", LAKE_ARTIFACT_CACHE="false",
               TMPDIR=str(work / "tmp"), PYTHONPATH=str(ROOT / ".cache/policy-python"))
    (work / "tmp").mkdir()

    def run(command, label):
        remaining = args.timeout - int(time.monotonic() - started)
        if remaining <= 0:
            raise TimeoutError("Verification execution budget reached")
        log = report.parent / (report.stem + "-" + label + ".log")
        entry = {"command": command, "log": str(log), "started_at": now(), "state": "running"}
        result["checks"].append(entry)
        write_json(report, result)
        print(f"Starting {label}: {' '.join(command)}", flush=True)
        t = time.monotonic()
        with log.open("x") as output:
            process = subprocess.Popen(["timeout", "--kill-after=30s", str(remaining), *command],
                                       cwd=destination, env=env, stdout=output, stderr=subprocess.STDOUT)
            entry["pid"] = process.pid
            write_json(report, result)
            code = process.wait()
        entry.update(exit_code=code, seconds=round(time.monotonic() - t, 3),
                     state="passed" if code == 0 else "failed", finished_at=now(), log_sha256=digest(log))
        write_json(report, result)
        print(f"Finished {label}: exit {code}", flush=True)
        if code != 0:
            raise RuntimeError(f"{label} failed with exit {code}")

    try:
        snapshot = extract(args.archive, destination)
        result["snapshot_sha256"] = digest(destination / "SOURCE_SNAPSHOT.json")
        selected = json.loads(selected_file(destination, args.comparator_config).read_text())
        selection = json.loads(selected_file(destination, "SELECTION.json").read_text())
        if selection.get("comparator") != args.comparator_config:
            raise ValueError("Archive selection disagrees with the requested comparator")
        if "exporter" in selection and selection["exporter"] != args.exporter:
            raise ValueError("Archive selection disagrees with the requested exporter")
        selected_modules = [selected[key] for key in ("challenge_module", "solution_module")]
        for module in selected_modules:
            selected_file(destination, module.replace(".", "/") + ".lean")
        selected_file(destination, args.exporter)
        result["selected_modules"] = selected_modules
        result["selected_theorems"] = selected["theorem_names"]
        # Re-export the sealed extraction through its included exporter.
        run([sys.executable, args.exporter, "--output", str(work / "reexport.tar.gz"),
             "--report", str(work / "reexport.json")], "determinism")
        if digest(work / "reexport.tar.gz") != result["archive_sha256"]:
            raise ValueError("Sealed source re-export differs byte-for-byte")
        result["deterministic_archive"] = True
        run([sys.executable, "scripts/check-metadata.py", "--policy-tree",
             str(args.policy_tree.resolve()), "--revision", args.policy_revision],
            "metadata")
        if not args.check_only:
            selected_file(destination, args.audit_script)
            cache = (ROOT / ".lake/packages").resolve(strict=True)
            result["dependencies_before"] = dependencies(cache, destination / "lake-manifest.json")
            if (destination / ".lake").exists():
                raise ValueError("Project artifacts unexpectedly present before fresh build")
            (destination / ".lake").mkdir()
            (destination / ".lake/packages").symlink_to(cache, target_is_directory=True)
            result["project_artifacts_initially_absent"] = True
            result["public_dependency_artifacts_reused"] = True
            result["dependency_cache"] = str(cache)
            result["lean_version"] = subprocess.check_output(["lean", "--version"], env=env, text=True).strip()
            toolchain = (destination / "lean-toolchain").read_text().strip()
            if (cache / "mathlib/lean-toolchain").read_text().strip() != toolchain:
                raise ValueError("Project and canonical Mathlib toolchains differ")
            version = toolchain.split(":")[-1].removeprefix("v")
            if f"version {version}," not in result["lean_version"]:
                raise ValueError("Wrong Lean executable version")
            run(["lake", f"-Kjobs={args.threads}", "build",
                 *[f"+{module}:olean" for module in selected_modules], "+AuditSupport:olean"], "build")
            run(["lake", "env", "lean", "-DstderrAsMessages=false", args.audit_script], "axioms")
            result["dependencies_after"] = dependencies(cache, destination / "lake-manifest.json")
            if result["dependencies_after"] != result["dependencies_before"]:
                raise ValueError("Dependency pins changed during verification")
        check_sources(destination, snapshot)
        result["sources_unchanged"] = True
        result["passed"] = True
        result["state"] = "passed"
    except Exception as error:
        result.update(state="failed", error=f"{type(error).__name__}: {error}")
    finally:
        result.update(finished_at=now(), seconds=round(time.monotonic() - started, 3))
        write_json(report, result)
    print(json.dumps({k: v for k, v in result.items() if k != "checks"}, indent=2), flush=True)
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
