#!/usr/bin/env python3
"""Run PalomarSubmission's September 25 pinned execute path on a frozen local archive.

This adapter replaces only `prepare()`'s GitHub checkout with a copy of a
hash-checked extracted archive. The pinned verifier's preparation validators
and `execute` implementation remain unchanged. The resulting report is local
evidence, not a Palomar workflow report or submission.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tomllib

PALOMAR_HEAD = "a59f25bd8a66bf6faf3a4f4260d412989c0185ea"
STANDARD_PROFILE = "palomar-standard-v1"
BWRAP_TAG = "v0.12.0"
LOCAL_REPOSITORY = "local/conditional-candidate"
LOCAL_REQUEST_ID = "local0000001"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def git(root: Path, *arguments: str) -> str:
    return subprocess.check_output(
        ["git", "-c", "core.hooksPath=/dev/null", "-C", str(root), *arguments],
        text=True,
    ).strip()


def load_archive_checker():
    source = Path(__file__).resolve().parents[2] / "scripts" / "verify-zeta-candidate.py"
    spec = importlib.util.spec_from_file_location("zeta_candidate_archive_checker", source)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load archive checker at {source}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--archive", type=Path, required=True)
    result.add_argument("--expect-sha256", required=True)
    result.add_argument("--policy-tree", type=Path, required=True,
                        help="clean PalomarSubmission checkout at the required exact commit")
    result.add_argument("--work-dir", type=Path, required=True)
    result.add_argument("--report", type=Path, required=True)
    result.add_argument("--bwrap", type=Path, required=True)
    result.add_argument("--licensee", type=Path, required=True,
                        help="pinned Bundle executable for Palomar's SPDX detector")
    result.add_argument("--execution-budget-seconds", type=int, default=19_800)
    result.add_argument("--execute", action="store_true",
                        help="continue into the expensive current verifier after preflight")
    return result


def main() -> int:
    args = parser().parse_args()
    archive = args.archive.resolve(strict=True)
    policy = args.policy_tree.resolve(strict=True)
    work = args.work_dir.resolve()
    output = args.report.resolve()
    bwrap = args.bwrap.resolve(strict=True)
    licensee = args.licensee.resolve(strict=True)

    if work.exists() or output.exists():
        raise SystemExit("Refusing to overwrite existing work or evidence")
    if not 1 <= args.execution_budget_seconds <= 19_800:
        raise SystemExit("Execution budget must be between 1 and the published 19,800 seconds")
    if len(args.expect_sha256) != 64 or any(c not in "0123456789abcdef" for c in args.expect_sha256):
        raise SystemExit("--expect-sha256 must be 64 lowercase hexadecimal characters")
    if git(policy, "rev-parse", "HEAD") != PALOMAR_HEAD:
        raise SystemExit(f"Palomar tree must be exactly {PALOMAR_HEAD}")
    if git(policy, "status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("Palomar policy tree must be clean")
    actual_archive_hash = sha256(archive)
    if actual_archive_hash != args.expect_sha256:
        raise SystemExit(f"Archive SHA-256 mismatch: {actual_archive_hash}")

    # Set this before importing the current verifier: its profile is loaded at
    # module import time. The standard profile is the public predictive-workflow
    # profile, even though the operator catalogue's default is Namespace.
    os.environ["PALOMAR_EXECUTION_PROFILE"] = STANDARD_PROFILE
    sys.path.insert(0, str(policy))
    from scripts import submission_contract, verification_profile, verify_submission

    selected_profile = verification_profile.load_profile(STANDARD_PROFILE)
    if selected_profile["id"] != STANDARD_PROFILE:
        raise RuntimeError("current verifier did not select the standard profile")

    work.mkdir(parents=True)
    source = work / "source"
    started = datetime.now(timezone.utc).isoformat()
    receipt: dict[str, object] = {
        "schema": "palomar-current-local-execution-v1",
        "scope": (
            "Local-only execution of the pinned current Palomar verifier on an unpublished archive. "
            "This is neither an official Palomar report nor a registry submission."
        ),
        "palomar_submission_commit": PALOMAR_HEAD,
        "execution_profile": STANDARD_PROFILE,
        "archive": str(archive),
        "archive_sha256": actual_archive_hash,
        "work_directory": str(work),
        "report_path": str(output),
        "started_at": started,
        "local_only": True,
        "official_palomar_report": False,
        "remote_submission": False,
        "execute_requested": args.execute,
        "state": "running",
    }
    write_json(output, receipt)

    try:
        profile_host = verification_profile.check_host(selected_profile, work)
        receipt["observed_host"] = profile_host

        bwrap_version = subprocess.check_output([str(bwrap), "--version"], text=True).strip()
        if bwrap_version != "bubblewrap 0.12.0":
            raise RuntimeError(f"expected bubblewrap 0.12.0, got {bwrap_version!r}")
        installer = policy / "scripts" / "install_bwrap.sh"
        installer_text = installer.read_text(encoding="utf-8")
        if f'BWRAP_VERSION="{BWRAP_TAG.removeprefix("v")}"' not in installer_text:
            raise RuntimeError("current Bubblewrap installer does not pin the required release")
        bwrap_probe = subprocess.run(
            [str(bwrap), "--unshare-user", "--ro-bind", "/", "/", "--proc", "/proc",
             "--dev", "/dev", "--", "/usr/bin/true"],
            text=True, capture_output=True, check=False,
        )
        receipt["bubblewrap"] = {
            "path": str(bwrap),
            "version": bwrap_version,
            "sha256": sha256(bwrap),
            "source_tag": BWRAP_TAG,
            "installer_sha256": sha256(installer),
            "smoke_exit_code": bwrap_probe.returncode,
            "smoke_stderr": bwrap_probe.stderr[-2_000:],
        }
        if bwrap_probe.returncode:
            raise RuntimeError("Bubblewrap namespace smoke failed")

        archive_checker = load_archive_checker()
        snapshot = archive_checker.extract(archive, source)
        snapshot_file = source / "SOURCE_SNAPSHOT.json"
        archive_checker.check_sources(source, snapshot)
        receipt["source_snapshot_sha256"] = sha256(snapshot_file)
        receipt["snapshot_file_count"] = len(snapshot)

        # Commit the extracted bytes locally so current prepare/execute see the
        # real Git metadata they require. This commit is synthetic and is
        # explicitly labeled as such in the receipt.
        git(source, "init", "--quiet")
        git(source, "add", ".")
        git(source, "-c", "user.name=Local Palomar execution",
            "-c", "user.email=local-execution@invalid", "commit", "--quiet", "-m",
            "Hash-checked local archive")
        local_commit = git(source, "rev-parse", "HEAD")
        verify_submission.validate_preservable_git_checkout(source, "local archive")
        verify_submission.reject_committed_build_artifacts(source)
        source_bytes = verify_submission.tree_size(source)
        receipt["local_git_commit"] = local_commit
        receipt["local_source_bytes"] = source_bytes
        receipt["source_snapshot_verified"] = True
        write_json(output, receipt)

        # Reuse current prepare() validators and report assembly. Only its
        # immutable remote checkout is replaced, and only with this validated
        # local source at the exact synthetic local commit.
        event_path = work / "local-input.json"
        event = {"inputs": {
            "repository": LOCAL_REPOSITORY,
            "commit": local_commit,
            "request_id": LOCAL_REQUEST_ID,
            "mode": "full",
            "options": json.dumps({
                "comparator_config_path": "comparator-zeta.json",
                "authorization_relationship": "I am a responsible author or maintainer",
            }),
        }}
        event_path.write_text(json.dumps(event), encoding="utf-8")
        work_dir_for_prepare = work / "prepare-work"
        report_path_for_prepare = work / "prepared-report.json"
        original_clone = verify_submission.clone_commit

        def copy_local_archive(url: str, commit: str, destination: Path) -> None:
            if url != "https://github.com/local/conditional-candidate" or commit != local_commit:
                raise RuntimeError("prepare requested a source other than the bound local archive")
            shutil.copytree(source, destination, symlinks=True)

        verify_submission.clone_commit = copy_local_archive
        try:
            prepare_result = verify_submission.prepare(argparse.Namespace(
                event=str(event_path),
                work_dir=str(work_dir_for_prepare),
                output=str(report_path_for_prepare),
                licensee=str(licensee),
            ))
        finally:
            verify_submission.clone_commit = original_clone
        prepared = json.loads(report_path_for_prepare.read_text(encoding="utf-8"))
        receipt["prepare_exit_code"] = prepare_result
        receipt["prepare_status"] = prepared.get("status")
        receipt["prepare_errors"] = prepared.get("errors", [])
        archive_checker.check_sources(work_dir_for_prepare / "source", snapshot)
        receipt["prepared_source_snapshot_verified"] = True

        # Remove the synthetic repository URL and request id even when a
        # current intake validator reports an error.
        requested_source = prepared.get("source", {})
        prepared["source"] = {
            "kind": "unpublished-local-archive",
            "local_commit": local_commit,
            "archive_sha256": actual_archive_hash,
            "source_snapshot_sha256": receipt["source_snapshot_sha256"],
            "bytes": source_bytes,
            **({"project_path": requested_source["project_path"]}
               if requested_source.get("project_path") else {}),
        }
        prepared["submission"] = {"scope": "local-only; no Palomar submission id"}
        prepared["local_only"] = True
        prepared["official_palomar_report"] = False
        prepared["verification_profile"] = verify_submission.verification_profile_evidence()
        prepared["verification_profile"]["observed_host"] = profile_host
        write_json(report_path_for_prepare, prepared)
        metadata_path = work_dir_for_prepare / "metadata.json"
        if metadata_path.is_file():
            metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
            metadata["source"] = prepared["source"]
            metadata["submission"] = prepared["submission"]
            metadata["local_only"] = True
            metadata["official_palomar_report"] = False
            metadata["verification_profile"] = prepared["verification_profile"]
            write_json(metadata_path, metadata)
        if prepare_result != 0 or prepared.get("status") != "pending":
            raise RuntimeError("current Palomar prepare validators did not accept the local candidate")

        receipt["prepared_report_sha256"] = hashlib.sha256(
            json.dumps(prepared, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()
        local_mechanical = work / "local-execution.json"
        write_json(local_mechanical, prepared)
        receipt["execution_report"] = str(local_mechanical)
        receipt["prepared_report_status"] = prepared["status"]
        write_json(output, receipt)

        if not args.execute:
            receipt["cgroup_bootstrap"] = {
                "tested": False,
                "passed": None,
                "reason": "preparation-only mode; execute flag was not supplied",
            }
            receipt["state"] = "prepared; verifier not executed"
            receipt["finished_at"] = datetime.now(timezone.utc).isoformat()
            write_json(output, receipt)
            return 0

        # This official source probe starts only /usr/bin/true in a temporary
        # cgroup, then removes its evidence directory. It is the same bootstrap
        # test execute runs before candidate-controlled code. Fail closed here,
        # after exact archive and current intake preparation have been recorded.
        try:
            bootstrap = verify_submission.supervisor_bootstrap(work)
            receipt["cgroup_bootstrap"] = {"tested": True, "passed": True, "argv_prefix": bootstrap}
        except Exception as error:
            receipt["cgroup_bootstrap"] = {
                "tested": True,
                "passed": False,
                "error_type": type(error).__name__,
                "error": str(error),
            }
            raise RuntimeError("current verifier cgroup bootstrap preflight failed") from error
        write_json(output, receipt)

        env = dict(os.environ)
        for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "PALOMAR_JOB_STARTED_AT",
                     "MATHLIB_CACHE_DIR", "MATHLIB_CACHE_GET_URL", "LAKE_PKG_URL_MAP"):
            env.pop(name, None)
        env["PALOMAR_EXECUTION_PROFILE"] = STANDARD_PROFILE
        env["TMPDIR"] = str(work / "tmp")
        Path(env["TMPDIR"]).mkdir()
        command = [
            sys.executable, str(policy / "scripts" / "verify_submission.py"), "execute",
            "--work-dir", str(work / "prepare-work"),
            "--output", str(local_mechanical),
            "--bwrap", str(bwrap),
            "--bwrap-source-tag", BWRAP_TAG,
            "--execution-budget-seconds", str(args.execution_budget_seconds),
            "--workflow-url", "local-only:not-an-official-palomar-report",
        ]
        receipt["execute_command"] = command
        receipt["execute_started_at"] = datetime.now(timezone.utc).isoformat()
        write_json(output, receipt)
        log = work / "execute.log"
        with log.open("x", encoding="utf-8") as stream:
            process = subprocess.run(command, cwd=policy, env=env,
                                     stdout=stream, stderr=subprocess.STDOUT, check=False)
        receipt["execute_exit_code"] = process.returncode
        receipt["execute_log_sha256"] = sha256(log)
        receipt["execution_report_sha256"] = sha256(local_mechanical)
        receipt["execution_status"] = json.loads(local_mechanical.read_text(encoding="utf-8")).get("status")
        archive_checker.check_sources(source, snapshot)
        receipt["source_snapshot_unchanged_after_execute"] = True
        archive_checker.check_sources(work_dir_for_prepare / "source", snapshot)
        receipt["prepared_source_snapshot_unchanged_after_execute"] = True
        receipt["state"] = "passed" if process.returncode == 0 and receipt["execution_status"] == "pass" else "failed"
        receipt["passed"] = receipt["state"] == "passed"
        receipt["finished_at"] = datetime.now(timezone.utc).isoformat()
        write_json(output, receipt)
        return 0 if receipt["passed"] else 1
    except Exception as error:
        receipt["state"] = "blocked" if "cgroup bootstrap" in str(error) else "failed"
        receipt["error"] = f"{type(error).__name__}: {error}"
        receipt["finished_at"] = datetime.now(timezone.utc).isoformat()
        write_json(output, receipt)
        print(receipt["error"], file=sys.stderr)
        return 2 if receipt["state"] == "blocked" else 1


if __name__ == "__main__":
    raise SystemExit(main())
