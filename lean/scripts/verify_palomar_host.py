#!/usr/bin/env python3
"""Reproduce the full pinned Palomar pipeline on an identified local archive.

Default: read-only preflight. --launch starts a detached user-systemd scope;
--run runs in the foreground. Both use fresh work/evidence paths. The only
upstream substitution is prepare's remote checkout, replaced with the exact
validated local archive. No build, sandbox, export, comparison or kernel check
is removed. Results are local evidence, never an official Palomar report.

The supported Namespace profile specifies capacity minimums. It does not cap
this host at 32 GiB: official phase cgroups use 95%/98% of effective host RAM.
This launcher adds neither a CPU restriction nor a memory cap.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode = True
PROJECT = Path(__file__).resolve().parent.parent
SELF = Path(__file__).resolve()
ARCHIVE_CHECKER = PROJECT / "scripts/verify-zeta-candidate.py"
SUBMISSION_HEAD = "65f0154ed776cd26c224254aa57b379137f28b0d"
POLICY_HEAD = "96b034cc31a72a63d4f4041911dce337a85c9a04"
PROFILE = "palomar-namespace-16x32-v1"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
CANONICAL_PREFIX = Path("/opt/lean/toolchains/leanprover--lean4---v4.35.0-rc2")
LEAN_TOOLS = {"lean", "lake", "leanexport", "leanchecker", "con-ron", "nanoda_bin"}
TOOL_NAMES = LEAN_TOOLS | {"bwrap", "python", "bundle"}
SETUP_ENVIRONMENT = {"BUNDLE_PATH", "GEM_HOME", "GEM_PATH", "BUNDLE_FROZEN", "BUNDLE_DEPLOYMENT"}
LOCAL_REPOSITORY = "local/conditional-candidate"
ACCEPTANCES = {name: f"{name} kernel accepts the solution" for name in
               ("con-ron", "nanoda", "Lean default")}


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".writing")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def git(tree, *args):
    return subprocess.check_output(
        ["git", "-c", "core.hooksPath=/dev/null", "-C", str(tree), *args],
        text=True, env={**os.environ, "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_CONFIG_NOSYSTEM": "1"},
    ).strip()


def clean_pin(tree, pin):
    if git(tree, "rev-parse", "HEAD") != pin:
        raise ValueError(f"wrong upstream revision: {tree}")
    if git(tree, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError(f"upstream tree is not clean: {tree}")


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ValueError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_hashed_file(item):
    path = Path(item["path"])
    if not path.is_absolute() or not re.fullmatch(r"[0-9a-f]{64}", item["sha256"]):
        raise ValueError("trusted file needs an absolute path and lowercase SHA-256")
    if digest(path) != item["sha256"]:
        raise ValueError(f"trusted file identity changed: {path}")
    return path


def validate_setup(path):
    setup = read_json(path)
    if setup.get("schema") != "unit-distance-trusted-setup-v1":
        raise ValueError("unsupported trusted setup manifest schema")
    if setup["toolchain"]["id"] != TOOLCHAIN:
        raise ValueError("setup does not name the submitted Lean toolchain")
    if Path(setup["toolchain"]["prefix"]) != CANONICAL_PREFIX:
        raise ValueError("setup must use the canonical shared Lean toolchain")
    if CANONICAL_PREFIX.resolve(strict=True) != CANONICAL_PREFIX:
        raise ValueError("canonical Lean toolchain must be a real installation directory")
    if set(setup["tools"]) != TOOL_NAMES:
        raise ValueError("trusted setup must identify all six Lean binaries, bwrap, python and bundle")
    for name, item in setup["tools"].items():
        tool = validate_hashed_file(item)
        if not os.access(tool, os.X_OK):
            raise ValueError(f"trusted tool is not executable: {tool}")
        if name in LEAN_TOOLS and (tool != CANONICAL_PREFIX / "bin" / name or tool.is_symlink()):
            raise ValueError(f"{name} must be the official binary inside the shared toolchain")
    for item in setup.get("files", []):
        validate_hashed_file(item)
    if not set(setup.get("environment", {})) <= SETUP_ENVIRONMENT:
        raise ValueError("unsupported trusted setup environment variable")
    for name, pin in (("submission", SUBMISSION_HEAD), ("policy", POLICY_HEAD)):
        tree = setup["upstream"][name]
        if tree["commit"] != pin or not Path(tree["path"]).is_absolute():
            raise ValueError(f"wrong {name} pin in trusted setup")
        clean_pin(Path(tree["path"]), pin)
    return setup


def require_gate(gate, archive_sha, submission):
    required = {"state": "passed", "passed": True, "deterministic_archive": True,
                "sources_unchanged": True, "archive_sha256": archive_sha,
                "policy_revision": SUBMISSION_HEAD, "policy_tree": str(submission)}
    if any(gate.get(key) != value for key, value in required.items()):
        raise ValueError("archive gate does not certify these exact bytes at the selected verifier pin")


def execution_environment(setup, started, temporary):
    env = dict(os.environ)
    for name in list(env):
        if name.startswith(("BUNDLE_", "GEM_", "PYTHON")) or name in {
            "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN_NUM_THREADS",
            "RAYON_NUM_THREADS", "OMP_NUM_THREADS",
            "PALOMAR_JOB_STARTED_AT", "PALOMAR_EXECUTION_PROFILE", "MATHLIB_CACHE_DIR",
            "MATHLIB_CACHE_GET_URL", "LAKE_PKG_URL_MAP", "LAKE_NO_CACHE", "LAKE_ARTIFACT_CACHE",
            "LD_PRELOAD", "LD_LIBRARY_PATH", "RUBYOPT", "RUBYLIB", "COMPARATOR_BWRAP",
        }:
            env.pop(name, None)
    env.update(setup.get("environment", {}))
    env.update({
        "PATH": os.pathsep.join((str(CANONICAL_PREFIX / "bin"),
                                  str(Path(setup["tools"]["python"]["path"]).parent),
                                  "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin")),
        "PALOMAR_EXECUTION_PROFILE": PROFILE, "PALOMAR_JOB_STARTED_AT": str(started),
        "TMPDIR": str(temporary), "PYTHONDONTWRITEBYTECODE": "1",
        "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_CONFIG_NOSYSTEM": "1", "GIT_TERMINAL_PROMPT": "0",
    })
    return env


def execution_command(setup, work, report, budget):
    return [setup["tools"]["python"]["path"],
            str(Path(setup["upstream"]["submission"]["path"]) / "scripts/verify_submission.py"),
            "execute", "--work-dir", str(work / "prepare-work"), "--output", str(report),
            "--bwrap", setup["tools"]["bwrap"]["path"], "--bwrap-source-tag", "v0.12.0",
            "--execution-budget-seconds", str(budget),
            "--workflow-url", "local-only:not-an-official-palomar-report"]


def check_terminal(report, returncode, archive_sha, selected, expected_kernels):
    """Require affirmative evidence, not a started checker or a zero wrapper exit."""
    if returncode != 0 or report.get("status") != "pass" or report.get("stage") != "complete":
        raise ValueError("official execution did not finish with status pass and stage complete")
    if report.get("source", {}).get("archive_sha256") != archive_sha:
        raise ValueError("terminal source identity disagrees with this archive")
    if report.get("verification_profile", {}).get("id") != PROFILE:
        raise ValueError("terminal verification profile disagrees")
    protected = json.loads(report["protected_config"])
    if hashlib.sha256(report["protected_config"].encode()).hexdigest() != report["protected_config_sha256"]:
        raise ValueError("protected configuration digest disagrees")
    if not re.fullmatch(r"PalomarCanonical[0-9a-f]{24}\.Challenge", protected.get("challenge_module", "")):
        raise ValueError("protected Challenge alias is absent")
    for name in ("solution_module", "theorem_names", "definition_names", "permitted_axioms"):
        if protected.get(name) != selected.get(name, []):
            raise ValueError(f"protected configuration changed the selected {name}")
    if set(protected["permitted_axioms"]) != {"propext", "Quot.sound", "Classical.choice"}:
        raise ValueError("selected permitted axiom set changed")
    if protected.get("external_kernels") != expected_kernels:
        raise ValueError("protected configuration does not run both pinned external kernels")
    observed_kernels = {item["name"]: item["argv"] for item in report.get("kernels", [])}
    if observed_kernels != expected_kernels:
        raise ValueError("terminal kernel identities disagree")
    lines = set(report.get("comparator_log_tail", "").splitlines())
    if not set(ACCEPTANCES.values()) <= lines:
        raise ValueError("missing affirmative acceptance from con-ron, NanoDa or Lean")
    if report.get("errors"):
        raise ValueError("terminal pass includes errors")
    return {"fresh_project_build": True, "protected_challenge_export": True,
            "protected_solution_export": True, "statement_and_definition_comparison": True,
            "allowed_axioms": protected["permitted_axioms"],
            "kernel_acceptances": ACCEPTANCES,
            "basis": "Unmodified pinned execute completed; protected configuration and all kernel acceptances checked."}


def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--expect-sha256", required=True)
    parser.add_argument("--archive-gate", required=True, type=Path)
    parser.add_argument("--trusted-setup", required=True, type=Path)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--work-dir", type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--launch", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--supervise", action="store_true", help=argparse.SUPPRESS)
    mode.add_argument("--adapter", action="store_true", help=argparse.SUPPRESS)
    return parser.parse_args()


def common_arguments(args):
    return ["--archive", str(args.archive), "--expect-sha256", args.expect_sha256,
            "--archive-gate", str(args.archive_gate), "--trusted-setup", str(args.trusted_setup),
            "--output-dir", str(args.output_dir), "--work-dir", str(args.work_dir)]


def preflight(args):
    args.archive = args.archive.resolve(strict=True)
    args.archive_gate = args.archive_gate.resolve(strict=True)
    args.trusted_setup = args.trusted_setup.resolve(strict=True)
    if not re.fullmatch(r"[0-9a-f]{64}", args.expect_sha256) or digest(args.archive) != args.expect_sha256:
        raise ValueError("archive does not match --expect-sha256")
    setup = validate_setup(args.trusted_setup)
    submission = Path(setup["upstream"]["submission"]["path"])
    require_gate(read_json(args.archive_gate), args.expect_sha256, submission)
    profile_module = load_module(submission / "scripts/verification_profile.py", "host_verification_profile")
    profile = profile_module.load_profile(PROFILE)
    if profile["id"] != PROFILE or profile["limits"]["execution_budget_seconds"] != 19_800:
        raise ValueError("pinned supported profile/deadline unexpectedly changed")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    args.output_dir = (args.output_dir or PROJECT / "verification/migration-20260929" / ("full-" + stamp)).resolve()
    args.work_dir = (args.work_dir or PROJECT / ".cache/build-tmp" / ("migration-full-" + stamp)).resolve()
    for path in (args.output_dir, args.work_dir):
        if not path.is_relative_to(PROJECT) or path == PROJECT:
            raise ValueError("work and evidence directories must stay inside the research Lean project")
    if args.output_dir == args.work_dir or args.output_dir.is_relative_to(args.work_dir) or args.work_dir.is_relative_to(args.output_dir):
        raise ValueError("work and evidence directories must be disjoint")
    if args.work_dir.exists() or (args.output_dir.exists() and not (args.supervise or args.adapter)):
        raise ValueError("use fresh work and evidence paths; earlier attempts are preserved")
    observed = profile_module.check_host(profile, PROJECT)
    return setup, profile, {
        "schema": "unit-distance-new-host-launch-v1", "state": "preflight", "at": now(),
        "archive": str(args.archive), "archive_sha256": args.expect_sha256,
        "archive_gate": str(args.archive_gate), "trusted_setup": str(args.trusted_setup),
        "execution_profile": PROFILE, "profile": profile,
        "profile_sha256": profile_module.profile_digest(profile), "observed_host": observed,
        "inherited_cpu_affinity": sorted(os.sched_getaffinity(0)),
        "outer_cpu_limit": None, "outer_memory_limit": None,
        "resource_policy": "All inherited CPUs; official phase cgroups use 95%/98% of effective host RAM.",
        "execution_budget_seconds": profile["limits"]["execution_budget_seconds"],
        "job_timeout_seconds": profile["limits"]["job_timeout_minutes"] * 60,
        "inputs_sha256": {str(p): digest(p) for p in (SELF, ARCHIVE_CHECKER, args.trusted_setup, args.archive_gate)},
        "tools": setup["tools"], "upstream": setup["upstream"],
        "out": str(args.output_dir), "work": str(args.work_dir),
        "local_only": True, "official_palomar_report": False, "remote_submission": False,
    }


def verify_launch_inputs(args, current):
    launch = read_json(args.output_dir / "launch.json")
    for key in ("archive_sha256", "profile_sha256", "inputs_sha256", "tools", "upstream", "out", "work"):
        if launch.get(key) != current.get(key):
            raise ValueError(f"launch input changed: {key}")


def adapter(args, setup, profile, launch):
    started_epoch = float(os.environ["PALOMAR_JOB_STARTED_AT"])
    work, out = args.work_dir, args.output_dir
    work.mkdir(parents=True)
    (work / "tmp").mkdir()
    env = execution_environment(setup, started_epoch, work / "tmp")
    os.environ.clear()
    os.environ.update(env)
    # Profile selection and the shared clock must precede the upstream import.
    policy = Path(setup["upstream"]["submission"]["path"])
    sys.path.insert(0, str(policy))
    from scripts import verify_submission as verifier
    if verifier.VERIFICATION_PROFILE != profile:
        raise ValueError("upstream import selected a different verification profile")
    report_path = out / "execution.json"
    receipt = {**{key: launch[key] for key in ("archive_sha256", "execution_profile", "profile_sha256",
                                             "tools", "upstream", "local_only", "official_palomar_report", "remote_submission")},
               "schema": "unit-distance-new-host-execution-v1", "state": "running", "passed": False,
               "started_at": now(), "job_started_at_epoch": started_epoch,
               "budget_scope": "Local preflight, preparation and execute share the official clock. Installed tool download/setup time is not reproduced.",
               "execution_budget_seconds": profile["limits"]["execution_budget_seconds"],
               "execution_report": str(work / "local-execution.json"), "work_directory": str(work)}
    write_json(report_path, receipt)
    try:
        archive_checker = load_module(ARCHIVE_CHECKER, "host_archive_checker")
        source = work / "source"
        snapshot = archive_checker.extract(args.archive, source)
        archive_checker.check_sources(source, snapshot)
        receipt["project_build_outputs_initially_absent"] = not (source / ".lake").exists()
        if not receipt["project_build_outputs_initially_absent"]:
            raise ValueError("submitted archive contains project build state")
        if (source / "lean-toolchain").read_text().strip() != TOOLCHAIN:
            raise ValueError("archive selects a different toolchain")
        receipt["source_snapshot_sha256"] = digest(source / "SOURCE_SNAPSHOT.json")
        receipt["snapshot_file_count"] = len(snapshot)
        git(source, "init", "--quiet")
        git(source, "add", ".")
        git(source, "-c", "user.name=Local Palomar verification", "-c", "user.email=local-verification@invalid",
            "commit", "--quiet", "--no-gpg-sign", "-m", "Exact local archive; unpublished synthetic commit")
        local_commit = git(source, "rev-parse", "HEAD")
        verifier.validate_preservable_git_checkout(source, "local archive")
        verifier.reject_committed_build_artifacts(source)
        receipt["local_git_commit"] = local_commit
        receipt["local_source_bytes"] = verifier.tree_size(source)
        event = {"inputs": {"repository": LOCAL_REPOSITORY, "commit": local_commit,
                            "request_id": "local0000001", "mode": "full",
                            "options": json.dumps({"comparator_config_path": "comparator-zeta.json",
                                                   "authorization_relationship": "I am a responsible author or maintainer"})}}
        write_json(work / "local-input.json", event)
        original_clone = verifier.clone_commit

        def copy_local_archive(url, commit, destination):
            if url != "https://github.com/" + LOCAL_REPOSITORY or commit != local_commit:
                raise ValueError("prepare requested a different source")
            shutil.copytree(source, destination, symlinks=True)

        verifier.clone_commit = copy_local_archive
        try:
            result = verifier.prepare(argparse.Namespace(event=str(work / "local-input.json"),
                                      work_dir=str(work / "prepare-work"), output=str(work / "prepared-report.json"),
                                      licensee=setup["tools"]["bundle"]["path"]))
        finally:
            verifier.clone_commit = original_clone
        prepared = read_json(work / "prepared-report.json")
        receipt.update(prepare_exit_code=result, prepare_status=prepared.get("status"),
                       prepare_errors=prepared.get("errors", []))
        write_json(report_path, receipt)
        if result != 0 or prepared.get("status") != "pending":
            raise ValueError("official prepare did not accept the local candidate")
        prepared_source = work / "prepare-work/source"
        archive_checker.check_sources(prepared_source, snapshot)
        if (prepared_source / ".lake").exists():
            raise ValueError("prepared source unexpectedly has build state")
        prepared["source"] = {"kind": "unpublished-local-archive", "local_commit": local_commit,
                              "archive_sha256": args.expect_sha256,
                              "source_snapshot_sha256": receipt["source_snapshot_sha256"],
                              "bytes": receipt["local_source_bytes"]}
        prepared["submission"] = {"scope": "local-only; no Palomar submission id"}
        prepared.update(local_only=True, official_palomar_report=False)
        prepared["verification_profile"]["observed_host"] = launch["observed_host"]
        write_json(work / "prepared-report.json", prepared)
        metadata = read_json(work / "prepare-work/metadata.json")
        metadata.update({key: prepared[key] for key in ("source", "submission", "local_only",
                                                       "official_palomar_report", "verification_profile")})
        write_json(work / "prepare-work/metadata.json", metadata)
        mechanical = work / "local-execution.json"
        write_json(mechanical, prepared)
        receipt["prepared_source_snapshot_verified"] = True
        receipt["prepared_project_build_outputs_initially_absent"] = True
        receipt["cgroup_bootstrap"] = verifier.supervisor_bootstrap(work)
        command = execution_command(setup, work, mechanical, profile["limits"]["execution_budget_seconds"])
        receipt["execute_command"] = command
        receipt["execute_started_at"] = now()
        write_json(report_path, receipt)
        with (work / "execute.log").open("x", encoding="utf-8") as stream:
            process = subprocess.run(command, cwd=policy, env=env, stdout=stream,
                                     stderr=subprocess.STDOUT, check=False)
        receipt["execute_exit_code"] = process.returncode
        terminal = read_json(mechanical)
        receipt.update(execution_status=terminal.get("status"), execution_stage=terminal.get("stage"))
        archive_checker.check_sources(source, snapshot)
        archive_checker.check_sources(prepared_source, snapshot)
        for tree in (source, prepared_source):
            if digest(tree / "SOURCE_SNAPSHOT.json") != receipt["source_snapshot_sha256"]:
                raise ValueError("source snapshot manifest changed during execution")
        if digest(args.archive) != args.expect_sha256:
            raise ValueError("archive changed during execution")
        validate_setup(args.trusted_setup)
        for path, expected in launch["inputs_sha256"].items():
            if digest(path) != expected:
                raise ValueError(f"runner input changed during execution: {path}")
        receipt["sources_unchanged"] = receipt["tools_unchanged"] = True
        expected_kernels = verifier.protected_kernels({name: Path(setup["tools"][name]["path"]) for name in LEAN_TOOLS})
        receipt["completed_checks"] = check_terminal(terminal, process.returncode, args.expect_sha256,
                                                     read_json(source / "comparator-zeta.json"), expected_kernels)
        receipt["exports"] = {name: {"path": str(path), "bytes": path.stat().st_size, "sha256": digest(path)}
                              for name in ("challenge", "solution")
                              for path in [work / "prepare-work/exports" / (name + ".export")]}
        receipt.update(state="passed", passed=True)
    except Exception as error:
        receipt.update(state="failed", passed=False, error=f"{type(error).__name__}: {error}")
        print(receipt["error"], file=sys.stderr, flush=True)
    finally:
        for name, path in (("execution_report_sha256", work / "local-execution.json"),
                           ("execute_log_sha256", work / "execute.log"),
                           ("resource_metrics_sha256", work / "prepare-work/resource-metrics.jsonl")):
            if path.is_file():
                receipt[name] = digest(path)
        receipt.update(finished_at=now(), seconds=round(time.time() - started_epoch, 3))
        write_json(report_path, receipt)
    return 0 if receipt["passed"] else 1


def observe(args):
    memory = {line.split(":", 1)[0]: int(line.split()[1]) * 1024
              for line in Path("/proc/meminfo").read_text().splitlines()
              if line.startswith(("MemTotal:", "MemAvailable:", "SwapFree:"))}
    result = {"at": now(), "host_memory_bytes": memory,
              "workspace_free_bytes": shutil.disk_usage(PROJECT).free}
    try:
        report = read_json(args.work_dir / "local-execution.json")
        result.update(status=report.get("status"), stage=report.get("stage"),
                      resource_usage=report.get("resource_usage"))
    except (OSError, ValueError):
        result.update(status="preparing", stage="local-preparation")
    return result


def supervise(args, setup, profile, launch):
    started = time.time()
    command = [setup["tools"]["python"]["path"], str(SELF), *common_arguments(args), "--adapter"]
    report = {"schema": "unit-distance-new-host-supervisor-v1", "state": "running", "passed": False,
              "archive_sha256": args.expect_sha256, "execution_profile": PROFILE,
              "started_at": now(), "job_started_at_epoch": started, "adapter_command": command,
              "official_palomar_report": False, "local_only": True}
    output = args.output_dir / "supervisor.json"
    write_json(output, report)
    process = None
    previous_sigterm = signal.getsignal(signal.SIGTERM)

    def terminated(signum, frame):
        raise InterruptedError(f"supervisor received signal {signum}")

    signal.signal(signal.SIGTERM, terminated)
    try:
        env = execution_environment(setup, started, args.work_dir / "tmp")
        with (args.output_dir / "adapter.log").open("x", encoding="utf-8") as stream:
            process = subprocess.Popen(command, cwd=PROJECT, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
        report["adapter_pid"] = process.pid
        write_json(output, report)
        # Leave one minute of the published job window for cleanup and receipt.
        deadline = time.monotonic() + profile["limits"]["job_timeout_minutes"] * 60 - 60
        with (args.output_dir / "observations.jsonl").open("x", encoding="utf-8") as observations:
            while process.poll() is None:
                sample = observe(args)
                observations.write(json.dumps(sample, sort_keys=True) + "\n")
                observations.flush()
                if time.monotonic() >= deadline:
                    raise TimeoutError("outer job deadline reached after official execution budget and cleanup margin")
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    pass
        report["adapter_exit_code"] = process.returncode
        execution = read_json(args.output_dir / "execution.json")
        terminal = read_json(args.work_dir / "local-execution.json")
        if not (process.returncode == 0 and execution.get("state") == "passed"
                and execution.get("passed") is True and terminal.get("status") == "pass"
                and terminal.get("stage") == "complete" and execution.get("archive_sha256") == args.expect_sha256
                and terminal.get("source", {}).get("archive_sha256") == args.expect_sha256):
            raise ValueError("adapter and official terminal reports do not jointly establish a pass")
        report.update(state="passed", passed=True, terminal_reports_agree=True)
    except BaseException as error:
        report.update(state="failed", error=f"{type(error).__name__}: {error}")
        if process is not None and process.poll() is None:
            # The official babysitter also watches verifier liveness and kills
            # its cgroup if that verifier disappears, including detached tasks.
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=30)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=10)
        if process is not None:
            report["adapter_exit_code"] = process.returncode
        print(report["error"], file=sys.stderr, flush=True)
    finally:
        signal.signal(signal.SIGTERM, previous_sigterm)
        for name, path in (("execution_sha256", args.output_dir / "execution.json"),
                           ("local_execution_sha256", args.work_dir / "local-execution.json")):
            if path.is_file():
                report[name] = digest(path)
        report.update(finished_at=now(), seconds=round(time.time() - started, 3), final_observation=observe(args))
        write_json(output, report)
    return 0 if report["passed"] else 1


def main():
    args = arguments()
    setup, profile, launch = preflight(args)
    if args.adapter or args.supervise:
        verify_launch_inputs(args, launch)
        if args.adapter:
            return adapter(args, setup, profile, launch)
        return supervise(args, setup, profile, launch)
    if not (args.launch or args.run):
        print(json.dumps(launch, indent=2, sort_keys=True))
        return 0
    if args.launch and Path("/proc/1/comm").read_text().strip() != "systemd":
        raise ValueError("detached launch requires user systemd; --run remains available")
    args.output_dir.mkdir(parents=True)
    launch.update(state="launching", launched_at=now())
    write_json(args.output_dir / "launch.json", launch)
    if args.run:
        return supervise(args, setup, profile, launch)
    unit = "unit-distance-full-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%f").lower()
    command = ["systemd-run", "--user", "--scope", "--quiet", "--unit=" + unit,
               "--property=RuntimeMaxSec=" + str(profile["limits"]["job_timeout_minutes"] * 60), "--",
               setup["tools"]["python"]["path"], str(SELF), *common_arguments(args), "--supervise"]
    try:
        env = execution_environment(setup, time.time(), args.work_dir / "tmp")
        with (args.output_dir / "launcher.log").open("x", encoding="utf-8") as stream:
            process = subprocess.Popen(command, cwd=PROJECT, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
        launch.update(state="launched", pid=process.pid, unit=unit + ".scope", command=command)
    except Exception as error:
        launch.update(state="launch-failed", error=f"{type(error).__name__}: {error}")
        raise
    finally:
        write_json(args.output_dir / "launch.json", launch)
    print(json.dumps({key: launch[key] for key in ("state", "pid", "out", "work", "unit")}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
