#!/usr/bin/env python3
"""Run the unchanged pinned Palomar verifier in one bounded user slice.

Default: read-only preflight. --probe runs only official delegation/capacity
probes; --run runs the full pipeline. --launch detaches the full controller.
No upstream file or previous receipt is edited. A strict local systemd provider
adapter adds one dedicated slice to the official delegated-scope invocation.
All verification payloads share its memory limit, CPU quota and CPU affinity.
The small evidence/cleanup controller stays outside, so OOMs retain receipts.
This is local hardware reproduction, not a hosted Palomar report.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode = True
SELF = Path(__file__).resolve()
PROJECT = SELF.parent.parent
BASE_PATH = SELF.with_name("verify_palomar_host.py")
_spec = importlib.util.spec_from_file_location("bounded_host_shared_checks", BASE_PATH)
base = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(base)
TARGETS = {
    "standard": {"profile": "palomar-standard-v1", "cpus": 4, "memory_bytes": 16 * 1024**3},
    "namespace": {"profile": "palomar-namespace-16x32-v1", "cpus": 16, "memory_bytes": 32 * 1024**3},
}
SYSTEMD_RUN = Path("/usr/bin/systemd-run")
SYSTEMCTL = Path("/usr/bin/systemctl")
CGROUP_ROOT = Path("/sys/fs/cgroup")
OFFICIAL_SCOPE_PREFIX = ["--user", "--scope", "--quiet", "--property=Delegate=yes", "--"]
CGROUP_FILES = ("memory.max", "memory.high", "memory.swap.max", "memory.current", "memory.peak",
                "memory.events", "memory.events.local", "cpu.max", "cpu.stat", "pids.current",
                "cgroup.events", "cgroup.controllers", "cgroup.subtree_control")


def call(command, **kwargs):
    return subprocess.run([str(x) for x in command], check=True, text=True, capture_output=True,
                          timeout=60, **kwargs).stdout.strip()


def config_path(value):
    path = Path(value)
    return (path if path.is_absolute() else PROJECT / path).resolve(strict=True)


def load_config(path):
    value = base.read_json(path)
    required = {"schema", "archive", "archive_sha256", "archive_gate", "trusted_setup", "target",
                "comparator_config_path"}
    if set(value) - (required | {"cpus"}) or not required <= set(value):
        raise ValueError("configuration has missing or unsupported keys")
    if value["schema"] != "unit-distance-bounded-config-v1" or value["target"] not in TARGETS:
        raise ValueError("unsupported bounded configuration schema or target")
    target = TARGETS[value["target"]]
    relative = PurePosixPath(value["comparator_config_path"])
    if (relative.is_absolute() or not relative.parts or ".." in relative.parts
            or str(relative) != value["comparator_config_path"] or "\\" in str(relative)):
        raise ValueError("comparator_config_path must be a canonical relative archive path")
    value = {**value, **{key: str(config_path(value[key])) for key in
                       ("archive", "archive_gate", "trusted_setup")}, "target_limits": target}
    if not re.fullmatch(r"[0-9a-f]{64}", value["archive_sha256"]):
        raise ValueError("archive SHA-256 must be lowercase hex")
    affinity = sorted(os.sched_getaffinity(0))
    cpus = value.get("cpus", affinity[:target["cpus"]])
    if (not isinstance(cpus, list) or any(type(cpu) is not int for cpu in cpus)
            or len(cpus) != target["cpus"] or cpus != sorted(set(cpus))
            or not set(cpus) <= set(affinity)):
        raise ValueError("CPU selection must identify exactly the target's available CPUs")
    value["cpus"] = cpus
    return value


def profile_module(setup):
    return base.load_module(Path(setup["upstream"]["submission"]["path"]) /
                            "scripts/verification_profile.py", "bounded_verification_profile")


def preflight(config, output, work):
    config = config.resolve(strict=True)
    selected = load_config(config)
    archive = Path(selected["archive"])
    if base.digest(archive) != selected["archive_sha256"]:
        raise ValueError("archive identity does not match configuration")
    setup = base.validate_setup(selected["trusted_setup"])
    upstream = Path(setup["upstream"]["submission"]["path"])
    base.require_gate(base.read_json(selected["archive_gate"]), selected["archive_sha256"], upstream)
    module = profile_module(setup)
    profile = module.load_profile(selected["target_limits"]["profile"])
    if profile["limits"]["execution_budget_seconds"] != 19_800:
        raise ValueError("pinned official execution deadline changed")
    observed = module.check_host(profile, PROJECT)
    if observed["memory_bytes"] < selected["target_limits"]["memory_bytes"]:
        raise ValueError("this enclosing environment has less memory than the requested target")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    output = (output or PROJECT / "verification/hosted-fit-20260929" / (selected["target"] + "-" + stamp)).resolve()
    work = (work or PROJECT / ".cache/hosted-fit-20260929" / (selected["target"] + "-" + stamp)).resolve()
    for path in (output, work):
        if not path.is_relative_to(PROJECT) or path == PROJECT or path.exists():
            raise ValueError("use fresh work/evidence directories inside the research Lean project")
    if output.is_relative_to(work) or work.is_relative_to(output):
        raise ValueError("work and evidence directories must be disjoint")
    run_id = hashlib.sha256(str(output).encode()).hexdigest()[:20]
    inputs = [SELF, BASE_PATH, base.ARCHIVE_CHECKER, config, Path(selected["trusted_setup"]),
              Path(selected["archive_gate"]), SYSTEMD_RUN, SYSTEMCTL]
    return {"schema": "unit-distance-bounded-launch-v1", "created_at": base.now(),
            "configuration": selected, "configuration_path": str(config), "profile": profile,
            "profile_sha256": module.profile_digest(profile), "unbounded_host": observed,
            "execution_budget_seconds": profile["limits"]["execution_budget_seconds"],
            "job_timeout_seconds": profile["limits"]["job_timeout_minutes"] * 60,
            "slice": "udpalomar" + run_id + ".slice", "controller_unit": "udpalomarcontroller" + run_id,
            "output": str(output), "work": str(work), "tools": setup["tools"], "upstream": setup["upstream"],
            "inputs_sha256": {str(path): base.digest(path) for path in inputs},
            "local_only": True, "official_palomar_report": False, "remote_submission": False,
            "budget_scope": "Preparation and execute share the official clock; preinstalled tool download/setup is not reproduced.",
            "resource_scope": "All verification payloads share the bounded slice; evidence/cleanup controller remains outside it."}


def verify_inputs(launch):
    for path, expected in launch["inputs_sha256"].items():
        if base.digest(path) != expected:
            raise ValueError(f"launcher input changed: {path}")
    config = launch["configuration"]
    if base.digest(config["archive"]) != config["archive_sha256"]:
        raise ValueError("archive bytes changed")
    setup = base.validate_setup(config["trusted_setup"])
    if setup["tools"] != launch["tools"] or setup["upstream"] != launch["upstream"]:
        raise ValueError("trusted identities changed")
    base.require_gate(base.read_json(config["archive_gate"]), config["archive_sha256"],
                      Path(setup["upstream"]["submission"]["path"]))
    module = profile_module(setup)
    profile = module.load_profile(config["target_limits"]["profile"])
    if profile != launch["profile"] or module.profile_digest(profile) != launch["profile_sha256"]:
        raise ValueError("supported profile changed")
    return setup


def read_cgroup(path):
    result = {"path": str(path)}
    for name in CGROUP_FILES:
        try:
            result[name] = (path / name).read_text().strip()
        except FileNotFoundError:
            pass
    return result


def own_cgroup():
    relative = next(line[3:] for line in Path("/proc/self/cgroup").read_text().splitlines()
                    if line.startswith("0::"))
    if ".." in Path(relative).parts:
        raise ValueError("invalid cgroup membership")
    return CGROUP_ROOT / relative.lstrip("/")


def check_boundary(runtime, *, require_member):
    path = Path(runtime["cgroup"])
    if not path.is_relative_to(CGROUP_ROOT) or path.name != runtime["slice"]:
        raise ValueError("invalid bounded ancestor path")
    actual = read_cgroup(path)
    if actual.get("memory.max") != str(runtime["memory_bytes"]) or actual.get("memory.swap.max") != "0":
        raise ValueError("aggregate memory/swap limit is missing or changed")
    quota, period = actual.get("cpu.max", "max 0").split()
    if not quota.isdigit() or int(period) <= 0 or int(quota) != len(runtime["cpus"]) * int(period):
        raise ValueError("aggregate CPU quota is missing or changed")
    if require_member:
        if not own_cgroup().is_relative_to(path):
            raise ValueError("verification process escaped the bounded ancestor")
        if sorted(os.sched_getaffinity(0)) != runtime["cpus"]:
            raise ValueError("verification process has the wrong CPU affinity")
    return actual


def load_runtime(path, *, require_member=True):
    runtime = base.read_json(path)
    if runtime.get("schema") != "unit-distance-bounded-runtime-v1":
        raise ValueError("unexpected runtime manifest")
    if base.digest(runtime["launch_path"]) != runtime["launch_sha256"]:
        raise ValueError("immutable launch receipt changed")
    launch = base.read_json(runtime["launch_path"])
    for item in (runtime["provider"], runtime["systemd_run"], runtime["launcher"], runtime["python"],
                 runtime["official_babysitter"]):
        base.validate_hashed_file(item)
    if runtime["slice"] != launch["slice"] or runtime["cpus"] != launch["configuration"]["cpus"]:
        raise ValueError("runtime route disagrees with launch")
    if runtime["memory_bytes"] != launch["configuration"]["target_limits"]["memory_bytes"]:
        raise ValueError("runtime memory bound disagrees with launch")
    check_boundary(runtime, require_member=require_member)
    return runtime, launch


def routed_command(runtime, arguments, unit):
    if arguments[:len(OFFICIAL_SCOPE_PREFIX)] != OFFICIAL_SCOPE_PREFIX:
        raise ValueError("provider accepts only the unchanged official scope prefix")
    payload = arguments[len(OFFICIAL_SCOPE_PREFIX):]
    if payload[:2] != [runtime["python"]["path"], runtime["official_babysitter"]["path"]]:
        raise ValueError("provider accepts only the pinned official cgroup supervisor")
    if not re.fullmatch(r"udpalomar[a-f0-9]+", unit):
        raise ValueError("invalid routed scope unit")
    return [runtime["systemd_run"]["path"], *OFFICIAL_SCOPE_PREFIX[:-1],
            "--slice=" + runtime["slice"], "--unit=" + unit, "--", *payload]


def route_scope(path, arguments):
    runtime, _ = load_runtime(path)
    # Each invocation has an auditable scope; only placement/name are added.
    unit = "udpalomar" + hashlib.sha256(f"{os.getpid()}:{time.time_ns()}".encode()).hexdigest()[:24]
    command = routed_command(runtime, arguments, unit)
    entry = {"at": base.now(), "pid": os.getpid(), "caller_cgroup": str(own_cgroup()),
             "affinity": sorted(os.sched_getaffinity(0)), "unit": unit + ".scope",
             "expected_cgroup": str(Path(runtime["cgroup"]) / (unit + ".scope")),
             "official_arguments": arguments, "executed_command": command}
    descriptor = os.open(runtime["route_log"], os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
    try:
        line = (json.dumps(entry, sort_keys=True) + "\n").encode()
        if os.write(descriptor, line) != len(line):
            raise OSError("incomplete route receipt write")
    finally:
        os.close(descriptor)
    os.execv(command[0], command)


def execution_environment(setup, started, work, runtime, launch):
    base.PROFILE = launch["configuration"]["target_limits"]["profile"]
    env = base.execution_environment(setup, started, work / "tmp")
    env["PATH"] = str(Path(runtime["provider"]["path"]).parent) + os.pathsep + env["PATH"]
    return env


def official_import(setup, launch):
    sys.path.insert(0, setup["upstream"]["submission"]["path"])
    from scripts import verify_submission
    if verify_submission.VERIFICATION_PROFILE != launch["profile"]:
        raise ValueError("official verifier imported a different profile")
    return verify_submission


def capacity(runtime, launch, setup):
    module = profile_module(setup)
    return {"at": base.now(), "cgroup": str(own_cgroup()), "affinity": sorted(os.sched_getaffinity(0)),
            "observed_host": module.check_host(launch["profile"], PROJECT),
            "ancestors": [read_cgroup(path) for path in module.cgroup_directories()],
            "aggregate_boundary": check_boundary(runtime, require_member=True)}


def capacity_child(path):
    runtime, launch = load_runtime(path)
    print(json.dumps(capacity(runtime, launch, {"upstream": launch["upstream"]}), sort_keys=True))
    return 0


def check_phase_capacity(inner, observed, runtime, profile):
    # The unchanged supervisor writes integer byte limits; Linux's memory
    # controller stores whole pages, rounded down. Keep the stricter ceiling.
    page = os.sysconf("SC_PAGE_SIZE")
    requested = {name: runtime["memory_bytes"] * profile["limits"][percent] // 100
                 for name, percent in (("memory.high", "memory_high_percent"),
                                       ("memory.max", "memory_max_percent"))}
    applied = {name: value // page * page for name, value in requested.items()}
    phase = next((entry for entry in inner["ancestors"] if entry["path"] == observed["cgroup"]), {})
    if (inner["observed_host"]["memory_bytes"] != applied["memory.max"]
            or inner["observed_host"]["effective_cpus"] != len(runtime["cpus"])
            or inner["affinity"] != runtime["cpus"]
            or not Path(inner["cgroup"]).is_relative_to(Path(runtime["cgroup"]))
            or not Path(observed["cgroup"]).is_relative_to(Path(runtime["cgroup"]))
            or any(phase.get(name) != str(value) for name, value in applied.items())):
        raise ValueError("nested official phase did not retain the expected capacity and ancestor")
    return {"page_size_bytes": page, "requested_bytes": requested, "kernel_applied_bytes": applied}


def bootstrap_probe(path, runtime, launch, setup, verifier):
    """Exercise the real upstream bootstrap and phase supervisor, without Lean."""
    output, work = Path(launch["output"]), Path(launch["work"])
    outer = capacity(runtime, launch, setup)
    expected = runtime["memory_bytes"]
    if (outer["observed_host"]["memory_bytes"] != expected
            or outer["observed_host"]["effective_cpus"] != len(runtime["cpus"])):
        raise ValueError("official outer profile measurement disagrees with bounded target")
    prefix = verifier.supervisor_bootstrap(work)
    if prefix != [runtime["provider"]["path"], *OFFICIAL_SCOPE_PREFIX]:
        raise ValueError("official verifier did not choose the identified routing provider")
    status = output / "capacity-supervisor.json"
    fifo = work / "capacity-liveness"
    os.mkfifo(fifo, 0o600)
    descriptor = os.open(fifo, os.O_RDWR | os.O_CLOEXEC)
    try:
        command = verifier.supervisor_command(
            [setup["tools"]["python"]["path"], "-B", str(SELF), "--capacity-child", str(path)],
            cwd=work, environment={}, timeout=20,
            resource_properties=verifier.permissive_resource_properties(),
            unit_name="palomar-" + hashlib.sha256(str(output).encode()).hexdigest()[:24],
            status_path=status, liveness_path=fifo)
        result = subprocess.run(command, cwd=work, env=os.environ.copy(), text=True,
                                capture_output=True, timeout=60, check=False)
    finally:
        os.close(descriptor)
    (output / "capacity-stdout.json").write_text(result.stdout)
    (output / "capacity-stderr.log").write_text(result.stderr)
    observed = base.read_json(status)
    if result.returncode != 0 or observed.get("state") != "finished" or not observed.get("placement_ok"):
        raise ValueError("official nested supervisor probe failed")
    inner = json.loads(result.stdout)
    phase_limits = check_phase_capacity(inner, observed, runtime, launch["profile"])
    receipt = {"schema": "unit-distance-bounded-capacity-v1", "passed": True,
               "scope": "Official bootstrap and real cgroup supervisor only; no proof execution or sandbox substitution.",
               "official_bootstrap": prefix, "outer": outer, "inner": inner,
               "phase_memory_limits": phase_limits,
               "phase_command": command, "phase_status_sha256": base.digest(status),
               "same_aggregate_ancestor": True, "same_cpu_affinity": True,
               "official_phase_limit_derived_from_bounded_capacity": True}
    base.write_json(output / "capacity.json", receipt)
    return receipt


def full_pipeline(runtime, launch, setup, verifier, receipt):
    config = launch["configuration"]
    output, work = Path(launch["output"]), Path(launch["work"])
    report_path = output / "execution.json"
    checker = base.load_module(base.ARCHIVE_CHECKER, "bounded_archive_checker")
    source = work / "source"
    snapshot = checker.extract(Path(config["archive"]), source)
    checker.check_sources(source, snapshot)
    if (source / ".lake").exists():
        raise ValueError("submitted archive contains project build state")
    if (source / "lean-toolchain").read_text().strip() != base.TOOLCHAIN:
        raise ValueError("archive selects a different toolchain")
    selected_path = source / config["comparator_config_path"]
    if not selected_path.is_file() or not selected_path.resolve().is_relative_to(source):
        raise ValueError("archive does not contain the selected comparator configuration")
    selected = base.read_json(selected_path)
    receipt.update(project_build_outputs_initially_absent=True, snapshot_file_count=len(snapshot),
                   source_snapshot_sha256=base.digest(source / "SOURCE_SNAPSHOT.json"),
                   comparator_config_path=config["comparator_config_path"],
                   comparator_config_sha256=base.digest(selected_path))
    base.git(source, "init", "--quiet")
    # Every archived source is committed, including intentionally ignored source files.
    base.git(source, "add", "--force", ".")
    base.git(source, "-c", "user.name=Local Palomar verification", "-c", "user.email=local-verification@invalid",
             "commit", "--quiet", "--no-gpg-sign", "-m", "Exact local bounded archive; unpublished synthetic commit")
    local_commit = base.git(source, "rev-parse", "HEAD")
    verifier.validate_preservable_git_checkout(source, "local archive")
    verifier.reject_committed_build_artifacts(source)
    receipt.update(local_git_commit=local_commit, local_source_bytes=verifier.tree_size(source))
    event = {"inputs": {"repository": base.LOCAL_REPOSITORY, "commit": local_commit,
                        "request_id": "local0000001", "mode": "full",
                        "options": json.dumps({"comparator_config_path": config["comparator_config_path"],
                            "authorization_relationship": "I am a responsible author or maintainer"})}}
    base.write_json(work / "local-input.json", event)
    original_clone = verifier.clone_commit

    def copy_local_archive(url, commit, destination):
        if url != "https://github.com/" + base.LOCAL_REPOSITORY or commit != local_commit:
            raise ValueError("prepare requested a different source")
        shutil.copytree(source, destination, symlinks=True)

    verifier.clone_commit = copy_local_archive
    try:
        result = verifier.prepare(argparse.Namespace(event=str(work / "local-input.json"),
            work_dir=str(work / "prepare-work"), output=str(work / "prepared-report.json"),
            licensee=setup["tools"]["bundle"]["path"]))
    finally:
        verifier.clone_commit = original_clone
    prepared = base.read_json(work / "prepared-report.json")
    receipt.update(prepare_exit_code=result, prepare_status=prepared.get("status"),
                   prepare_errors=prepared.get("errors", []))
    base.write_json(report_path, receipt)
    if result != 0 or prepared.get("status") != "pending":
        raise ValueError("official prepare did not accept this local archive")
    prepared_source = work / "prepare-work/source"
    checker.check_sources(prepared_source, snapshot)
    if (prepared_source / ".lake").exists():
        raise ValueError("prepared source unexpectedly has build state")
    prepared["source"] = {"kind": "unpublished-local-archive", "local_commit": local_commit,
                          "archive_sha256": config["archive_sha256"],
                          "source_snapshot_sha256": receipt["source_snapshot_sha256"],
                          "bytes": receipt["local_source_bytes"]}
    prepared["submission"] = {"scope": "local-only; no Palomar submission id"}
    prepared.update(local_only=True, official_palomar_report=False)
    prepared["verification_profile"]["observed_host"] = receipt["observed_host"]
    base.write_json(work / "prepared-report.json", prepared)
    metadata = base.read_json(work / "prepare-work/metadata.json")
    metadata.update({key: prepared[key] for key in ("source", "submission", "local_only",
                                                   "official_palomar_report", "verification_profile")})
    base.write_json(work / "prepare-work/metadata.json", metadata)
    mechanical = work / "local-execution.json"
    base.write_json(mechanical, prepared)
    receipt.update(prepared_source_snapshot_verified=True, prepared_project_build_outputs_initially_absent=True)
    command = base.execution_command(setup, work, mechanical, launch["execution_budget_seconds"])
    receipt.update(execute_command=command, execute_started_at=base.now())
    base.write_json(report_path, receipt)
    with (work / "execute.log").open("x", encoding="utf-8") as stream:
        process = subprocess.run(command, cwd=setup["upstream"]["submission"]["path"], env=os.environ.copy(),
                                 stdout=stream, stderr=subprocess.STDOUT, check=False)
    receipt["execute_exit_code"] = process.returncode
    terminal = base.read_json(mechanical)
    receipt.update(execution_status=terminal.get("status"), execution_stage=terminal.get("stage"))
    for tree in (source, prepared_source):
        checker.check_sources(tree, snapshot)
        if base.digest(tree / "SOURCE_SNAPSHOT.json") != receipt["source_snapshot_sha256"]:
            raise ValueError("source snapshot manifest changed during execution")
    verify_inputs(launch)
    receipt["sources_unchanged"] = receipt["tools_unchanged"] = True
    expected_kernels = verifier.protected_kernels({name: Path(setup["tools"][name]["path"])
                                                  for name in base.LEAN_TOOLS})
    receipt["completed_checks"] = base.check_terminal(terminal, process.returncode, config["archive_sha256"],
                                                      selected, expected_kernels)
    expected_profile_sha = (base.digest(verifier.PROFILE_PATH) if launch["profile"]["id"] == "palomar-standard-v1"
                            else launch["profile_sha256"])
    if terminal["verification_profile"].get("sha256") != expected_profile_sha:
        raise ValueError("terminal official profile digest disagrees")
    receipt["exports"] = {name: {"path": str(path), "bytes": path.stat().st_size, "sha256": base.digest(path)}
                          for name in ("challenge", "solution")
                          for path in [work / "prepare-work/exports" / (name + ".export")]}


def worker(path):
    runtime, launch = load_runtime(path)
    setup = verify_inputs(launch)
    work, output = Path(launch["work"]), Path(launch["output"])
    work.mkdir(parents=True)
    (work / "tmp").mkdir()
    env = execution_environment(setup, runtime["started_epoch"], work, runtime, launch)
    os.environ.clear()
    os.environ.update(env)
    verifier = official_import(setup, launch)
    receipt = {"schema": "unit-distance-bounded-execution-v1", "state": "running", "passed": False,
               "started_at": base.now(), "archive_sha256": launch["configuration"]["archive_sha256"],
               "execution_profile": launch["profile"]["id"], "profile_sha256": launch["profile_sha256"],
               "runtime_sha256": base.digest(path), "mode": runtime["mode"],
               "execution_report": str(work / "local-execution.json"),
               "observed_host": profile_module(setup).check_host(launch["profile"], PROJECT),
               "tools": launch["tools"], "upstream": launch["upstream"],
               "local_only": True, "official_palomar_report": False, "remote_submission": False}
    report_path = output / "execution.json"
    base.write_json(report_path, receipt)
    try:
        bootstrap_probe(path, runtime, launch, setup, verifier)
        receipt["capacity_probe_passed"] = True
        if runtime["mode"] == "full":
            full_pipeline(runtime, launch, setup, verifier, receipt)
        verify_inputs(launch)
        load_runtime(path)
        receipt.update(state="passed", passed=True, proof_execution_performed=runtime["mode"] == "full")
    except Exception as error:
        receipt.update(state="failed", passed=False, error=f"{type(error).__name__}: {error}")
        print(receipt["error"], file=sys.stderr, flush=True)
    finally:
        for key, file in (("execution_report_sha256", work / "local-execution.json"),
                          ("execute_log_sha256", work / "execute.log"),
                          ("resource_metrics_sha256", work / "prepare-work/resource-metrics.jsonl")):
            if file.is_file():
                receipt[key] = base.digest(file)
        receipt.update(finished_at=base.now(), seconds=round(time.time() - runtime["started_epoch"], 3))
        base.write_json(report_path, receipt)
    return 0 if receipt["passed"] else 1


def create_runtime(launch, launch_path, started, created):
    """Configure a fresh implicit slice, never the shared app.slice or manager."""
    unit, output = launch["slice"], Path(launch["output"])
    if not re.fullmatch(r"udpalomar[a-f0-9]{20}\.slice", unit):
        raise ValueError("invalid dedicated slice name")
    properties = dict(line.split("=", 1) for line in call(
        [SYSTEMCTL, "--user", "show", unit, "--property=ActiveState", "--property=DropInPaths"]).splitlines())
    if properties != {"ActiveState": "inactive", "DropInPaths": ""}:
        raise ValueError("bounded slice is not fresh and unused")
    target, cpus = launch["configuration"]["target_limits"], launch["configuration"]["cpus"]
    created.append(unit)
    call([SYSTEMCTL, "--user", "set-property", "--runtime", unit,
          "MemoryMax=" + str(target["memory_bytes"]), "MemorySwapMax=0",
          "CPUQuota=" + str(100 * len(cpus)) + "%", "CPUQuotaPeriodSec=100ms",
          "MemoryAccounting=yes", "CPUAccounting=yes"])
    call([SYSTEMCTL, "--user", "start", unit])
    relative = call([SYSTEMCTL, "--user", "show", unit, "--property=ControlGroup", "--value"])
    path = CGROUP_ROOT / relative.lstrip("/")
    if not relative.startswith("/") or path.name != unit or ".." in path.parts:
        raise ValueError("systemd returned an invalid slice cgroup")
    provider = output / "provider-bin/systemd-run"
    provider.parent.mkdir()
    runtime_path = output / "runtime.json"
    python = launch["tools"]["python"]
    provider.write_text("#!" + python["path"] + "\nimport os, sys\nos.execv(" +
                        repr(python["path"]) + ", " + repr([python["path"], "-B", str(SELF),
                        "--route-scope", str(runtime_path)]) + " + sys.argv[1:])\n")
    provider.chmod(0o755)
    babysitter = Path(launch["upstream"]["submission"]["path"]) / "scripts/supervise_cgroup.py"
    runtime = {"schema": "unit-distance-bounded-runtime-v1", "created_at": base.now(),
               "launch_path": str(launch_path), "launch_sha256": base.digest(launch_path),
               "slice": unit, "cgroup": str(path), "memory_bytes": target["memory_bytes"], "cpus": cpus,
               "started_epoch": started, "mode": launch["mode"],
               "route_log": str(output / "scope-routes.jsonl"), "python": python,
               "provider": {"path": str(provider), "sha256": base.digest(provider)},
               "official_babysitter": {"path": str(babysitter), "sha256": base.digest(babysitter)},
               "launcher": {"path": str(SELF), "sha256": base.digest(SELF)},
               "systemd_run": {"path": str(SYSTEMD_RUN), "sha256": base.digest(SYSTEMD_RUN)}}
    check_boundary(runtime, require_member=False)
    base.write_json(runtime_path, runtime)
    return runtime, runtime_path


def check_routes(runtime):
    routes = [json.loads(line) for line in Path(runtime["route_log"]).read_text().splitlines()]
    if len(routes) < 2:
        raise ValueError("missing real bootstrap and capacity phase routes")
    for entry in routes:
        unit = entry["unit"].removesuffix(".scope")
        if (entry["executed_command"] != routed_command(runtime, entry["official_arguments"], unit)
                or entry["expected_cgroup"] != str(Path(runtime["cgroup"]) / entry["unit"])
                or not Path(entry["caller_cgroup"]).is_relative_to(Path(runtime["cgroup"]))
                or entry["affinity"] != runtime["cpus"]):
            raise ValueError("scope route evidence disagrees with the bounded placement")
    return {"count": len(routes), "sha256": base.digest(runtime["route_log"]),
            "all_official_supervisors_routed_to_slice": True}


def counters(raw):
    return {key: int(value) for key, value in (line.split() for line in raw.splitlines())}


def controller(launch_path):
    launch = base.read_json(launch_path)
    setup = verify_inputs(launch)
    if Path("/proc/1/comm").read_text().strip() != "systemd":
        raise ValueError("bounded reproduction requires the real systemd host")
    output, work = Path(launch["output"]), Path(launch["work"])
    started = time.time()
    receipt = {"schema": "unit-distance-bounded-supervisor-v1", "state": "running", "passed": False,
               "started_at": base.now(), "job_started_at_epoch": started,
               "archive_sha256": launch["configuration"]["archive_sha256"],
               "execution_profile": launch["profile"]["id"], "mode": launch["mode"],
               "local_only": True, "official_palomar_report": False,
               "launch_sha256": base.digest(launch_path), "resource_scope": launch["resource_scope"]}
    report_path = output / "supervisor.json"
    base.write_json(report_path, receipt)
    runtime, process, created = None, None, []
    old_handlers = {number: signal.getsignal(number) for number in (signal.SIGTERM, signal.SIGINT)}

    def terminated(number, frame):
        raise InterruptedError(f"controller received signal {number}")

    for number in old_handlers:
        signal.signal(number, terminated)
    try:
        # Ownership is recorded only after checking the slice is fresh.
        runtime, runtime_path = create_runtime(launch, launch_path, started, created)
        receipt["runtime_sha256"] = base.digest(runtime_path)
        receipt["initial_boundary"] = check_boundary(runtime, require_member=False)
        command = [str(SYSTEMD_RUN), "--user", "--scope", "--quiet",
                   "--unit=" + launch["slice"].removesuffix(".slice") + "worker",
                   "--slice=" + launch["slice"], "--property=Delegate=yes",
                   "--property=RuntimeMaxSec=" + str(launch["job_timeout_seconds"]), "--",
                   setup["tools"]["python"]["path"], "-B", str(SELF), "--worker", str(runtime_path)]
        receipt["worker_command"] = command
        env = execution_environment(setup, started, work, runtime, launch)
        with (output / "worker.log").open("x") as stream:
            process = subprocess.Popen(command, cwd=PROJECT, env=env, stdout=stream, stderr=subprocess.STDOUT,
                                       start_new_session=True,
                                       preexec_fn=lambda: os.sched_setaffinity(0, runtime["cpus"]))
        receipt["worker_pid"] = process.pid
        base.write_json(report_path, receipt)
        deadline = time.monotonic() + (120 if launch["mode"] == "probe" else launch["job_timeout_seconds"] - 60)
        with (output / "aggregate-observations.jsonl").open("x") as stream:
            while process.poll() is None:
                sample = {"at": base.now(), "boundary": check_boundary(runtime, require_member=False)}
                stream.write(json.dumps(sample, sort_keys=True) + "\n")
                stream.flush()
                if time.monotonic() >= deadline:
                    raise TimeoutError("bounded controller deadline reached")
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    pass
        receipt["worker_exit_code"] = process.returncode
        execution = base.read_json(output / "execution.json")
        if not (process.returncode == 0 and execution.get("passed") is True and execution.get("state") == "passed"
                and execution.get("archive_sha256") == receipt["archive_sha256"]
                and execution.get("execution_profile") == launch["profile"]["id"]
                and execution.get("mode") == launch["mode"]):
            raise ValueError("bounded worker did not establish a matching terminal pass")
        if launch["mode"] == "full":
            terminal = base.read_json(work / "local-execution.json")
            if not (terminal.get("status") == "pass" and terminal.get("stage") == "complete"
                    and terminal.get("source", {}).get("archive_sha256") == receipt["archive_sha256"]):
                raise ValueError("full official terminal report does not agree")
            receipt["terminal_reports_agree"] = True
        verify_inputs(launch)
        load_runtime(runtime_path, require_member=False)
        receipt["routing"] = check_routes(runtime)
        boundary = check_boundary(runtime, require_member=False)
        if counters(boundary.get("cgroup.events", "")).get("populated") != 0:
            raise ValueError("verification left live descendants in the bounded slice")
        if counters(boundary.get("memory.events.local", "")).get("oom_kill", 0):
            raise ValueError("aggregate slice suffered an OOM kill")
        if not boundary.get("memory.peak", "").isdigit():
            raise ValueError("aggregate memory peak is unavailable")
        receipt.update(state="passed", passed=True, proof_execution_performed=launch["mode"] == "full")
    except BaseException as error:
        receipt.update(state="failed", passed=False, error=f"{type(error).__name__}: {error}")
        print(receipt["error"], file=sys.stderr, flush=True)
    finally:
        # Retain aggregate counters before stopping the slice removes its cgroup.
        if runtime is not None:
            receipt["final_boundary_before_cleanup"] = read_cgroup(Path(runtime["cgroup"]))
        cleanup = []
        if created:
            for command in ([SYSTEMCTL, "--user", "stop", launch["slice"]],
                            [SYSTEMCTL, "--user", "revert", launch["slice"]]):
                try:
                    cleanup.append({"command": [str(x) for x in command], "output": call(command), "passed": True})
                except Exception as error:
                    cleanup.append({"command": [str(x) for x in command], "passed": False,
                                    "error": f"{type(error).__name__}: {error}"})
                    receipt.update(state="failed", passed=False)
        if process is not None and process.poll() is None:
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=10)
        receipt["cleanup"] = cleanup
        for number, handler in old_handlers.items():
            signal.signal(number, handler)
        for key, file in (("execution_sha256", output / "execution.json"),
                          ("local_execution_sha256", work / "local-execution.json"),
                          ("route_log_sha256", output / "scope-routes.jsonl"),
                          ("capacity_sha256", output / "capacity.json"),
                          ("observations_sha256", output / "aggregate-observations.jsonl")):
            if file.is_file():
                receipt[key] = base.digest(file)
        receipt.update(finished_at=base.now(), seconds=round(time.time() - started, 3))
        base.write_json(report_path, receipt)
    return 0 if receipt["passed"] else 1


def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--work-dir", type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--probe", action="store_true", help="only official delegation/capacity probes, no Lean run")
    mode.add_argument("--run", action="store_true", help="full verification, foreground controller")
    mode.add_argument("--launch", action="store_true", help="full verification, detached controller service")
    return parser.parse_args()


def main():
    if len(sys.argv) >= 3 and sys.argv[1] in {"--route-scope", "--capacity-child", "--worker", "--controller"}:
        action, path = sys.argv[1], Path(sys.argv[2])
        if action == "--route-scope":
            return route_scope(path, sys.argv[3:])
        if len(sys.argv) != 3:
            raise ValueError("internal mode takes one manifest path")
        return {"--capacity-child": capacity_child, "--worker": worker, "--controller": controller}[action](path)
    args = arguments()
    launch = preflight(args.config, args.output_dir, args.work_dir)
    if not (args.probe or args.run or args.launch):
        print(json.dumps(launch, indent=2, sort_keys=True))
        return 0
    if Path("/proc/1/comm").read_text().strip() != "systemd":
        raise ValueError("run the bounded launcher on the systemd host, outside a tool sandbox")
    launch["mode"] = "probe" if args.probe else "full"
    output = Path(launch["output"])
    output.mkdir(parents=True)
    path = output / "launch.json"
    base.write_json(path, launch)
    if args.launch:
        command = [str(SYSTEMD_RUN), "--user", "--unit=" + launch["controller_unit"],
                   "--property=RuntimeMaxSec=" + str(launch["job_timeout_seconds"]),
                   "--property=KillMode=control-group", "--working-directory=" + str(PROJECT),
                   launch["tools"]["python"]["path"], "-B", str(SELF), "--controller", str(path)]
        result = call(command)
        base.write_json(output / "detached-launch.json", {"at": base.now(), "command": command, "output": result})
        print(json.dumps({"state": "launched", "controller_unit": launch["controller_unit"] + ".service",
                          "output": str(output), "work": launch["work"]}, indent=2))
        return 0
    return controller(path)


if __name__ == "__main__":
    raise SystemExit(main())
