#!/usr/bin/env python3
"""Run the pinned local Palomar adapter with candidate24 eight-CPU build and one-CPU con-ron affinity.

This host-side supervisor confines process operations to its own descendants.
The surrounding systemd scope must provide the memory and CPU limits described
in the candidate24 runbook. It does not alter verifier or policy code.
"""

from __future__ import annotations

import argparse
import ctypes
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


PALOMAR_HEAD = "a59f25bd8a66bf6faf3a4f4260d412989c0185ea"
STANDARD_PROFILE = "palomar-standard-v1"
POLL_SECONDS = 0.5
MAX_TIMEOUT_SECONDS = 19_980
DEFAULT_TIMEOUT_SECONDS = 19_800
OUTER_TIMEOUT_MARGIN_SECONDS = 120
OUTER_GUARD_SHUTDOWN_GRACE_SECONDS = 5
SUPERVISOR_TERM_GRACE_SECONDS = 1
SUPERVISOR_KILL_GRACE_SECONDS = 3


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: str | Path) -> str:
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read_json(path: str | Path) -> dict:
    value = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise RuntimeError(f"expected a JSON object in {path}")
    return value


def write_json(path: Path, value: dict) -> None:
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def git(root: Path, *arguments: str) -> str:
    return subprocess.check_output(
        ["git", "-c", "core.hooksPath=/dev/null", "-C", str(root), *arguments],
        text=True,
    ).strip()


def proc_stat(path: str | Path) -> dict | None:
    """Read PID/TID identity; Linux comm may itself contain a closing paren."""
    try:
        raw = Path(path).read_text()
    except (FileNotFoundError, ProcessLookupError):
        return None
    end = raw.rfind(")")
    fields = raw[end + 2 :].split()
    return {
        "pid": int(raw.split(" ", 1)[0]),
        "start_ticks": int(fields[19]),
        "ppid": int(fields[1]),
        "state": fields[0],
    }


def identity(row: dict) -> tuple[int, int]:
    return row["pid"], row["start_ticks"]


def require_binary_identity(actual_path: str | Path, actual_sha: str,
                            expected_path: str | Path, expected_sha: str,
                            label: str) -> None:
    if Path(actual_path).resolve() != Path(expected_path).resolve():
        raise RuntimeError(f"{label} executable path mismatch")
    if actual_sha != expected_sha:
        raise RuntimeError(f"{label} executable digest mismatch")


def require_cpu_mask(actual: set[int], expected: set[int], label: str) -> None:
    if actual != expected:
        raise RuntimeError(f"{label} affinity mismatch: expected {sorted(expected)}, got {sorted(actual)}")


def effective_cpu_quota(rows: list[dict]) -> Fraction:
    """Return the tightest finite quota across this cgroup and its ancestors."""
    capacities = []
    for row in rows:
        raw_quota, raw_period = row["cpu.max"].split()
        period = int(raw_period)
        if period <= 0:
            raise RuntimeError(f"invalid cpu.max period at {row['path']}")
        if raw_quota != "max":
            quota = int(raw_quota)
            if quota <= 0:
                raise RuntimeError(f"invalid cpu.max quota at {row['path']}")
            capacities.append(Fraction(quota, period))
    if not capacities:
        raise RuntimeError("no finite CPU quota found in candidate24 cgroup ancestry")
    return min(capacities)


def require_eight_cpu_ancestry(rows: list[dict]) -> Fraction:
    effective = effective_cpu_quota(rows)
    if effective < 8:
        raise RuntimeError(
            f"effective cgroup CPU quota is {float(effective):.3f}, fewer than eight CPUs"
        )
    return effective


def resource_caps() -> dict:
    if Path("/proc/1/comm").read_text().strip() != "systemd":
        raise RuntimeError("run inside a bounded user systemd scope")
    memberships = [line[3:] for line in Path("/proc/self/cgroup").read_text().splitlines()
                   if line.startswith("0::")]
    if len(memberships) != 1 or ".." in Path(memberships[0]).parts:
        raise RuntimeError("unexpected cgroup-v2 membership")
    membership = Path(memberships[0])
    if not membership.is_absolute() or not membership.name.endswith(".scope") or (
            f"user@{os.getuid()}.service" not in membership.parts):
        raise RuntimeError("a user systemd scope is required")
    root = Path("/sys/fs/cgroup")
    group = root / str(membership).lstrip("/")
    rows = []
    scope_row = None
    while group != root:
        row = {"path": str(group), **{
            name: (group / name).read_text().strip()
            for name in ("memory.max", "memory.high", "memory.swap.max", "cpu.max")
        }}
        rows.append(row)
        if group == root / str(membership).lstrip("/"):
            scope_row = row
        group = group.parent
    finite = [int(row["memory.max"]) for row in rows if row["memory.max"] != "max"]
    if not finite or min(finite) <= 0:
        raise RuntimeError("the outer scope must provide a finite positive memory cap")
    if scope_row is None:
        raise RuntimeError("could not read the active systemd scope limits")
    if int(scope_row["memory.max"]) > 24 * 1024**3:
        raise RuntimeError("candidate24 scope memory.max exceeds 24 GiB")
    if scope_row["memory.high"] == "max" or int(scope_row["memory.high"]) > 23 * 1024**3:
        raise RuntimeError("candidate24 scope must set MemoryHigh at or below 23 GiB")
    if scope_row["memory.swap.max"] != "0":
        raise RuntimeError("candidate24 scope must disable swap")
    cpu_capacity = require_eight_cpu_ancestry(rows)
    affinity = sorted(os.sched_getaffinity(0))
    if len(affinity) != 8:
        raise RuntimeError(f"supervisor must start with exactly eight allowed CPUs, got {affinity}")
    return {
        "cgroup": str(root / str(membership).lstrip("/")),
        "ancestors": rows,
        "effective_memory_max_bytes": min(finite),
        "effective_cpu_quota": f"{cpu_capacity.numerator}/{cpu_capacity.denominator}",
        "available_cpu_affinity": affinity,
    }


class OwnedTree:
    """Track only descendants discovered from this supervisor; defend PID reuse."""

    def __init__(self, emit):
        self.emit = emit
        self.known: dict[int, dict] = {}

    def refresh(self) -> dict[int, dict]:
        todo = [(os.getpid(), None), *((pid, None) for pid in self.known)]
        visited: set[int] = set()
        live: dict[int, dict] = {}
        while todo:
            pid, parent = todo.pop(0)
            if pid in visited:
                continue
            visited.add(pid)
            row = proc_stat(f"/proc/{pid}/stat")
            if row is None or row["state"] == "Z":
                continue
            old = self.known.get(pid)
            if old is not None and identity(old) != identity(row):
                continue
            if pid != os.getpid():
                if old is None:
                    if parent is None:
                        continue
                    parent_now = proc_stat(f"/proc/{parent[0]}/stat")
                    if row["ppid"] != os.getpid() and (
                        row["ppid"] != parent[0] or parent_now is None
                        or identity(parent_now) != parent
                    ):
                        continue
                    try:
                        fd = os.pidfd_open(pid)
                    except ProcessLookupError:
                        continue
                    check = proc_stat(f"/proc/{pid}/stat")
                    if check is None or identity(check) != identity(row) or check["ppid"] not in (
                        parent[0], os.getpid()
                    ):
                        os.close(fd)
                        continue
                    row["pidfd"] = fd
                    self.known[pid] = row
                else:
                    row["pidfd"] = old["pidfd"]
                live[pid] = row
            try:
                tasks = list(Path(f"/proc/{pid}/task").iterdir())
                for task in tasks:
                    check = proc_stat(f"/proc/{pid}/stat")
                    if check is None or identity(check) != identity(row):
                        break
                    try:
                        todo.extend((int(child), identity(row)) for child in
                                    (task / "children").read_text().split())
                    except (FileNotFoundError, ProcessLookupError):
                        pass
            except (FileNotFoundError, ProcessLookupError):
                pass
        for pid in list(self.known):
            if pid not in live:
                os.close(self.known.pop(pid)["pidfd"])
        return live

    @staticmethod
    def threads(row: dict) -> list[Path]:
        try:
            return list(Path(f'/proc/{row["pid"]}/task').iterdir())
        except (FileNotFoundError, ProcessLookupError):
            return []

    @staticmethod
    def current_affinity(row: dict) -> set[int] | None:
        try:
            before = proc_stat(f'/proc/{row["pid"]}/stat')
            if before is None or identity(before) != identity(row):
                return None
            cpus = os.sched_getaffinity(row["pid"])
            after = proc_stat(f'/proc/{row["pid"]}/stat')
            return cpus if after is not None and identity(after) == identity(row) else None
        except ProcessLookupError:
            return None

    def affinity(self, row: dict, cpus: set[int], *, require_inherited: bool = False) -> None:
        for task in self.threads(row):
            thread = proc_stat(task / "stat")
            process = proc_stat(f'/proc/{row["pid"]}/stat')
            if thread is None or process is None or identity(process) != identity(row):
                continue
            tid = thread["pid"]
            try:
                before = os.sched_getaffinity(tid)
                if require_inherited and before != cpus:
                    raise RuntimeError(
                        f"process {row['pid']} did not inherit affinity {sorted(cpus)}"
                    )
                if before == cpus:
                    continue
                check = proc_stat(task / "stat")
                if check is None or identity(check) != identity(thread):
                    continue
                os.sched_setaffinity(tid, cpus)
                check = proc_stat(task / "stat")
                if check is None or identity(check) != identity(thread):
                    continue
                after = os.sched_getaffinity(tid)
                if after != cpus:
                    raise RuntimeError(f"affinity did not take effect for owned thread {tid}")
                self.emit("affinity", pid=row["pid"], start_ticks=row["start_ticks"],
                          tid=tid, thread_start_ticks=thread["start_ticks"],
                          before=sorted(before), after=sorted(after))
            except ProcessLookupError:
                pass

    def assert_affinity(self, row: dict, cpus: set[int]) -> list[dict]:
        """Fail if any live thread in this identity is not on the exact CPU mask."""
        expected_tids: set[int] | None = None
        for _ in range(3):
            tasks = self.threads(row)
            tids = {int(task.name) for task in tasks}
            observations = []
            for task in tasks:
                thread = proc_stat(task / "stat")
                process = proc_stat(f'/proc/{row["pid"]}/stat')
                if thread is None or process is None or identity(process) != identity(row):
                    continue
                actual = os.sched_getaffinity(thread["pid"])
                require_cpu_mask(actual, cpus,
                                 f"thread {thread['pid']} of process {row['pid']}")
                check = proc_stat(task / "stat")
                if check is None or identity(check) != identity(thread):
                    raise RuntimeError("thread identity changed during NanoDa affinity check")
                observations.append({"tid": thread["pid"], "start_ticks": thread["start_ticks"],
                                     "affinity": sorted(actual)})
            current = {int(task.name) for task in self.threads(row)}
            if current == tids:
                if len(observations) != len(tids):
                    raise RuntimeError("could not verify every live NanoDa thread")
                return observations
            expected_tids = current
        raise RuntimeError(
            f"thread set for NanoDa {row['pid']} did not stabilize during affinity check: {expected_tids}"
        )

    def cleanup(self) -> list[dict]:
        """Terminate only identities in this supervisor's descendant tree."""
        # Stay inside guarded-build's five-second outer process-group grace.
        # This lets us kill any detached-but-owned child and write the receipt
        # before the outer guard escalates its group to SIGKILL.
        for signum, seconds in (
            (signal.SIGTERM, SUPERVISOR_TERM_GRACE_SECONDS),
            (signal.SIGKILL, SUPERVISOR_KILL_GRACE_SECONDS),
        ):
            deadline = time.monotonic() + seconds
            signaled: set[tuple[int, int]] = set()
            while True:
                live = self.refresh()
                if not live:
                    return []
                for row in live.values():
                    key = identity(row)
                    if key in signaled:
                        continue
                    try:
                        signal.pidfd_send_signal(row["pidfd"], signum)
                        self.emit("cleanup-signal", pid=row["pid"],
                                  start_ticks=row["start_ticks"], signal=int(signum))
                    except ProcessLookupError:
                        pass
                    signaled.add(key)
                if time.monotonic() >= deadline:
                    break
                time.sleep(0.1)
        return [{"pid": row["pid"], "start_ticks": row["start_ticks"]}
                for row in self.refresh().values()]


def executable(row: dict) -> str | None:
    try:
        path = os.readlink(f'/proc/{row["pid"]}/exe')
        current = proc_stat(f'/proc/{row["pid"]}/stat')
        return path if current is not None and identity(current) == identity(row) else None
    except (FileNotFoundError, ProcessLookupError):
        return None


def restricted_descendants(live: dict[int, dict], roots: set[tuple[int, int]]) -> set[int]:
    narrow = {pid for pid, row in live.items() if identity(row) in roots}
    while True:
        children = {pid for pid, row in live.items() if row["ppid"] in narrow}
        if children <= narrow:
            return narrow
        narrow |= children


def phase_decision(mode: str, stage: str | None, conron_seen: bool) -> str:
    """Pure stage policy, separated for isolated tests."""
    if mode == "eight":
        if stage in ("comparator", "complete"):
            raise RuntimeError("missed solution-export; one-worker inheritance is unproven")
        return "pin-one" if stage == "solution-export" else "keep-eight"
    if mode == "one":
        return "restore-eight" if conron_seen else "keep-one"
    if mode == "restored":
        return "keep-phases"
    raise RuntimeError(f"unknown affinity mode {mode!r}")


class AffinityPlan:
    def __init__(self, eight: set[int], checker_cpu: int, checker_sha: str,
                 nanoda_path: Path, nanoda_sha: str, emit):
        self.eight = set(eight)
        if checker_cpu not in self.eight:
            raise ValueError("checker CPU must belong to the eight-CPU build mask")
        self.one = {checker_cpu}
        self.checker_sha = checker_sha
        self.nanoda_path = nanoda_path.resolve()
        self.nanoda_sha = nanoda_sha
        self.emit = emit
        self.mode = "eight"
        self.narrow: set[tuple[int, int]] = set()
        self.observed: set[tuple[int, int]] = set()
        self.seen_conron: set[tuple[int, int]] = set()
        self.conron_seen = False
        self.nanoda_seen = False
        self.nanoda_instances: dict[tuple[int, int], dict] = {}
        self.export_seen = False

    def update(self, tree: OwnedTree, stage: str | None) -> None:
        live = tree.refresh()
        names = {pid: executable(row) for pid, row in live.items()}
        action = phase_decision(self.mode, stage, self.conron_seen)
        if action == "keep-eight":
            # comparator-preflight may run a smoke checker; it is not the main replay.
            for row in live.values():
                tree.affinity(row, self.eight)
            self.observed.update(identity(row) for row in live.values())
            return
        if action == "pin-one":
            for _ in range(3):
                live = tree.refresh()
                for row in live.values():
                    if Path(executable(row) or "").name == "con-ron":
                        raise RuntimeError("main con-ron started before one-CPU export pin")
                    tree.affinity(row, self.one)
            self.export_seen = True
            self.mode = "one"
            self.emit("solution-export-pinned", stage=stage, one_cpu=sorted(self.one))
            names = {pid: executable(row) for pid, row in live.items()}
        elif action == "restore-eight":
            self.mode = "restored"
            self.emit("restore-eight", eight_cpus=sorted(self.eight),
                      excluded="main con-ron and owned descendants")

        for pid, row in live.items():
            name = Path(names.get(pid) or "").name
            key = identity(row)
            if name == "con-ron" and key not in self.seen_conron:
                if self.mode != "one":
                    raise RuntimeError("con-ron appeared outside the one-CPU phase")
                tree.affinity(row, self.one, require_inherited=True)
                if digest(f'/proc/{pid}/exe') != self.checker_sha:
                    raise RuntimeError("owned con-ron executable digest mismatch")
                current = proc_stat(f"/proc/{pid}/stat")
                if current is None or identity(current) != key:
                    continue
                self.seen_conron.add(key)
                self.narrow.add(key)
                self.conron_seen = True
                self.emit("con-ron-observed", pid=pid, start_ticks=row["start_ticks"],
                          executable=names[pid], sha256=self.checker_sha,
                          inherited_cpus=sorted(self.one))

        # Restore in the same poll where the exact checker is first observed;
        # this lets a subsequent NanoDa process inherit eight CPUs even when
        # the checker phase is short.
        if self.mode == "one" and self.conron_seen:
            self.mode = "restored"
            self.emit("restore-eight", eight_cpus=sorted(self.eight),
                      excluded="main con-ron and owned descendants")

        if self.mode == "restored":
            for row in live.values():
                key = identity(row)
                if key not in self.observed and row["ppid"] == os.getpid():
                    # Preserve a one-CPU checker child adopted by our subreaper
                    # between polls, even if its original parent has exited.
                    if tree.current_affinity(row) == self.one:
                        self.narrow.add(key)
                        self.emit("retain-one-cpu-adopted-child", pid=row["pid"],
                                  start_ticks=row["start_ticks"])

        restricted = restricted_descendants(live, self.narrow)
        self.narrow.update(identity(live[pid]) for pid in restricted)
        nanoda_pids = set()
        for pid, row in live.items():
            name = Path(names.get(pid) or "").name
            key = identity(row)
            if name == "nanoda_bin":
                require_binary_identity(names[pid], digest(f'/proc/{pid}/exe'),
                                        self.nanoda_path, self.nanoda_sha, "NanoDa")
                if self.mode != "restored" or pid in restricted:
                    raise RuntimeError("NanoDa appeared before restoring the eight-CPU mask")
                if key not in self.nanoda_instances:
                    tree.affinity(row, self.eight, require_inherited=True)
                    self.nanoda_instances[key] = {
                        "pid": pid, "start_ticks": row["start_ticks"],
                        "executable": names[pid], "sha256": self.nanoda_sha,
                        "affinity_samples": 0, "first_seen_at": now(),
                        "last_seen_at": None, "thread_counts": [],
                    }
                thread_observations = tree.assert_affinity(row, self.eight)
                sample = self.nanoda_instances[key]
                sample["affinity_samples"] += 1
                sample["last_seen_at"] = now()
                thread_ids = [{"tid": item["tid"], "start_ticks": item["start_ticks"]}
                              for item in thread_observations]
                identities_changed = sample.get("thread_identities") != thread_ids
                sample["thread_identities"] = thread_ids
                sample["thread_counts"].append(len(thread_observations))
                sample["thread_mask_sha256"] = hashlib.sha256(
                    json.dumps(thread_observations, sort_keys=True, separators=(",", ":")).encode()
                ).hexdigest()
                nanoda_pids.add(pid)
                self.nanoda_seen = True
                self.emit("nanoda-affinity-verified", pid=pid, start_ticks=row["start_ticks"],
                          executable=names[pid], sha256=self.nanoda_sha,
                          verified_cpus=sorted(self.eight), thread_count=len(thread_observations),
                          thread_identities=thread_ids if identities_changed else None,
                          thread_mask_sha256=sample["thread_mask_sha256"],
                          sample=sample["affinity_samples"])
            cpus = self.one if self.mode == "one" or pid in restricted else self.eight
            if pid not in nanoda_pids:
                tree.affinity(row, cpus)
        self.observed.update(identity(row) for row in live.values())


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--adapter", type=Path, required=True)
    result.add_argument("--archive", type=Path, required=True)
    result.add_argument("--expect-sha256", required=True)
    result.add_argument("--archive-gate", type=Path, required=True)
    result.add_argument("--policy-tree", type=Path, required=True)
    result.add_argument("--work-dir", type=Path, required=True)
    result.add_argument("--report", type=Path, required=True,
                        help="adapter receipt; its live mechanical report is work-dir/local-execution.json")
    result.add_argument("--bwrap", type=Path, required=True)
    result.add_argument("--licensee", type=Path, required=True)
    result.add_argument("--checker-executable", type=Path, required=True)
    result.add_argument("--nanoda-executable", type=Path, required=True)
    result.add_argument("--execution-budget-seconds", type=int, default=19_800)
    result.add_argument("--checker-cpu", type=int, required=True)
    result.add_argument("--build-cpus", type=int, choices=(8,), default=8,
                        help="must be eight; the inherited taskset mask identifies the CPUs")
    result.add_argument("--supervisor-report", type=Path, required=True)
    result.add_argument("--timeout-seconds", type=int, default=DEFAULT_TIMEOUT_SECONDS)
    result.add_argument("--execute", action="store_true", required=True)
    return result


def main() -> int:
    args = parser().parse_args()
    adapter = args.adapter.resolve(strict=True)
    archive = args.archive.resolve(strict=True)
    gate_path = args.archive_gate.resolve(strict=True)
    policy = args.policy_tree.resolve(strict=True)
    work = args.work_dir.resolve()
    adapter_receipt = args.report.resolve()
    supervisor_receipt = args.supervisor_report.resolve()
    bwrap = args.bwrap.resolve(strict=True)
    licensee = args.licensee.resolve(strict=True)
    checker = args.checker_executable.resolve(strict=True)
    nanoda = args.nanoda_executable.resolve(strict=True)
    live_report = work / "local-execution.json"
    if work.exists() or live_report.exists():
        raise SystemExit(f"Refusing to overwrite existing work directory: {work}")
    if adapter_receipt.exists() or supervisor_receipt.exists():
        raise SystemExit("Refusing to overwrite existing receipts")
    if not adapter_receipt.parent.is_dir() or not supervisor_receipt.parent.is_dir():
        raise SystemExit("Create the new candidate24 receipt directory before launch")
    if args.execution_budget_seconds < 1 or args.execution_budget_seconds > 19_800:
        raise SystemExit("Execution budget must be between 1 and 19,800 seconds")
    if not 60 <= args.timeout_seconds <= MAX_TIMEOUT_SECONDS - OUTER_TIMEOUT_MARGIN_SECONDS:
        raise SystemExit(
            f"Supervisor timeout must be 60..{MAX_TIMEOUT_SECONDS - OUTER_TIMEOUT_MARGIN_SECONDS} "
            f"seconds to leave {OUTER_TIMEOUT_MARGIN_SECONDS}s for outer cleanup"
        )
    if len(args.expect_sha256) != 64 or any(c not in "0123456789abcdef" for c in args.expect_sha256):
        raise SystemExit("--expect-sha256 must be 64 lowercase hexadecimal characters")
    if git(policy, "rev-parse", "HEAD") != PALOMAR_HEAD:
        raise SystemExit(f"policy tree must be exactly {PALOMAR_HEAD}")
    if git(policy, "status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("policy tree must be clean")
    if digest(archive) != args.expect_sha256:
        raise SystemExit("archive SHA-256 differs from --expect-sha256")
    gate = read_json(gate_path)
    if not (gate.get("state") == "passed" and gate.get("passed") is True
            and gate.get("deterministic_archive") is True
            and gate.get("sources_unchanged") is True
            and gate.get("archive_sha256") == args.expect_sha256
            and gate.get("policy_tree") == str(policy)):
        raise SystemExit("candidate24 archive gate receipt does not bind a passed exact archive")
    checker_sha = digest(checker)
    nanoda_sha = digest(nanoda)
    if checker.name != "con-ron" or not os.access(checker, os.X_OK):
        raise SystemExit("checker executable is not executable")
    if nanoda.name != "nanoda_bin" or not os.access(nanoda, os.X_OK):
        raise SystemExit("NanoDa executable must be the executable toolchain nanoda_bin")
    adapter_text = adapter.read_text(encoding="utf-8")
    if f'PALOMAR_HEAD = "{PALOMAR_HEAD}"' not in adapter_text or (
        f'STANDARD_PROFILE = "{STANDARD_PROFILE}"' not in adapter_text
    ):
        raise SystemExit("adapter source does not declare the pinned current policy and Standard profile")
    policy_verifier = (policy / "scripts" / "verify_submission.py").read_text(encoding="utf-8")
    policy_babysitter = (policy / "scripts" / "supervise_cgroup.py").read_text(encoding="utf-8")
    if '"--die-with-parent"' not in policy_verifier or "PR_SET_PDEATHSIG" not in policy_babysitter:
        raise SystemExit("pinned verifier no longer provides parent-death cleanup for isolated sandbox children")

    allowed = set(os.sched_getaffinity(0))
    if len(allowed) != args.build_cpus or args.checker_cpu not in allowed:
        raise SystemExit(f"inherited affinity must be exactly eight CPUs and include checker CPU; got {sorted(allowed)}")
    eight = allowed
    one = {args.checker_cpu}
    gate_sha = digest(gate_path)
    adapter_sha = digest(adapter)
    bwrap_sha = digest(bwrap)
    licensee_sha = digest(licensee)
    try:
        caps = resource_caps()
    except Exception as error:
        raise SystemExit(f"resource preflight failed: {error}") from error

    # Orphaned adapter/verifier children must remain discoverable by this process.
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0) != 0:  # PR_SET_CHILD_SUBREAPER
        raise OSError(ctypes.get_errno(), "PR_SET_CHILD_SUBREAPER failed")

    record = {
        "schema": "candidate24-eight-cpu-phase-aware-supervisor-v1",
        "state": "preflight",
        "started_at": now(),
        "supervisor_pid": os.getpid(),
        "supervisor_process_group": os.getpgrp(),
        "supervisor_sha256": digest(__file__),
        "adapter": str(adapter),
        "adapter_sha256": adapter_sha,
        "archive": str(archive),
        "archive_sha256": args.expect_sha256,
        "archive_gate": str(gate_path),
        "archive_gate_sha256": gate_sha,
        "policy_tree": str(policy),
        "policy_commit": PALOMAR_HEAD,
        "execution_profile": STANDARD_PROFILE,
        "work_dir": str(work),
        "adapter_receipt": str(adapter_receipt),
        "live_execution_report": str(live_report),
        "supervisor_receipt": str(supervisor_receipt),
        "checker_executable": str(checker),
        "checker_sha256": checker_sha,
        "nanoda_executable": str(nanoda),
        "nanoda_sha256": nanoda_sha,
        "bwrap_sha256": bwrap_sha,
        "licensee_sha256": licensee_sha,
        "eight_cpus": sorted(eight),
        "conron_cpus": sorted(one),
        "execution_budget_seconds": args.execution_budget_seconds,
        "timeout_seconds": args.timeout_seconds,
        "poll_seconds": POLL_SECONDS,
        "resource_caps": caps,
        "local_only": True,
        "remote_submission": False,
    }
    event_path = supervisor_receipt.with_name("affinity-events.jsonl")
    event_log = event_path.open("x", encoding="utf-8")

    def save() -> None:
        write_json(supervisor_receipt, record)

    def emit(event: str, **details) -> None:
        event_log.write(json.dumps({"at": now(), "event": event, **details}, sort_keys=True) + "\n")
        event_log.flush()

    tree = OwnedTree(emit)
    child: subprocess.Popen | None = None
    interrupted: list[int] = []
    for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(signum, lambda sig, _frame: interrupted.append(sig))
    save()
    plan = AffinityPlan(eight, args.checker_cpu, checker_sha, nanoda, nanoda_sha, emit)
    started = time.monotonic()
    try:
        if interrupted:
            raise InterruptedError(f"received signal {interrupted[0]}")
        command = [
            sys.executable, "-u", str(adapter),
            "--archive", str(archive),
            "--expect-sha256", args.expect_sha256,
            "--policy-tree", str(policy),
            "--work-dir", str(work),
            "--report", str(adapter_receipt),
            "--bwrap", str(bwrap),
            "--licensee", str(licensee),
            "--execution-budget-seconds", str(args.execution_budget_seconds),
            "--execute",
        ]
        record.update(state="running", command=command)
        emit("launch", command=command, eight_cpus=sorted(eight), one_cpu=sorted(one),
             archive_sha256=args.expect_sha256, policy_commit=PALOMAR_HEAD)
        save()
        adapter_log = supervisor_receipt.with_name("adapter.log")
        with adapter_log.open("x", encoding="utf-8") as log:
            child = subprocess.Popen(
                command,
                cwd=adapter.parents[2],
                stdout=log,
                stderr=subprocess.STDOUT,
                preexec_fn=lambda: os.sched_setaffinity(0, eight),
            )
            record["adapter_pid"] = child.pid
            adapter_pgid = os.getpgid(child.pid)
            record["adapter_process_group"] = adapter_pgid
            if adapter_pgid != os.getpgrp():
                raise RuntimeError("adapter escaped the supervisor process group")
            save()
            stage = None
            report_error_since = None
            while child.poll() is None:
                if interrupted:
                    raise InterruptedError(f"received signal {interrupted[0]}")
                if time.monotonic() - started > args.timeout_seconds:
                    raise TimeoutError("candidate24 verification exceeded supervisor timeout")
                try:
                    report = read_json(live_report) if live_report.exists() else {}
                    report_error_since = None
                except (FileNotFoundError, json.JSONDecodeError) as error:
                    if report_error_since is None:
                        report_error_since = time.monotonic()
                        emit("live-report-read-retry", error=str(error))
                    if time.monotonic() - report_error_since > 30:
                        raise RuntimeError("local-execution.json unreadable for 30 seconds") from error
                    report = {"stage": stage}
                current_stage = report.get("stage")
                if current_stage != stage:
                    stage = current_stage
                    record["last_stage"] = stage
                    emit("stage", stage=stage, report=str(live_report))
                    save()
                plan.update(tree, stage)
                time.sleep(POLL_SECONDS)
        record["adapter_exit_code"] = child.returncode
        if not adapter_receipt.is_file() or not live_report.is_file():
            raise RuntimeError("adapter exited without both terminal receipts")
        adapter_result = read_json(adapter_receipt)
        execution_result = read_json(live_report)
        record["adapter_state"] = adapter_result.get("state")
        record["adapter_passed"] = adapter_result.get("passed")
        record["execution_status"] = execution_result.get("status")
        record["execution_stage"] = execution_result.get("stage")
        record["adapter_receipt_sha256"] = digest(adapter_receipt)
        record["live_execution_report_sha256"] = digest(live_report)
        record["adapter_log"] = str(adapter_log)
        record["adapter_log_sha256"] = digest(adapter_log)
        if adapter_result.get("archive_sha256") != args.expect_sha256:
            raise RuntimeError("terminal adapter receipt archive hash mismatch")
        if adapter_result.get("palomar_submission_commit") != PALOMAR_HEAD:
            raise RuntimeError("terminal adapter receipt policy commit mismatch")
        if adapter_result.get("execution_profile") != STANDARD_PROFILE:
            raise RuntimeError("terminal adapter receipt profile mismatch")
        if adapter_result.get("local_only") is not True or adapter_result.get("remote_submission") is not False:
            raise RuntimeError("adapter receipt is not explicitly local-only")
        if adapter_result.get("execution_status") != "pass" or execution_result.get("status") != "pass":
            raise RuntimeError("terminal adapter/mechanical status is not pass")
        if adapter_result.get("state") != "passed" or adapter_result.get("passed") is not True:
            raise RuntimeError("terminal adapter receipt is not passed")
        if adapter_result.get("execution_report") != str(live_report):
            raise RuntimeError("adapter receipt points at an unexpected execution report")
        if execution_result.get("stage") != "complete":
            raise RuntimeError("terminal mechanical report stage is not complete")
        if not plan.export_seen or not plan.conron_seen or not plan.nanoda_seen:
            raise RuntimeError("missing required solution-export, con-ron, or NanoDa phase evidence")
        if any(item["affinity_samples"] < 2 for item in plan.nanoda_instances.values()):
            raise RuntimeError("NanoDa did not remain observable for two affinity samples")
        if child.returncode != 0:
            raise RuntimeError(f"adapter exited {child.returncode}")
        if digest(archive) != args.expect_sha256 or digest(gate_path) != gate_sha:
            raise RuntimeError("archive or gate receipt changed during verification")
        if digest(checker) != checker_sha:
            raise RuntimeError("con-ron executable changed during verification")
        if digest(nanoda) != nanoda_sha:
            raise RuntimeError("NanoDa executable changed during verification")
        if digest(adapter) != adapter_sha:
            raise RuntimeError("adapter source changed during verification")
        if git(policy, "rev-parse", "HEAD") != PALOMAR_HEAD or git(
            policy, "status", "--porcelain", "--untracked-files=all"
        ):
            raise RuntimeError("pinned policy tree changed during verification")
        record.update(state="passed", conron_observed_on_one_cpu=True,
                      nanoda_observed_on_eight_cpus=True,
                      nanoda_instances=list(plan.nanoda_instances.values()),
                      archive_unchanged=True, policy_unchanged=True,
                      checker_unchanged=True, adapter_unchanged=True)
    except Exception as error:
        record.update(state="failed", error=f"{type(error).__name__}: {error}")
    finally:
        try:
            survivors = tree.cleanup()
        except Exception as error:
            survivors = [{"cleanup_error": f"{type(error).__name__}: {error}"}]
        record["cleanup_survivors"] = survivors
        record["nanoda_instances"] = list(plan.nanoda_instances.values())
        if survivors:
            record.update(state="failed", cleanup_error="owned processes survived SIGKILL grace")
        if child is not None:
            record["adapter_exit_code"] = child.poll()
        record["finished_at"] = now()
        emit("finished", state=record["state"], cleanup_survivors=survivors)
        event_log.close()
        record["affinity_events"] = str(event_path)
        record["affinity_events_sha256"] = digest(event_path)
        save()
    print(f'{record["state"]}: {supervisor_receipt}', flush=True)
    return 0 if record["state"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
