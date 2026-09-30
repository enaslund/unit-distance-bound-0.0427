# Reproducing the conditional package checks

A verification receipt applies to the archive SHA-256 it records. Including
a script, receipt or NanoDa option in a source archive does not establish a
new verification result. Records distinguish completed, failed and interrupted
attempts; only files in a sealed archive's snapshot are its payload. No
official Palomar report or editorial outcome is claimed.

## Current source and verifier, September 29, 2026

The inspected PalomarSubmission revision is
`65f0154ed776cd26c224254aa57b379137f28b0d`. The source pins
`leanprover/lean4:v4.35.0-rc2` and canonical Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. A versioned shared Lean installation
can serve multiple project folders; each project selects its exact version
through `lean-toolchain`.

Use that pinned official verifier for the full protected pipeline. All checks
remain required, including both external kernels and Lean replay. Its execution
budget is 19,800 seconds. Source integrity or imported axiom queries alone do
not replace the protected export comparison and its fresh axiom traversal.

The [September 29 proof refactor](HOSTED_RESOURCE_REPAIR_20260929.md) explains
the source change and the separate hosted-capacity tests. The selected source
snapshot is frozen before the new full run; later receipts must identify its
exact archive and source hashes. The earlier full local success applies only
to the preceding archive and does not establish hosted fit for this one.

The following material preserves earlier dated reproduction records. Its old
host resource settings, paths and verifier pins are historical context, not
the configuration for a new run.

## Historical entrypoints, checked September 27, 2026

The current inspected verifier is PalomarSubmission
`a59f25bd8a66bf6faf3a4f4260d412989c0185ea`, with local checkout
`.cache/upstream/PalomarSubmission-current-20260925-pinned`. It requires Lean
at least `v4.35.0-rc2`. These are dated pins, not a promise that upstream will
remain unchanged. [STATUS.md](../STATUS.md) records the selected package and
the latest verification state. A running attempt is not a pass.

| Entrypoint | Supported scope |
| --- | --- |
| `scripts/check-metadata.py` | Current pinned metadata contract and direct Challenge import/size checks. Its default checkout and commit are the September 25 path and `a59f25…` pin above. It does not compile or check proofs. |
| `scripts/verify-zeta-candidate.py --check-only` | Archive integrity, deterministic re-export, and metadata checks. Supply both the current `--policy-tree` and `--policy-revision` explicitly. Its older default tree is retained while the running verifier imports this helper. |
| `scripts/verify-zeta-candidate.py` without `--check-only` | A separate source build and imported-axiom audit. It is not the full protected Palomar verifier or independent kernel replay. Its dependency cache needs separate toolchain/source validation. |
| `verification/conditional-20260925/verify-current-palomar-local.py` | Current pinned local preparation adapter, with full protected execution only when `--execute` is supplied. Execution needs the host cgroup context and coordinated resource supervision. |
| `verification/conditional-candidate24-20260927/run-candidate24-eight-cpu-supervised.py` | Resource and process supervisor used by the current C24 full run. It preserves the current adapter and mandatory checks. The direct launcher beside it claims one authorized attempt and must not be reused to queue duplicates. |
| `scripts/verify-palomar-local.py` and `scripts/setup-verification-tools.sh` | Historical September 21 implementation and standalone tool pins for verifier `3561d237…`. They do not run or install the current verifier toolchain. |
| `verification/conditional-20260923/verify-current-palomar-local.py` | Historical adapter for the September 23/24 pin `1703d7ba…`. The word `current` in its filename describes that checkpoint. |

From `lean-formalization`, the current metadata check is:

```sh
PYTHONPATH=.cache/policy-python python3 -B scripts/check-metadata.py
```

This workspace's `.cache/policy-python` provides the policy's pinned PyYAML
6.0.3. A fresh checkout should install the exact policy `requirements.txt` in
an isolated Python environment and use that interpreter instead. The checker
selects `formalization-zeta.yaml` in the research checkout and
`formalization.yaml` in an extracted selected package. A historical check
must provide both `--policy-tree` and `--revision`, since the default is the
newer inspected pin.

An archive-only check of a new source archive uses fresh output paths:

```sh
python3 -B scripts/verify-zeta-candidate.py \
  --archive /absolute/path/source.tar.gz \
  --work-dir /absolute/path/new-archive-check \
  --report /absolute/path/new-archive-check.json \
  --check-only \
  --policy-tree .cache/upstream/PalomarSubmission-current-20260925-pinned \
  --policy-revision a59f25bd8a66bf6faf3a4f4260d412989c0185ea
```

For full verification on this eight-CPU host, the current adapter explicitly
selects `palomar-standard-v1`. The default upstream Namespace profile needs
16 effective CPUs and at least 28 GiB effective memory. Current verification
includes structural comparison, permitted-axiom checks, Lean replay, con-ron,
and NanoDa. The Standard execution budget remains 19,800 seconds. Preparation
or archive checks do not establish any of those proof results. Follow the
current supervised run's resource plan rather than adding `--execute` to an
old command without a host guard and the shared build lock.

The fresh C24 full attempt begun at 23:12:54 UTC is recorded under
[`standard-full-direct-20260927T231254Z`](../verification/conditional-candidate24-20260927/standard-full-direct-20260927T231254Z/RESOURCE_PLAN.md).
Its terminal supervisor, adapter, and mechanical receipts determine the
outcome. Neither its launch nor any earlier interrupted comparator run is a
verification pass. A complete pass would still be for the theorem conditional
on the explicit fixed-field hypothesis H.

## Historical package checkpoint, September 27, 2026 at 08:04 UTC

At the 08:04 UTC package checkpoint, candidate23's deterministic source export
and archive-only metadata gate passed. The archive is
[`conditional-source-23-final.tar.gz`](../dist/conditional-candidate23-20260927/conditional-source-23-final.tar.gz),
SHA-256 `a8b47796a275a598e2be85c9f6d4e28b560782047b4b7d6e8ea6c5c3f3d7132d`. The
[export receipt](../verification/conditional-candidate23-20260927/candidate23-export.json)
records 2,163 project modules and zero missing references. The
[archive-gate receipt](../verification/conditional-candidate23-20260927/candidate23-archive-check.json)
records deterministic archive and source checks passed, metadata exit 0 under
PalomarSubmission revision
`a59f25bd8a66bf6faf3a4f4260d412989c0185ea`, and no proof verification.
Candidate22's archive-only gate also passed. Candidate21's preserved archive
gate failed metadata because its wrapper omitted the explicit policy revision;
see its [failed receipt](../verification/conditional-candidate21-20260927/candidate21-archive-check.json).

Candidate20's isolated retry2 ended at 07:11:55 UTC with exit 75 at
148,000/149,249 con-ron checks, after the host guard measured 3.423931 GiB
available (<3.5 GiB). The cgroup peak was 12,768,038,912 bytes and OOM
counters were zero. The [retry receipt](../verification/conditional-20260927/retry-20260927-retry2/retry.json)
and [replay receipt](../verification/conditional-20260927/conron-one-worker-20260927-retry2/replay.json)
record an infrastructure-stopped incomplete replay; the owner released the
reservation at 07:11:55.554731 UTC. Retry1 had failed before checker startup
because its scope lacked `cpu.max`. Neither retry produced a kernel verdict;
retry2 did not start the full verifier. Candidate23 has only archive and
metadata checks at this checkpoint. No full verifier or H proof pass is
claimed. Historical status sections below retain their dates and scope.

## Historical verifier route, September 24, 2026

Archive 17 is the prior sealed package with a completed deterministic export,
SHA-256
`3e369cb1cdc367fbb396946b9b69c1898a99d69cbb534b9b0d5ebe8cc29f1672`.
Its [candidate record](../verification/conditional-20260923/candidate17-packaging-preparation.md)
reports passed deterministic archive/snapshot and metadata checks, exact
selected-proof-input identity with archive 07, all 17 extracted finite scripts,
and two extracted 128-mask genus/atom checks. These are post-export checkout
records, not members of archive 17. No full verifier replay ran on archive 17.
The [September 23 handoff](FINAL_HANDOFF_SOL_LUNA_20260923.md) records its
scope and open work. Any later Lean 4.35 candidate needs its own selected
build, archive, current metadata and verifier receipts. This embedded account
does not claim a current verifier pass.

At that September 24 checkpoint, the public PalomarSubmission pin was
`1703d7babd984ccc3831cdf89c28221abe34808f`; its supported Lean floor is
`v4.35.0-rc2`. The package at archive 17 pins `v4.32.0`, so it is below that
floor. The [archive-17 current-policy smoke](../verification/conditional-20260923/current-policy-smoke-17-head1703.json)
reaches the toolchain policy check and returns `toolchain.unsupported` before
proof compilation, Comparator or kernel replay. The
[compatibility assessment](../verification/conditional-20260923/current-policy-compatibility.md)
and [migration assessment](../verification/conditional-20260923/toolchain-migration-assessment.md)
record the migration requirement. A successful build or verifier run for a
migrated archive must be assessed from its separate exact-digest receipt.

At that checkpoint, metadata checking used the following pin. To reproduce
that historical check with today's wrapper, pass the old revision explicitly:

```sh
python3 scripts/check-metadata.py \
  --policy-tree .cache/upstream/PalomarSubmission-current-20260923-pinned \
  --revision 1703d7babd984ccc3831cdf89c28221abe34808f \
  --metadata formalization-zeta.yaml
```

The recorded root-metadata check passed the current metadata contract and
direct Challenge size/import checks. To check an exact extracted candidate
metadata file, pass it as another `--metadata` value; do so only after the
archive has been produced and its source snapshot checked. The checker accepts
an explicit `--revision` for historical reproductions.

That verifier's hosted `prepare` command requires a public repository
and commit, so an unpublished migration archive cannot use that intake path.
The local-only adapter at
[`verification/conditional-20260923/verify-current-palomar-local.py`](../verification/conditional-20260923/verify-current-palomar-local.py)
binds the archive SHA, extracts and checks its source snapshot, creates a
synthetic local Git commit, and invokes the pinned current `prepare()`
validators with only the GitHub checkout callback replaced. It marks its
receipt and report as local and does not create a Palomar submission ID. With
`--execute`, it calls the unmodified current `execute` command only after the
official cgroup bootstrap succeeds.

Inside the Codex sandbox, the standard profile's memory and workspace checks
and a `/usr/bin/bwrap` 0.12.0 namespace smoke passed, but the current cgroup
bootstrap failed: PID 1 was `codex`, the `sudo` helper was blocked by `no new
privileges`, and there was no systemd user bus. The actual host was tested
separately on September 24. Its exact pinned
[`supervisor_bootstrap()` probe](../verification/conditional-20260924/host-bootstrap-20260924.json)
passed with PID 1 `systemd` and selected `systemd-run --user --scope
--property=Delegate=yes`; the probe ran only `/usr/bin/true`. This establishes
the host bootstrap route, not a full candidate execution. Preparation-only
mode still runs the archive and metadata validators and records cgroup status
as untested. Bubblewrap version alone does not prove its build provenance;
use a binary built by the pinned current installer for an execution attempt.

To run the local preparation adapter after a migrated archive exists, source
the task-local Ruby environment so current Palomar's locked SPDX detector can
run, then substitute the archive digest and a pinned Bubblewrap path:

```sh
source .cache/conditional-20260921/ruby/env.sh
python3 verification/conditional-20260923/verify-current-palomar-local.py \
  --archive /absolute/path/migrated-source.tar.gz \
  --expect-sha256 <64-lowercase-hex-digest> \
  --policy-tree .cache/upstream/PalomarSubmission-current-20260923-pinned \
  --work-dir /absolute/path/fresh-current-local-work \
  --report /absolute/path/fresh-current-local-receipt.json \
  --bwrap /absolute/path/pinned-bubblewrap-0.12.0 \
  --licensee .cache/conditional-20260921/ruby/gems/bin/bundle
```

This command performs current preparation only. Add `--execute` to attempt the
full current verifier on the host; the September 24 bootstrap probe supports
that route but does not predict its build or proof result. Running the same
command inside the Codex sandbox still fails at cgroup bootstrap. Neither a
local preparation receipt nor a local execution result is an official Palomar
workflow report or registry decision.

Archive 07's full local pass below is evidence for the **older pinned
implementation** and for byte-identical selected proof inputs in archive 17.
The following pins and commands reproduce that historical setup only; they do
not reproduce current PalomarSubmission.

## Historical policy and tool pins

Pins used for the historical local verifier, checked on September 21, 2026:

- [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md): `792c7c0b9e798bd02719e795ef11fa2b5929e067`.
- [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/tree/3561d237dcc4b28482558ad28a64d767d7cc8615): `3561d237dcc4b28482558ad28a64d767d7cc8615`.
- Profile: `palomar-standard-v1`, execution budget 19,800 seconds, fresh
  submitted `.lake` state, authenticated pinned Mathlib cache when available.
- Lean: `leanprover/lean4:v4.32.0`; Mathlib:
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Comparator: `575674928e239f5bc452aab72d1dd7b0f1326494` (its own toolchain is
  Lean `v4.34.0-rc1`). NanoDa: `68d5ca9db226849b41a6fff59d796ff19d0a8840`.
- Landrun: `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`.
- Exporter matching the submitted Lean: `4e7915201d3f9f04470d9eae002fa695f7cdc589`.

Tool binaries are trusted inputs built from those revisions, and their exact
hashes are recorded. The setup script builds these public pins; Git, elan,
Cargo and Go must already be installed. Keep tools and verification work on
disk outside `/tmp`: the pinned verifier uses systemd `PrivateTmp`.

```sh
bash scripts/setup-verification-tools.sh
git clone https://github.com/PalomarRegistry/PalomarSubmission.git .cache/palomar
git -C .cache/palomar checkout --detach 3561d237dcc4b28482558ad28a64d767d7cc8615
python3 -m venv .cache/palomar-python
.cache/palomar-python/bin/python -m pip install --require-hashes -r .cache/palomar/requirements.txt
.cache/palomar-python/bin/python scripts/check-metadata.py --policy-tree .cache/palomar \
  --revision 3561d237dcc4b28482558ad28a64d767d7cc8615 --metadata formalization.yaml
```

The root license is Apache-2.0. To run the policy's exact SPDX detector,
install Ruby and Bundler `2.7.2`, then run `bundle install` with
`BUNDLE_GEMFILE` set to the pinned policy's `Gemfile`. Pass that Bundler
executable with `--licensee` below. Omitting the option explicitly leaves
the detector check unperformed in the local receipt; a separate detector
receipt can bind the same root-license hash.

## Ordinary source build and complete owned-declaration audit

From an extracted package, with the pinned Lean available through elan:

```sh
lake exe cache get
lake build +ChallengeZeta:olean +SolutionZeta:olean +AuditSupport:olean
lake env lean -DstderrAsMessages=false verification/ZetaAudit.lean
```

This audit checks every imported declaration owned by a `UnitDistance` module,
including private helpers and ports in other namespaces, and every submission
wrapper declaration. It rejects an empty selection and any transitive axiom
outside the three allowed axioms. It is not independent kernel replay.

## Historical local execution using the September 21 implementation

The historical `scripts/verify-palomar-local.py` runner validates and extracts the immutable archive into a new
directory, creates a local Git snapshot, checks the metadata/configuration and
source constraints, then invokes the unmodified pinned
`scripts/verify_submission.py execute`. That implementation downloads and
authenticates the public dependencies, obtains the Mathlib cache, compiles
the Challenge using only canonical permitted dependencies, protects its
artifacts and configuration, and invokes stock Comparator with NanoDa enabled.
The verifier performs filesystem/network confinement probes, comparison,
axiom checking, Lean kernel replay and quotient checks.

The local preparation step replaces remote intake for a local run. It does
not fake a public repository, GitHub workflow or submission identifier. The
standard execution code and its resource limits are unchanged. The host is
recorded; running locally does not reproduce the identity of Palomar's
hosted runner. For the pinned verifier, a working Linux systemd manager and
Landrun confinement are required. The runner fails if confinement fails.

With absolute paths substituted for the source archive, an unused work
directory and an unused receipt path:

```sh
.cache/palomar-python/bin/python scripts/verify-palomar-local.py \
  --archive /absolute/path/conditional-source.tar.gz \
  --work-dir /absolute/path/fresh-verification \
  --report /absolute/path/local-execution-receipt.json \
  --policy-tree .cache/palomar \
  --comparator .cache/verification-tools/comparator/.lake/build/bin/comparator \
  --lean4export .cache/verification-tools/lean4export/.lake/build/bin/lean4export \
  --nanoda .cache/verification-tools/nanoda/target/release/nanoda_bin \
  --landrun .cache/verification-tools/bin/landrun
```

The final JSON must say `passed: true`, and its embedded execution report
must say `status: pass`. An exit code alone is insufficient because the
upstream verifier reports proof/infrastructure failures through JSON.
Successful execution does not prove the numerical hypothesis (H).

## Packaging and publication boundary

`scripts/export-zeta-candidate.py` writes a deterministic source archive.
It selects the complete local import closure, attribution, an independent
Challenge, one configuration and focused submission documentation. It includes
no compiled artifacts, dependency checkouts, symlinks or private tool paths.
`SELECTION.json` records source origins, and `SOURCE_SNAPSHOT.json` hashes
every payload file. Re-exporting an intact extraction gives the same archive.

The locally tested subject is the source archive. A proposed public commit
needs to match its payload, and a new submission needs current public policy
checks. Publishing a repository, providing a public 40-character commit,
requesting Palomar verification and registration are separate actions.
A local pass does not establish editorial suitability, human proof review or
registration. No such remote action is claimed here.

## Local verification record, September 22, 2026

The pinned verifier (PalomarSubmission `3561d237dcc4b28482558ad28a64d767d7cc8615`,
Comparator `575674928e239f5bc452aab72d1dd7b0f1326494`, NanoDa
`68d5ca9db226849b41a6fff59d796ff19d0a8840`, Landrun
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, standard profile, execution
budget 19,800 seconds, Licensee detector included) was run locally on the
source archive `conditional-source-07.tar.gz`, SHA-256
`f5bfc2e50e6432af0d6dfccf26801bf1de6d147f42cb6b037478e0b40c3ccd0a`. The
receipt `verification/conditional-20260922/standard-07.json`
records `passed: true` with embedded execution status `pass`: Mathlib
cache obtained, canonical Challenge isolated, statement and permitted-axiom
comparison, NanoDa acceptance, Lean kernel acceptance and the quotient
post-check, in 11,378 seconds end to end (Comparator phase 11,047 seconds,
38,485 CPU-seconds, process peak 7.75 GiB) on an 8-CPU, 31 GiB host shared
with other builds; the host conditions are in
`verification/conditional-20260922/host-conditions.txt`.
Companion records: `verification/conditional-20260922/export-07.json`,
`verification/conditional-20260922/test-export-07.json`,
`verification/conditional-20260922/intake-07.json` and
`verification/conditional-20260922/policy-recheck.json`.

Archive 17's exact selected-proof-input comparison with archive 07 is
recorded in its candidate record above. This preserves the scope of the old
receipt; it is not a new execution on archive 17 or a proof of H. The observed
hosted runner at the time had 4 CPUs and about 15.6 GiB of memory. The local
timing establishes completion on the recorded local host, not timing on that
hosted profile or its later replacements.
