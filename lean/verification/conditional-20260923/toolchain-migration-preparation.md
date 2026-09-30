# Candidate14 v4.35.0-rc2 migration preparation

## Isolated copy

The sealed archive was left untouched. Its extracted project copy is at
`lean-formalization/.cache/build-tmp/conditional14-v435-migration/unit-distance-zeta/`.
The working main project toolchain and Lake files were not changed.

Applied only these compatibility edits in that copy:

- `lean-toolchain`: `leanprover/lean4:v4.32.0` → `leanprover/lean4:v4.35.0-rc2`.
- `lakefile.toml`: Mathlib revision → exact tag commit
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
- `lake-manifest.json`: Mathlib and all eight transitive dependencies were set
  to the exact revisions recorded in Mathlib's `v4.35.0-rc2` manifest. A
  source comparison confirms all nine package names agree and all revisions
  match that release closure.
- `IwasawaIndexing.lean`: changed the removed import
  `Mathlib.Logic.Denumerable` to `Mathlib.Basic.Denumerable`.
- `SELECTION.json`: updated its recorded external import name for that one
  relocated module.

The extracted historical docs, receipts, and `SOURCE_SNAPSHOT.json` still
refer to the sealed v4.32 candidate; this directory is a compile probe, not a
new export or package candidate.

## Checks so far

This section records the source-only preparation before the staged acquisition
and probe documented below.

- Candidate14 archive SHA-256 before extraction:
  `4d4e657cbb557049b1d8281321941c1940053af40a2669d0435ed5388b500199`.
- New `lake-manifest.json` revisions match the Mathlib v4.35.0-rc2 release
  manifest plus its exact Mathlib commit.
- Previously queried Mathlib v4.35.0-rc2 source tree contains all candidate
  recorded external imports after the one path change. The relocated module
  contains `Denumerable`, `nonempty_denumerable`, and `Denumerable.eqv`, which
  are the declarations used by `IwasawaIndexing.lean`.
- No Lake update, toolchain installation, cache download, build, or proof edit
  has been performed in this preparation step.

## Build status and scale

The following was the pre-acquisition status; see the staged receipts below
for the later task-local install and leaf compile.

The required Lean v4.35.0-rc2 toolchain is not installed in the shared local
`.elan` directory; only Lean v4.32.0 and v4.34.0-rc1 were found there. Thus an
incremental probe still requires making the v4.35 release binary and Mathlib
artifacts available. I have not started that work or any compile because the
parent requested explicit coordination for the single expensive slot.

At this preparation stage, a successful minimal compile of `IwasawaIndexing.lean`
was still pending. The later leaf compile establishes that the known import
repair and this module's nearby Mathlib API surface work. It does not establish
viability of the full closure: candidate14 has 2,163 project modules and 704
other Mathlib import paths, and API/tactic changes may surface later.
Archive07's prior full v4.32 verifier run took 11,378 seconds within a 19,800
second budget; candidate14 proof inputs match archive07, but that timing does
not predict a v4.35 rebuild.

At planning time, any compile was to use the master guard with the shared lock
`/tmp/lean-formalization-1000.build.lock`, inherited TMPDIR and threshold
settings, serial Lean `-j1 -M2560`, and parent coordination. The staged check
later found that Lean 4.35's Lake 5 CLI rejects `lake build -j1`; see the
execution receipts below. No full closure result is claimed here.

## Independent local availability and probe review before acquisition (September 23)

The following records the pre-acquisition source review; the final staged
outcome and updated limits appear later in this note.

At the time of this pre-acquisition check, I checked the isolated extraction
and host-visible Lean locations without starting Lake or Lean. The migration copy has no `.lake` directory or package
checkout. `lean`, `lake`, and `elan` are not on this shell's `PATH`; I found no
v4.35 executable under `/home/naslund_eric/.elan/toolchains` or the shared
toolchain locations I searched. The earlier preparation record says v4.32.0
and v4.34.0-rc1 were found in a shared `.elan` directory, but neither exposes
a v4.35 toolchain here. The workspace's
`.cache/relocated-dependency-cache/mathlib` resolves to the project workspace
itself and contains no Mathlib sources or build artifacts. At that time there
was no usable local v4.35.0-rc2 toolchain/Mathlib cache to test against; the
later task-local installation and cache receipts are documented below.

The smallest meaningful first Lean probe identified at that point was the
changed module itself:

```text
UnitDistance/Upstream/Yamaguchi/ValuedFieldTheory/LocalField/DiscreteValuationField/IwasawaIndexing.lean
```

The proposed probe was to compile that single source with
`lake env lean -j1 -M2560`. It exercises the relocated Denumerable import and
the class/instance/projection APIs actually used by that file while avoiding
the much larger `ChallengeZeta` closure. The command must run through the
master guard with `/tmp/lean-formalization-1000.build.lock`, host admission/stop
thresholds 10/6 GiB, cgroup admission/stop thresholds 1/0.5 GiB, inherited
TMPDIR, and explicit parent coordination. This leaf has since passed as
recorded below. At preflight, the next informative probe was identified as
`ChallengeZeta.lean`; it is not a small probe because it recursively loads
the selected project closure.

Concrete blockers and remaining uncertainties at preflight (updated status
below):

- **Pre-acquisition environment blocker:** neither the new compiler nor its
  dependency/cache was then present in the local environment, so no compile
  could be launched in that extracted copy at that time.
- **Likely cache/resource blocker:** without a matching prebuilt Mathlib cache,
  Lake would need substantial dependency compilation under the 4 GiB cgroup
  ceiling. The single-module source probe is only small if those imports are
  already cached; otherwise dependency preparation itself is the expensive
  work that needs coordination.
- **Known source repair:** the removed `Mathlib.Logic.Denumerable` import was
  redirected to `Mathlib.Basic.Denumerable`. At this preflight point import
  resolution and the downstream proof were untested; the later leaf compile
  verifies the migrated module's import and proof.
- **Project-wide API risk:** all other candidate import paths being present
  does not prove declaration or tactic compatibility. The first probe covers
  one leaf. `ChallengeZeta` is needed to surface issues in the selected
  theorem closure, and the full verifier must be rerun on the matched pins
  before any migrated candidate is reviewable as verified.

No Lean/Lake process, toolchain installation, cache download, or compile was
started for this review. Per-worker CPU and memory usage is unavailable (no
worker/build metrics were collected); it is not reported as zero.

## Resource-bounded setup plan (September 23)

### Toolchain layout and writable destination

There is a reusable project-local `.toolchain` convention: the live
`lean-formalization/.toolchain` symlink points to the shared Lean 4.32.0
installation in the Sarkozy repository's `.elan/toolchains`; export tests
reuse that symlink. The corresponding shared `.elan/bin/elan` is available at
`/home/naslund_eric/src/enaslund/sarkozy-lower-bound/master/lean-formalization/.elan/bin/elan`.
The existing Lean 4.32.0 and 4.34.0-rc1 toolchain directories occupy 2.8 GiB
and 2.9 GiB on disk. The current Mathlib dependency/cache tree for v4.32
occupies 1.3 GiB total (the Mathlib package directory is about 1.2 GiB).
The migration extraction is 39 MiB. The workspace filesystem currently has
about 73 GiB free.

The shared `.elan` installation is outside this task's writable roots, so do
not install v4.35 there or retarget the live `.toolchain` symlink. Use the
ignored migration directory under the writable workspace instead:

```text
MIGRATION_ROOT=/home/naslund_eric/src/enaslund/unit-distance-bound/master/lean-formalization/.cache/build-tmp/conditional14-v435-migration/unit-distance-zeta
MIGRATION_TASK_CACHE=/home/naslund_eric/src/enaslund/unit-distance-bound/master/lean-formalization/.cache/build-tmp/conditional14-v435-migration
LOCAL_ELAN_HOME=$MIGRATION_TASK_CACHE/elan
SHARED_ELAN_BIN=/home/naslund_eric/src/enaslund/sarkozy-lower-bound/master/lean-formalization/.elan/bin/elan
MASTER_GUARD=/home/naslund_eric/src/enaslund/unit-distance-bound/master/automation/lean-formalization/guarded_build.py
```

The Lean 4.35.0-rc2 release is published by Lean and Mathlib's matching tag
resolves to commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The exact
matching toolchain and Mathlib pin are already in the migration copy. Lean's
official release page does not expose a retrievable asset size through the
read-only source inspection here. For planning, reserve at least 3.5 GiB for
one Lean toolchain plus a temporary compressed archive: the installed 4.32
and 4.34 toolchains are 2.8/2.9 GiB, and the precise v4.35 archive/expanded
size remains unmeasured. Reserve a further 1.5 GiB for a full Mathlib plus
transitive dependency cache, using the current 1.3 GiB v4.32 dependency cache
as a rough proxy. A cautious peak-disk reservation is 5 GiB, leaving over
68 GiB on the measured workspace filesystem. A targeted two-module cache for
the first probe should need less, but its size is not known in advance.

The 4 GiB cgroup maximum is a memory ceiling, separate from those disk figures;
the run's 3 GiB high watermark, no-swap policy, and 150% CPU limit still apply.
For each potentially expensive installation/fetch/probe stage, use the shared
guard with host admission/stop thresholds 10/6 GiB, cgroup headroom thresholds
1/0.5 GiB, `LEAN_NUM_THREADS=1`, serial `lake -j1` where supported, Lean
`-j1 -M2560`, and `TMPDIR=$MIGRATION_TASK_CACHE/tmp` on the disk-backed
workspace filesystem. Actual peak RAM for elan unpack, cache decompression, and
the first cache-client build has not been measured. The guard must defer or
stop at its configured thresholds; do not weaken them to force admission.

### Commands, after explicit slot coordination

### Staging recheck before acquisition (September 23)

While waiting for the shared guarded-build slot, I rechecked only the isolated
migration workspace. Its local ELAN home and `.toolchain` link are both absent,
so the planned installation destinations are clean. The pinned
`lake-manifest.json` currently has SHA-256
`9bbd672bbae0f6311af4b33fc6928e391aa4962a17b9c0fb9b4e5db5e486b932`; this is
the pre-`lake update` value to compare against after package hydration. The
backing `/dev/sdb1` filesystem had 73 GiB available at this check. These are
disk/workspace observations only: no compiler, Lake command, network download,
cache retrieval, or build has run yet, and cgroup admission is still pending.

These are proposed commands only; no install, dependency fetch, or cache
download was run for this plan. From the master workspace root, prepare the
task-local directories and install the pinned Lean release into a task-local
Elan home. The source binary is the pre-existing Elan launcher; downloaded
compiler artifacts come from Lean's official release channel:

```sh
mkdir -p "$MIGRATION_TASK_CACHE/tmp" "$LOCAL_ELAN_HOME"
TMPDIR="$MIGRATION_TASK_CACHE/tmp" python3 "$MASTER_GUARD" \
  --lock-path /tmp/lean-formalization-1000.build.lock \
  --wait-seconds 60 --timeout-seconds 900 \
  --min-available-gib 10 --stop-below-gib 6 \
  --min-cgroup-available-gib 1 --stop-cgroup-below-gib 0.5 -- \
  env ELAN_HOME="$LOCAL_ELAN_HOME" \
  "$SHARED_ELAN_BIN" toolchain install leanprover/lean4:v4.35.0-rc2
```

Then create a candidate-local `.toolchain` link (after confirming the
destination does not already exist) and check the version without invoking
Lake:

```sh
ln -s "$LOCAL_ELAN_HOME/toolchains/leanprover--lean4---v4.35.0-rc2" \
  "$MIGRATION_ROOT/.toolchain"
"$MIGRATION_ROOT/.toolchain/bin/lean" --version
```

With the exact manifest already pinned, use `lake update` only to hydrate its
nine package checkouts, suppressing Mathlib's automatic post-update cache
fetch so that download is a separate guarded step. Run it from the migration
copy and compare `lake-manifest.json` to its pre-command checksum; the
recorded package revisions must remain unchanged:

```sh
cd "$MIGRATION_ROOT"
TMPDIR="$MIGRATION_TASK_CACHE/tmp" python3 "$MASTER_GUARD" \
  --lock-path /tmp/lean-formalization-1000.build.lock \
  --wait-seconds 60 --timeout-seconds 900 \
  --min-available-gib 10 --stop-below-gib 6 \
  --min-cgroup-available-gib 1 --stop-cgroup-below-gib 0.5 -- \
  env ELAN_HOME="$LOCAL_ELAN_HOME" \
  PATH="$MIGRATION_ROOT/.toolchain/bin:$PATH" \
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
```

For the first, narrow probe, fetch the two Mathlib import roots from
`IwasawaIndexing.lean`; Mathlib documents `lake exe cache get` as its supported
precompiled `.olean` retrieval mechanism and accepts file paths for narrower
retrieval:

```sh
TMPDIR="$MIGRATION_TASK_CACHE/tmp" python3 "$MASTER_GUARD" \
  --lock-path /tmp/lean-formalization-1000.build.lock \
  --wait-seconds 60 --timeout-seconds 900 \
  --min-available-gib 10 --stop-below-gib 6 \
  --min-cgroup-available-gib 1 --stop-cgroup-below-gib 0.5 -- \
  env ELAN_HOME="$LOCAL_ELAN_HOME" \
  PATH="$MIGRATION_ROOT/.toolchain/bin:$PATH" \
  lake exe cache get \
    Mathlib/NumberTheory/Padics/RingHoms.lean \
    Mathlib/Topology/Homeomorph/Lemmas.lean
```

Validate cache completeness for those import roots with a no-build check, then
compile only the patched project leaf:

```sh
TMPDIR="$MIGRATION_TASK_CACHE/tmp" python3 "$MASTER_GUARD" \
  --lock-path /tmp/lean-formalization-1000.build.lock \
  --wait-seconds 60 --timeout-seconds 900 \
  --min-available-gib 10 --stop-below-gib 6 \
  --min-cgroup-available-gib 1 --stop-cgroup-below-gib 0.5 -- \
  env ELAN_HOME="$LOCAL_ELAN_HOME" \
  PATH="$MIGRATION_ROOT/.toolchain/bin:$PATH" \
  lake build --no-build \
    Mathlib.NumberTheory.Padics.RingHoms \
    Mathlib.Topology.Homeomorph.Lemmas

TMPDIR="$MIGRATION_TASK_CACHE/tmp" python3 "$MASTER_GUARD" \
  --lock-path /tmp/lean-formalization-1000.build.lock \
  --wait-seconds 60 --timeout-seconds 900 \
  --min-available-gib 10 --stop-below-gib 6 \
  --min-cgroup-available-gib 1 --stop-cgroup-below-gib 0.5 -- \
  env ELAN_HOME="$LOCAL_ELAN_HOME" \
  PATH="$MIGRATION_ROOT/.toolchain/bin:$PATH" \
  lake env lean -j1 -M2560 \
    UnitDistance/Upstream/Yamaguchi/ValuedFieldTheory/LocalField/DiscreteValuationField/IwasawaIndexing.lean
```

If the leaf passes, fetching all Mathlib imports in the selected proof closure
(or the full Mathlib cache) and then compiling `ChallengeZeta.lean` is a
separate, larger stage; do not infer full-candidate viability from the leaf.
For a full upstream Mathlib cache rather than the leaf's two import roots, the
official cache client can be asked for its default full cache with the same
guard and environment:

```sh
TMPDIR="$MIGRATION_TASK_CACHE/tmp" python3 "$MASTER_GUARD" \
  --lock-path /tmp/lean-formalization-1000.build.lock \
  --wait-seconds 60 --timeout-seconds 900 \
  --min-available-gib 10 --stop-below-gib 6 \
  --min-cgroup-available-gib 1 --stop-cgroup-below-gib 0.5 -- \
  env ELAN_HOME="$LOCAL_ELAN_HOME" \
  PATH="$MIGRATION_ROOT/.toolchain/bin:$PATH" \
  lake exe cache get
```

This larger fetch is unnecessary for the first leaf probe; use it only after
coordination if broader closure compilation is authorized.

### Pre-acquisition cache availability and evidence limits

The Mathlib v4.35.0-rc2 release tag and matching source commit can be checked
from official Git metadata without installing Lean. That does not establish
that the central precompiled cache has every `.olean` needed by this exact tag.
The documented cache client is a Lean/Lake executable tied to the matching
toolchain/dependency graph; no local manifest-only or pre-install check found
here can prove cache completeness. A successful targeted `cache get` plus
`lake build --no-build` is the first concrete test for the leaf imports. A
successful full `cache get` plus no-build checks over the selected Mathlib
imports would verify cache coverage, while a normal candidate build is still
needed for local source/API compatibility. Partial cache hits are possible;
if required artifacts are missing, compilation would fall back to building
them and must remain under the same 4 GiB guard.

Primary sources: [Lean v4.35.0-rc2 release](https://github.com/leanprover/lean4/releases/tag/v4.35.0-rc2),
[Elan toolchain manager](https://github.com/leanprover/elan),
[Mathlib v4.35.0-rc2 release](https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0-rc2),
[Mathlib dependency/cache instructions](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency),
[Mathlib cache implementation entry point](https://github.com/leanprover-community/mathlib4/blob/v4.35.0-rc2/lakefile.lean).

## Staged execution receipts (September 23)

All acquisition and compile commands used the master
`automation/lean-formalization/guarded_build.py` with the shared lock
`/tmp/lean-formalization-1000.build.lock`, 900 second command timeout, host
admission/stop thresholds 10/6 GiB, and cgroup admission/stop thresholds
1/0.5 GiB. `TMPDIR` and the Mathlib cache directory were placed under this
migration task directory. No toolchain, cache, manifest, or source changes were
made outside the isolated migration copy. The live selected tree and sealed
candidate15 were not edited.

| Stage | Admission (host / cgroup headroom) | Result |
|---|---:|---|
| Install official Lean 4.35.0-rc2 into task-local ELAN home | 15.6 / 1.58 GiB | Exit 0; release toolchain installed |
| `lake update` with automatic cache hook disabled | 15.4 / 1.12 GiB | Exit 0; nine package revisions match the recorded pins |
| Cache client, first invocation with bare `Mathlib/...` paths | 15.7 / 1.14 GiB | Exit 1 after building its 42/42 Cache targets; paths were relative to the wrong cwd; no download |
| Cache retrieval with source paths but default cache directory | 16.0 / 1.40 GiB | Exit 1 before transfer; default `/home/naslund_eric/.cache/mathlib` is read-only |
| Targeted cache retrieval with task-local `MATHLIB_CACHE_DIR` | 15.4 / 1.25 GiB | Exit 0; 2,016 artifacts downloaded/decompressed; two misses warned |
| `lake build --no-build` for the two roots | 15.9 / 1.10 GiB | Exit 3; `Homeomorph.Lemmas` cached, `RingHoms` needs local compilation |
| Attempted `lake build -j1 ...` | 15.4 / 1.03 GiB | Exit 1 before compilation: Lake 5.0 reports unknown `-j` option |
| Direct guarded Lean compile of Mathlib `RingHoms.lean` (`-j1 -M2560`) | 14.4 / 1.05 GiB | Exit 0; wrote `RingHoms.olean` to Mathlib's build path |
| Direct guarded Lean compile of `IwasawaIndexing.lean` (`-j1 -M2560`) | 14.2 / 1.43 GiB | Exit 0 |

The standalone cache client was therefore usable from the downstream Lake
workspace, but its path arguments had to be prefixed with
`.lake/packages/mathlib/`. Mathlib documents `MATHLIB_CACHE_DIR`; setting it to
the isolated task-local directory avoided writes to the read-only default
cache. The cache endpoint returned 2,016 of 2,018 requested files for the
two-root import closure; two files were missing from both attempted cache
endpoints. The one required direct import without a cache artifact,
`RingHoms`, was successfully compiled with the matching Lean binary. The
project leaf then elaborated successfully against that artifact and the
cached `Homeomorph.Lemmas` and `Basic.Denumerable` artifacts. Its proof/API
surface and relocated import are checked by Lean; this is not a Lake-tracked
project build and does not verify any parent module.

Lake 5.0.0-src in this release does not accept `lake build -j1`; its local
`lake build --help` contains no jobs option. To keep the leaf test truly serial
and pass Lean's 2,560 MiB memory cap, the two successful checks used direct
`lake env lean -j1 -M2560` invocations. `lake --help` identified the installed
Lake version as 5.0.0-src+11acb17, paired with Lean 4.35.0-rc2 commit
`11acb17ec6b07a8f9e9173e6845197929540936b`.

Measured task-local storage after these stages: the installed toolchain is
3.0 GiB; `.lake/packages` is 2.4 GiB, including about 1.3 GiB of Mathlib Lean
artifacts; compressed targeted cache files occupy 127 MiB (2,016 `.ltar`
files). The backing workspace filesystem had 67 GiB free at the final check.
SHA-256 receipts:

| File | SHA-256 |
|---|---|
| Migration `lake-manifest.json` | `66e692fad41bf0fb95f43659f47145ca4b1aed36100d15e6d5c1f425049e7b47` |
| Migration `lean-toolchain` | `8dc8d6f560141069d9073e370611716ef77ada0da8ffa37e2149f44b2e63ac7a` |
| `IwasawaIndexing.lean` source | `dd4604febcebeca14f66af4e17516478ade192ab2126a8fdbf40d01fb3ef467f` |
| Mathlib `RingHoms.lean` source | `93ba84a94f41b266b73aaaab58a34982d0cb61cfb5bea592d05cb01ab31113c6` |
| compiled Mathlib `RingHoms.olean` | `dd343f3273392a48120d5dccce8b459850c5f8af190318207843eb96c65fd8b7` |
| cached Mathlib `Homeomorph.Lemmas.olean` | `6fb35552f9023f038abac27608673a3e84fa1bb2dd1f0b3bdc8643facb601aa8` |
| cached Mathlib `Basic.Denumerable.olean` | `ac9b595e2fe350d82f7e16ad6a29635d199f8f717ac6325102edf6f379c48817` |

The post-update manifest serialization hash differs from the pre-update hash,
but inspection confirmed all nine package revision hashes are unchanged,
including Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Package checkouts
were created only in this isolated copy. The two cache setup failures above
were respectively a working-directory error and a read-only default cache
path; neither indicates toolchain or proof failure.

Per-worker CPU time and peak RSS are unavailable: the guard reports admission
headroom and timeout but does not produce process-specific usage data, and no
per-worker accounting was collected during these completed runs. This is
unavailable, not zero. The headroom values in the table are guard snapshots,
not measurements of peak use.

### Full closure implications and limits

The candidate14 inventory has 2,163 project modules and 704 distinct Mathlib
import paths in the selected source closure. The present evidence covers just
one patched project leaf plus two direct Mathlib roots and their 2,018-file
cache closure. In that small closure, cache artifacts were sufficient except
for one direct root that compiled successfully within the guard. This is
encouraging for targeted testing, but it does not establish how many unique
Mathlib modules or project modules the full `ChallengeZeta.lean` closure will
need, whether other cache misses will compile under 4 GiB, or whether APIs and
tactics match throughout.

Any further bounded probe, after a separate run-level decision, should target
a larger import aggregation or selected proof module and first resolve the
supported Lake job-control mechanism. The complete candidate verifier is a
separate job: the prior v4.32 archive07 verifier took 11,378 seconds, but that
old run is not a v4.35 runtime prediction. A full cache fetch is not justified
by the successful leaf. No broader build was attempted here, and the run-level
assessment below advises against starting one before the current deadline.

## Current remaining-work inventory and deadline assessment (September 23)

I compared the migrated copy's `SELECTION.json` direct import paths with actual
`.olean` files after the focused cache fetch; this was a filesystem-only check,
not a build or another cache request. Of the 705 selected Mathlib external
direct imports, 201 currently have `.olean` artifacts and 504 do not. Cache
coverage does include thousands of transitive artifacts, so these direct-root
counts are not counts of every missing dependency. By top-level Mathlib area,
the currently unavailable direct roots are: RingTheory 111, Analysis 90,
NumberTheory 57, Algebra 44, FieldTheory 43, Topology 40, MeasureTheory 33,
LinearAlgebra 23, RepresentationTheory 17, Data 16, GroupTheory 16, Tactic 5,
CategoryTheory 4, Combinatorics 2, and one each in AlgebraicTopology, Dynamics,
and Probability.

For `ChallengeZeta.lean`'s 11 direct Mathlib roots, only
`Mathlib.Data.Finset.Prod` and `Mathlib.Order.Filter.AtTopBot.Tendsto` are
currently cached. Missing root artifacts are:

```text
Mathlib.Analysis.Calculus.LogDeriv
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.CStarAlgebra.Classes
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.AlgebraicTopology.SimplexCategory.Basic
Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
Mathlib.NumberTheory.Harmonic.EulerMascheroni
Mathlib.NumberTheory.NumberField.DedekindZeta
```

The scoped migration tree has no project `.olean` artifacts for its 2,163
selected project modules. Within Mathlib's package build directory there are
1,778 `.olean` files; dependency package artifact counts are LeanSearchClient 4,
Qq 14, aesop 132, batteries 193, importGraph 10, plausible 13, and proofwidgets
10 (Cli 0). These counts do not establish that all transitive requirements of
the full selected closure are present. The targeted cache closure fetched
2,016 compressed artifacts and expanded to about 1.3 GiB of Mathlib Lean
artifacts. A full migration would need at least the missing selected import
roots supplied from cache or compiled, then a serial local build of the
selected project closure (2,163 project modules), compatibility repairs as
discovered, and a fresh axiom/full-verifier pass.

### Feasibility judgment for this run

The source change itself is feasible: one relocated import was repaired and
the affected leaf compiles on Lean 4.35.0-rc2. A **fully verified current-policy
candidate is infeasible to complete responsibly in this run** under the
current 4 GiB memory ceiling, 150% CPU limit, shared serialized slot, and
14:41:17 UTC deadline. This is a run-specific resource/time judgment, not a
claim that the migration is technically impossible in general. The available
evidence is still only one leaf; at least 504 selected direct Mathlib roots
lack artifacts, 2,163 selected project modules have no built outputs in this
copy, and no full-closure v4.35 memory or runtime has been measured. The old
archive07 11,378-second v4.32 verifier run is not a safe estimate for this
larger-cache/new-toolchain build under the present local cap and queue. No
ChallengeZeta/full-cache action should be started in this run.

Keep candidate identities and proof receipts separate. Candidate 15 is the
frozen archive SHA-256
`7585c6dcd7806503237142df9a8544561a08d2cb9291e684991981d6b6cf4632`; its
recorded full proof-input comparison is byte identity with archives 14 and 07,
and its own current-policy smoke is `toolchain.unsupported` because the
package remains pinned to Lean 4.32.0. The prior full verifier receipt is for
archive07's old-pinned Lean 4.32/Mathlib set. The Lean 4.35.0-rc2 result above
is a direct leaf compile in a separate candidate14 migration scratch copy,
with the Mathlib pin changed and one import path edited. It neither upgrades
candidate 15 nor transfers the archive07 full-verification receipt to a
migrated candidate. A successor current-policy candidate would need its own
frozen export and full matched-pin verifier/audit receipt.
