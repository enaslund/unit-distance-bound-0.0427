# Source-only assessment: candidate14 on current Palomar Lean floor

**Dated scope, superseded in part.** This note records the source-only view
before toolchain acquisition. The later
[migration preparation record](toolchain-migration-preparation.md) reports a
guarded direct Lean `v4.35.0-rc2` compile of the patched `IwasawaIndexing`
leaf in an isolated candidate14 scratch copy. That check validates this one
import repair. The selected 2,163-module closure, candidate15 migration and
current-policy verifier remain untested; the later record gives the resource
assessment for this run.

## Conclusion

A migration looks **source-level feasible but untested**. The required Lean release candidate is published, and Mathlib has a matching `v4.35.0-rc2` tag whose `lean-toolchain` names the same Lean version. All 11 direct Mathlib imports in `ChallengeZeta.lean` exist in that tag. I also checked all 705 Mathlib module paths in candidate14's recorded external import set: 704 still exist under their recorded names. The sole missing path is a removed/relocated import, `Mathlib.Logic.Denumerable`, used by one retained local module. The matching release contains `Mathlib.Basic.Denumerable`, with the `Denumerable` class and `nonempty_denumerable` used there, so the source-level repair appears small.

This is not a compatibility or compilation result. The one import path must change, the package toolchain and Mathlib/transitive manifest pins must be moved together, and a fresh complete verifier run is required. API/elaboration changes elsewhere across a 2,163-module project closure remain untested.

## Pins and compatibility evidence

Candidate14 archive `conditional-source-14.tar.gz` is SHA-256 `4d4e657cbb557049b1d8281321941c1940053af40a2669d0435ed5388b500199`. Its root `lean-toolchain` is `leanprover/lean4:v4.32.0`; its Lake file pins Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`. The current PalomarSubmission checkout is exactly `e48a86d0495356b5131a92c9406aa6e27cf99e56`; its execution profile sets trusted toolchain floor `v4.35.0-rc2`. The current namespace profile provides 16 CPUs, 32 GiB, and 19,800 seconds.

Official release metadata confirms Lean `v4.35.0-rc2` is published, and Mathlib's corresponding release tag is published. The Mathlib tag's `lean-toolchain` is `leanprover/lean4:v4.35.0-rc2`; its release commit is `065356127b1dc0016f66b7283ce0ce2c4055aa55`. I queried that commit's complete Git tree (10,640 paths, not truncated) and compared it with the package's recorded module names:

- All 11 `ChallengeZeta.lean` direct Mathlib imports are present.
- Of 705 Mathlib paths in `SELECTION.json`'s external import set, 704 are present at the same path. The only missing path is `Mathlib.Logic.Denumerable`.
- The other three recorded core imports (`Lean.Elab.Command`, `Lean.Elab.Tactic.Omega`, `Lean.Util.CollectAxioms`) are present in the matching Lean release tree.
- `IwasawaIndexing.lean` imports the missing module and uses `Denumerable`, `nonempty_denumerable`, and `Denumerable.eqv`. The v4.35.0-rc2 Mathlib tree has `Mathlib/Basic/Denumerable.lean`; source inspection confirms those names are declared there. Replacing the import path is therefore a plausible compatibility fix, but has not been compiled.

Primary release sources: [Lean v4.35.0-rc2](https://github.com/leanprover/lean4/releases/tag/v4.35.0-rc2), [Mathlib v4.35.0-rc2 release](https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0-rc2), [matching Mathlib toolchain file](https://github.com/leanprover-community/mathlib4/blob/v4.35.0-rc2/lean-toolchain), [relocated Denumerable module](https://github.com/leanprover-community/mathlib4/blob/v4.35.0-rc2/Mathlib/Basic/Denumerable.lean).

## Likely verification scale

The deterministic export record for candidate14 reports 2,163 project modules, 2,372 files, and 34,437,784 source bytes (6,834,588-byte archive). This is a substantial fresh compile after changing Mathlib. Historical evidence gives a useful scale marker: archive 07 completed the local full pinned verifier in 11,378 seconds under a 19,800-second execution budget. Candidate14's proof-input identity record says its selected proof inputs match archive 07, but the handoff explicitly records that candidate14 itself did not receive a fresh complete verifier run. The historical time is about 57% of the current namespace-profile budget, leaving 8,422 seconds of nominal margin; this makes a run plausible, not predictable, because Lean, Mathlib, cache availability, and runner details change the build cost.

The current Mathlib release is an RC and is not the candidate's current dependency. The old manifest cannot simply be reused with Lean 4.35: update the root toolchain, Mathlib revision, and transitive manifest revisions as a consistent lock. A Mathlib cache for that exact revision and compatibility of every declaration/tactic in the local closure are not established here.

## Evidence boundary

No Lean or Lake build, cache fetch, package edit, or proof edit was performed. Source-path checks establish module availability, not successful imports or theorem compilation. A migration should be treated as a new proof-input set and receive a full verifier run; candidate14's older v4.32 receipt does not transfer across this toolchain/Mathlib change.
