# Full local verification of the sqrt241 branch

The selected theorem is
`UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound`, with
`ChallengeZeta241`, `SolutionZeta241`, and `comparator-zeta241.json`.
It proves the planar sequence conclusion at exact exponent `10427/10000`
conditional on H241, which remains unproved in Lean.

**Full local verification passed at 20:24:47 UTC on September 29, 2026.**
Candidate 4, from research commit
`697c3cd7801431d594c01785f2b3e88dd248576d`, completed the entire pinned official
pipeline under the supported 16-CPU/32-GiB namespace profile. The
[preserved terminal record](namespace-full-attempt4-preserved/README.md)
contains the raw receipts and checked identities. The result is local and
conditional on H241; it does not constitute publication, registry submission
or official Palomar acceptance.

## Preparation and first attempt

- Research base: `91c566c74af951746b2b745fc192c96e39a79a0f`.
- Archive preparation commit: `9d8cb318e6b92f38c6cf5f4d31d264835b70a147`.
- Candidate 1 SHA-256:
  `3110bc5db2bc477fe4e9a47167ad29f9c1416b028da00ab6c10957d8ec990b9f`.
- Snapshot SHA-256:
  `083073c5230f3dbacacc1d3c5ab9ca40c31fae1f36d842892e5b4e23484a57dd`.
- The dedicated exporter selects 2,288 project modules, including 237 Sqrt241
  modules, and includes attribution, licenses and dated research evidence.
- [The archive gate](candidate1-archive-gate.json) passed deterministic
  re-export, metadata intake and unchanged-source checks. These are packaging
  checks, not proof verification.
- [The failed attempt](namespace-full-attempt1/execution.json) passed the real
  16-CPU/32-GiB capacity probe and failed official source intake at 15:44:44 UTC:
  the auxiliary analysis script lacked the mandatory `module` header. No fresh
  build, protected exports, comparison or kernel replay ran in that attempt.

The shared root-owned Lean installation is
`/opt/lean/toolchains/leanprover--lean4---v4.35.0-rc2`; this worktree's ignored
`.toolchain` points to it. [Host setup](host-setup.json) identifies immutable
tool binaries and the trusted upstream pins. [Metadata intake](metadata-intake/README.md)
records that official upstream heads still matched those pins. The original
master full passes and public-layout candidate remain separate and unchanged.

## Replacement archive and interrupted attempt

Candidate 2 is bound to research commit
`ed7cef07b9eeb2f6e678dbd1cd16b845d8ebb737`:

- Archive SHA-256:
  `6ef2aa7c128b8de6741cdaad523b0be6fe71fe9c20560996a52f5a7b9374762f`.
- Snapshot SHA-256:
  `dea0aae20beb185f8c5ef8cbb30b43dd305baac09621620c4d85966575c833da`.
- [Archive gate](candidate2-archive-gate.json),
  [Git-only reconstruction](candidate2-git-inputs.json), and
  [all-source lexical intake](candidate2-source-intake.json) passed.
- The archive differs from candidate 1 only in `scripts/sqrt241/Analyze.lean`
  and the two generated identity manifests. All mathematical Lean source bytes
  are identical. The auxiliary script now uses module-system imports and a
  meta section; its analysis algorithm is unchanged. Its focused replay has
  separate evidence in `auxiliary-repair/`.
- [Full namespace attempt 2](namespace-full-attempt2/launch.json) launched at
  15:52:50 UTC under the unchanged official 16-CPU/32-GiB profile. Official
  preparation and the capacity probe passed, and execute began at 15:52:55 UTC.
  The controller was deliberately stopped at 15:55:24 UTC during trusted-cache
  setup, before the selected project build. Its supervisor records signal 15
  and successful cleanup; the interrupted worker receipt remains preserved as
  written. There is no proof-check failure or completed verification result.
- The separate auxiliary replay compiled successfully but its output did not
  match the preserved analysis: module-system visibility hid transitive proof
  bodies. That behavior requires repair. The interruption avoids spending a
  full run on an archive already known to need a further auxiliary change.

## Repaired archive and resource failure

Candidate 3 is bound to research commit
`2e02871fef432740af0cd6742b4daa274cd017c7`:

- Archive SHA-256:
  `290271044b4daafcaaa563b07a92fb7ab3ed2e67f35cbe3ba13190d85fa0d283`.
- Snapshot SHA-256:
  `1af4ae6bc56f3d2193998b968a332b47cc8556ffa8ec75036f0be17deb660d5d`.
- [Archive gate](candidate3-archive-gate.json),
  [Git-only reconstruction](candidate3-git-inputs.json), and
  [source intake and change scope](candidate3-source-intake.json) passed.
- [Auxiliary repair validation](auxiliary-repair/README.md) confirms the repaired
  analysis output is byte-for-byte identical to the preserved original. Lean's
  documented private import level restores the original inspection visibility.
- Compared with candidate 1, only the auxiliary script and identity manifests
  changed. All 2,852 other archive files are byte-identical.
- [Full namespace attempt 3](namespace-full-attempt3/launch.json) launched at
  16:04 UTC with fresh project build outputs and the unchanged official pipeline.
  Fresh project build and both protected exports passed. It terminated at
  17:35:34 UTC after 5,476.642 seconds with an out-of-memory failure during
  comparator execution, while NanoDa was the active checker. It is not a full
  verification pass. [Failure analysis](attempt3-resource-failure.md) and
  [verbatim preservation](namespace-full-attempt3-preserved/README.md) retain
  the terminal result. The subsequent diagnostic and repair are recorded below.

The [independent statement review](independent-statement-review.md) found no
material mismatch in the Euclidean sequence statement, field or explicit H241.
It is a source/mathematical-meaning review, not proof of H241 or kernel replay.
The [preliminary receipt review](final-result-review/PRELIMINARY.md) checked
27 source/configuration identity conditions before the terminal resource failure.
The [official-head recheck](final-official-heads/README.md) still matched both
trusted upstream revisions at 17:22 UTC.

## Isolated bottleneck, repair and full retry

The [separate NanoDa diagnostic](nanoda-diagnostic/README.md) used the exact
source revision bundled with Lean 4.35.0-rc2, adding only declaration-progress
logging. All 154,019 declarations started and 154,018 finished. Only the
private proof behind `Dyadic.u_yM` remained while memory grew to 38.148 GiB.
The diagnostic was deliberately stopped, with no OOM or kernel rejection;
that interrupted diagnostic is distinct from the official attempt 3 OOM.

The [repair evidence](dyadic-u-refactor/README.md) replaces its single large
closed computation with eight separately checked multiplication certificates
and explicit congruence/transitivity. The original public statement, model
data and GP source are unchanged, and the generator reproduces the revised
Lean source. Focused compilation passed in 16.275 seconds; unmodified NanoDa
passed in 1.422 seconds, con-ron verified mode in 6.535 seconds, and Lean
export replay in 4.830 seconds. The focused run's aggregate peak was
1,501,450,240 bytes, with no OOM. This is a selected-proof diagnostic, not a
full submission pass. [Independent source/arithmetic review](dyadic-u-independent-review/README.md)
checked every new equation, all 256 basis products and exact preservation.

Candidate 4 is bound to research commit
`697c3cd7801431d594c01785f2b3e88dd248576d`:

- Archive SHA-256:
  `c64d0aa7dcd648fa8ecd464da59787362f853190a5bee7cff9713e6c34f429a9`.
- Snapshot SHA-256:
  `e88eae2d20b2ada60272ee3ddf7286bb4e82d479a4e5de6c5ca86da22ec4f128`.
- [Archive and metadata gate](candidate4-archive-gate.json) and
  [Git-only byte-identical reconstruction](candidate4-git-inputs.json) passed.
- [Complete archive comparison](candidate4-change-scope.json) finds exactly
  six changed files: the dyadic Lean module, its generator, README, metadata,
  and two identity manifests. All other 2,849 files, including Challenge,
  Solution and the comparator, are byte-identical to candidate 3.
- The first packaging capture rejected incidental Python bytecode generated
  during review. [Its receipt](candidate4-export-attempt1.json) records moving
  that generated cache out of the source tree; no source or verifier changed.
- [Full namespace attempt 4](namespace-full-attempt4/launch.json) launched at
  18:13:30 UTC. Official preparation and the real capacity probe passed, and
  execute began at 18:13:35 UTC. Fresh project build outputs are used; all
  original required checks and the unchanged official pipeline remain enabled.
  It finished with complete/pass at 20:24:47 UTC. The terminal result is recorded
  separately below; earlier failures and diagnostic receipts remain preserved.

## Candidate 4 terminal result

The [official report](namespace-full-attempt4-preserved/work/local-execution.json),
[execution adapter](namespace-full-attempt4/execution.json),
[supervisor](namespace-full-attempt4/supervisor.json), and
[strict preservation receipt](namespace-full-attempt4-preserved/preservation.json)
agree on a full pass for the exact archive and source snapshot above. The
execution took 7,876.607 seconds; the supervisor, including final cleanup,
recorded 7,876.904 seconds. No required proof check was skipped or weakened.

| Required check | Result |
| --- | --- |
| Fresh project build | Passed; 6,958 jobs, 2,640.926 seconds |
| Protected Challenge export | Passed; 12.178 seconds |
| Protected Solution export | Passed; 109.846 seconds |
| Statement and transitive-definition comparison | Passed |
| Export-based allowed-axiom checks | Passed: `propext`, `Quot.sound`, `Classical.choice` |
| con-ron | Accepted 150,512 declarations in `--verified` mode |
| NanoDa | Affirmative acceptance of the full Solution export |
| Lean kernel replay | Affirmative acceptance of the full Solution export |
| Source/tool identities and cleanup | Unchanged sources/tools; cleanup passed, final process count zero |

The complete comparator phase took 4,933.564 seconds and ended with all three
kernel acceptance messages and `Your solution is okay!`. Both the initial
source and prepared project lacked build outputs before compilation. The
real capacity probe and routing checks passed. The canonical shared Lean
installation and pinned official tools were used; the separately instrumented
NanoDa diagnostic was not used for this proof pass.

The enforced aggregate limits were 16 CPUs, 34,359,738,368 bytes (32 GiB) and
zero swap. Aggregate memory reached that cap, with 22 `max` events and no OOM
or OOM-kill events in either hierarchical or local counters. There was one
hierarchical `high` event. These measurements establish successful completion
under the enforced limit, without demonstrating spare memory headroom. The
controller finished successfully and is inactive; the final boundary had
`populated 0` and `pids.current 0`. Preinstalled tool setup is outside the
recorded preparation/execute budget, as disclosed in the launch record.

The protected export identities are:

| Export | Bytes | SHA-256 |
| --- | ---: | --- |
| Challenge | 208,104,849 | `7ca7b7c5e7f2763319518bfea0ef1b700c65b329ff24671ad5fddeb826859f7c` |
| Solution | 1,768,562,311 | `3169ba346d324cd00d5c760bb81769bbc8a167f7cfd271662c4b25632c630f2b` |

The binary exports remain in the original workspace with checked identities.
The preservation copies the raw reports, logs and source identity files without
alteration. All 37 entries in its `SHA256SUMS` were rehashed successfully;
preservation reported no integrity or validation errors. Its receipt SHA-256 is
`ca5455d6408a0fd149700594b966bc3bbcf24530e24c67869552f9ef72655ae3`.

The [independent terminal review](final-result-review-candidate4/REVIEW.md)
passed all [70 checks](final-result-review-candidate4/terminal.json), with no
discrepancy found. It rechecked committed source blobs, both execution source
copies, actual protected export bytes, all kernel acceptances, tool identities,
resource boundaries and cleanup. Its earlier preliminary review is preserved
unchanged. This is an audit of the completed local run and its artifacts;
the separate source/mathematical-meaning reviews remain separately scoped.

## Completion gate

Completion requires one exact archive to pass fresh project build, protected
Challenge and Solution exports, statement/definition comparison, permitted
axioms, con-ron, NanoDa and Lean kernel replay, with a terminal complete/pass
report and unchanged source/tool identities. The bounded runner retains all
official checks. No partial phase is counted as completion.

Candidate 4 satisfies that local completion gate. Local verification does not
prove H241, publish a repository, submit a registry request or establish official
Palomar acceptance. This new terminal result is separate from the historical
receipts embedded in the unchanged archive. A public package and a hosted run
on its exact published commit remain separate steps for this candidate.
[Reproduction instructions](REPRODUCE.md) identify source recovery and the full
bounded run on this machine.
