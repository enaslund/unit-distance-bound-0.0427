# Target-sigma H6 replacement: Lean arithmetic leaf

`UnitDistance/H6TargetAggregateReplacementArithmetic20260923.lean` copies
the exact rational direct upper, frozen upper, old group sum, and group
allowance from `h6_target_aggregate_replacement.json` (SHA-256
`35ec8d17c01f716663e9e7c7b64862413efd65cbae6807851b3d06536e360f27`).
The file states three rational inequalities: the direct upper is strictly
larger than the frozen row endpoint; replacing that row in the old exact
mixed-quadratic group sum stays strictly below the published rational group
allowance; and the unchanged final rational upper stays below the manuscript
threshold. The source SHA-256 is
`b7393c6351dca618d7e5d707e54e83eeda8cd3c545c964c25b42c1e989c85c1e`;
the focused audit source SHA-256 is
`720817490eecb8733302237bea0893c32ee6e4e5a1ffa15d1c645118bd647135`.

**Status:** guarded Lean source compile **PASS** and focused axiom audit
**PASS**. The source compile exited 0 and wrote its `.olean` after guard
admission at 16.6 GiB host availability and 1.35 GiB cgroup headroom. The
separate audit exited 0 after admission at 16.7 GiB / 1.25 GiB and printed
only `propext`, `Classical.choice`, and `Quot.sound` for all three
declarations. Both used the pinned Lean toolchain, `-j1 -M2560`, inherited
disk-backed `TMPDIR`, the master guarded helper and shared lock, with a
900-second per-job timeout. The source and audit hashes above were unchanged
by these checks. No full selected proof or package verifier was run by this
research-leaf check.

An
[independent transcription review](h6-target-lean-arithmetic-transcription-review.md)
matched all four rational constants, the exact widened sum and slack, the
final ceiling literal, and the pinned receipt hashes. This
checked arithmetic leaf does not prove the direct outward Arb interval, the
AFE/kernel assumptions, the factor identity, the functional equation, the
global coefficient bound, the other analytic rows, or H. The individual row
comparison remains a FAIL, independently of the group arithmetic.
