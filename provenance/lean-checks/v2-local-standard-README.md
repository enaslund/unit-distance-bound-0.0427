# Local pinned Palomar pipeline for the version 2 package (2026-10-08)

> Copied from `lean-formalization/verification/v2-local-20261008/README.md` of the research repository at commit `a5273110`; links point to the copies in this directory.

**Passed.** The complete pinned Palomar pipeline (PalomarSubmission `65f0154`, profile
`palomar-standard-v1`: 4 CPUs, 16 GiB, no swap) ran on this host's trusted setup
(`verification/migration-20260929/trusted-setup.json`) against the version 2 candidate:

| Item | Value |
| --- | --- |
| Archive | exported from research commit `8c69d5c6` by `scripts/export-zeta241-candidate.py` ([export report](export-report.json)) |
| Archive SHA-256 | `647219527ad66a70a6e4274a759b563b2d601bd34ff90cbc4f0dab03be7dd8b4` |
| Source snapshot SHA-256 | `93c14710e72c15bf471a04d46b36c84721e98652dce9e7d87a100cc145bae2cf` (3,074 files) |
| Selected theorem | `UnitDistanceSqrt241Submission.target_of_wide_zeta_bound` (`comparator-zeta241.json`) |
| Archive gate | `scripts/verify-zeta-candidate.py --check-only`: passed ([archive-gate.json](v2-local-standard-archive-gate.json)) |
| Probe | passed (probe records in the research repository) |
| Full run | started 04:43:13 UTC, finished 06:36:50 UTC (6,818 s); `execution_status: pass`, `errors: []`; fresh build, protected export, Comparator with permitted axioms `propext`, `Quot.sound`, `Classical.choice`, and the kernels NanoDa and con-ron ([execution.json](v2-local-standard-execution.json), [local-execution.json](v2-local-standard-local-execution.json)) |
| Resources | peak memory 15.21 GiB of the 16-GiB limit, no OOM events; Solution build 3,568 s, export 116 s, Comparator phase 2,983 s |

This is a local reproduction, not an official Palomar report or registration. The archive
predates the manuscript's retitling (commit `11bae070`, "An Exponent of 1.043 for the Unit
Distance Problem"), which changes the shipped paper copy, README and metadata but no Lean file;
the published candidate will be re-exported after the paper's public commit is known, and its
archive gate rerun. The memory peak is close to the standard profile's limit.
