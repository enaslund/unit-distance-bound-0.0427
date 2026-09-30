# Bounded kernel replays of the ℚ(√241) package (2026-09-29)

Scope: the conditional package `ChallengeZeta241.lean` / `SolutionZeta241.lean`
(exponent 1.0427; the hypothesis H on the genus field `E` is explicit and **not**
proved). This directory records the three protected kernel checks of the Palomar
pipeline — con-ron, NanoDa and Lean's own kernel — run on the exported Solution
closure under the limits of the Palomar Standard hosted profile, the proof changes
that were needed for them to fit, and the full axiom audit. It reproduces the kernel
phase locally; it is not the complete protected workflow (see "Not covered").

## Merged sources (current)

When this work was merged with `verification/sqrt241-full-20260929`, the proof of
`Dyadic.u_yM` was taken from that branch: seven single products by `yM`, independently
reviewed and verified there in the complete 16-CPU/32-GiB pipeline. The pair-mass and
group-data changes described below were kept. The Solution export of the merged
sources (`solution241-merged.ndjson`, commit `3d15d340`, sha256
`a16eee2b5106c8b8f1b8ac9c334b0c4dda778ddc2f12b7d2e6bb7b96389cde1f`, 1,771,571,616 bytes)
was checked by each kernel on its own under the same limits:

| kernel | verdict | wall time | cgroup memory peak | memory events |
|---|---|---:|---:|---|
| con-ron (`--verified`) | accepted 151,309 declarations | 1,636.0 s | 10.29 GiB (11,043,725,312 B) | none |
| NanoDa 0.4.17 (`num_threads` 4) | accepted (exit 0) | 543.4 s | 10.36 GiB (11,118,198,784 B) | none |
| Lean kernel (`lake env leanchecker --from-export`) | "Lean default kernel accepts the solution" | 2,613.3 s | 7.95 GiB (8,532,897,792 B) | none |

The reorganization of the repository that followed changed no declaration: a
re-export from the final tree is byte-identical to this export. Declaration-by-declaration
comparisons (`compare_exports.py`):

* against the committed sources before any split (`solution241.ndjson`, commit
  `91c566c7`), only `MassCert.grid_checks`, `MassCert.cell_checks`,
  `MassCert.pairMassBetaIntegral_le_of_checks` and five auxiliary kernel-check lemmas
  changed their types, no definition changed, and 829 declarations are new
  (`merged-export-comparison-original.json`);
* against `solution241-r4` below, no common declaration changed; only the two `u_yM`
  repairs' own declarations differ (`merged-export-comparison-r4.json`).

Receipts: `merged-conron/`, `merged-nanoda/`, `merged-lean/`, `merged-driver.log`,
produced by the launchers and summarizer described below. The rest of this file
concerns the earlier sources of commit `7bdc6080` (export `solution241-r4`).

## Result

Final export `solution241-r4.ndjson` (sha256
`f461d50658b41e48d112fc43cc64fa8ba9e5a9498882dd3da4d2df7c1a6bf26f`, 1,771,563,528
bytes). Each kernel ran on its own under 4 CPUs (`taskset -c 0-3`, `CPUQuota=400%`),
`MemoryMax=16G` and `MemorySwapMax=0`:

| kernel | verdict | wall time | cgroup memory peak | memory events |
|---|---|---:|---:|---|
| con-ron (`--verified`) | accepted 151,293 declarations | 1,481.6 s | 10.45 GiB (11,217,887,232 B) | none |
| NanoDa 0.4.17 (`num_threads` 4) | accepted (exit 0) | 893.3 s | 9.25 GiB (9,928,056,832 B) | none |
| Lean kernel (`lake env leanchecker --from-export`) | "Lean default kernel accepts the solution" | 4,246.6 s | 7.37 GiB (7,912,275,968 B) | none |

The peaks are cgroup `memory.peak` values; they include the page cache charged for
reading the 1.77 GB export (and, for the Lean kernel, the waiting `lake env` wrapper).
Lean's replay is single-threaded. The host (8 CPUs, 31 GiB) was shared with other
jobs and under load (load average 9–12) during all runs, so the wall times are upper
estimates for a dedicated 4-CPU runner. In the pipeline, `lake comparator` runs the
three kernels one after the other in one phase; their sum here is 6,622 s.

## What was heavy, and why

con-ron keeps every intermediate of a declaration in memory until the declaration is
checked, and its big-number arithmetic is slow on long rationals (one `Nat.gcd` of two
3,000-bit numbers took 0.5 s in a micro-benchmark). NanoDa evaluated those rationals
quickly but was very slow, with steadily growing memory, on one reduction of a deep
product in a nested quadratic algebra. Lean's kernel had no difficulty with any of
these declarations.

1. **con-ron, as committed (`conron-trace1-oom/`).** The export of the Solution as
   committed (`f15f9f92…`) was OOM-killed at 16 GiB after 504 s, with 143,664 of
   148,794 checks done. The attribution
   (`verification/hosted-fit-20260929/diagnosis/pending_from_progress.py`) left
   exactly three active checks, all in the generated pair-mass certificate
   `UnitDistance/Sqrt241/Numerics/PairMassData.lean`: `MassCert.grid_checks`,
   `MassCert.cell_checks` and `MassCert.total_check`, each one `decide +kernel`
   over the whole 12 × 12 grid. Memory grew by about 80 MiB/s for 140 s while they
   ran. The exact 144-cell total carries denominators of tens of thousands of digits,
   and one exact logarithm of `RatLog.lean` (30-term `artanh` series) of a
   15–25-digit rational took 4–15 s in con-ron.
2. **con-ron after the pair-mass restructuring (`conron-trace2-pass-14GiB/`).**
   Accepted (`8915da3f…`, 1,529.5 s), but with a 14.15 GiB peak: the two
   Cayley-edge certificates `Retained.dyadicMapFn_step_coordinates_zero/_one`
   (`GroupData/DyadicMaps.lean`, one `decide +kernel` over 32 group elements × 3
   generators × 23 coordinates each) ran together for 65 s and added about 7 GiB.
   The next largest ℚ(√241) checks were `MagnusB.third_row_certificate` and
   `Universal.initial_certificate` (28 s each; the latter, alone at the time, added
   about 1.6 GiB) and `Retained.forms_zero_certificate` (16 s, about 1.1 GiB).
3. **con-ron after the group-data splits (`conron-trace3-pass/`).** Accepted
   (`318e2f74…`, 1,521.6 s), peak 10.08 GiB.
4. **NanoDa on that export (`nanoda-trace3-oom/`).** OOM-killed at 16 GiB after
   about 1,194 s. NanoDa prints no progress, so the attribution used a diagnostic
   NanoDa 0.4.17 build whose only change is a START/DONE line around the unchanged
   per-declaration check (built on 2026-09-25 in an earlier session, binary
   `33421ac3…`; diagnostic only, not a verdict): all 154,815 other declarations were
   done, and the only unfinished one was the kernel check of
   `Discriminant.Dyadic.u_yM` (`π₂ u = y⁸`, one reduction of the eightfold product
   `yM * yM * ⋯ * yM` in the nested quadratic model of degree 16), which grew by about
   40 MiB/s for more than 230 s (`nanoda-diagnostic-r3.json`). The largest other
   NanoDa item was the pair `ArithmeticProP.fieldScalarUnitH2_tensor(_eq_zero_iff_norm)`
   of the imported ℚ package (220–305 s, about 9.3 GiB together).
5. **Final export (`conron-final/`, `nanoda-final/`, `lean-final/`).** The con-ron
   peak (10.27 GiB sampled at t ≈ 1,457 s) is where two unchanged certificates of the
   imported ℚ package (`RetainedQuadratic.dyadicMapFn_step_coordinates`, 37 s;
   `CatalogRetainedCoordinates.cocycle_polar_certificate`, 27 s) overlapped the two
   Horner identities `f_yM`, `h_uM` of `Discriminant/DyadicModel.lean` (23 s each).
   The largest ℚ(√241) checks now take at most 23 s in con-ron; the baseline of the
   loaded environment is about 4.5–5 GiB.

Per-check con-ron durations were estimated from the progress logs (the `k`-th
completion frees the worker that claims pending index `k + 3`); memory attribution is
by coincidence in time, as in `verification/hosted-fit-20260929/diagnosis/`.

## What was changed

No theorem statement of the submission chain changed: `SolutionZeta241`,
`target_of_canonical_genus_zeta_bound`, `Witness.uniform_margin`, `JPair_lower`,
`MassCert.pairMassBetaIntegral_le_massUpper` (with `massUpper = 38.794821206`) and
everything downstream are as before. The certificate data `XL`, `XU`, `hTab`, `HTab`,
`yM`, `uM` and all polynomial lists are byte-identical. Only internal certificate
lemmas changed. Mechanically (`compare_exports.py`, types compared up to binder names,
`export-comparison.json`): of the 154,010 declarations common to the committed and the
final export, exactly three named declarations changed their statement —
`MassCert.grid_checks`, `MassCert.cell_checks` and
`MassCert.pairMassBetaIntegral_le_of_checks`, which now use `logLoR`/`logHiR` — plus six
auxiliary `…_proof_1_1` lemmas whose names are reused by the split checks; no definition
body changed; 812 declarations are new, and 5 left the closure (the three former
monolithic pair-mass kernel checks and `le_rpow_of_logs`, `rpow_le_of_logs`, which remain
in `RatLog.lean`).

* **Pair-mass certificate** (`Numerics/PairMassData.lean`, regenerated by
  `scripts/sqrt241/generate_pair_mass_certificate.py 12`):
  * one lemma per grid point (`grid_check_k`, 11) and per cell (`cell_check_i_j`,
    144), each its own `decide +kernel`; `grid_checks` and `cell_checks` are
    assembled by `forall_lt_succ_of` (new in `PairMassRat.lean`);
  * directed rounding of the total: the exact contribution
    `HTab i j * max (cellEbar …) 0` of each cell (a rational with a denominator of a
    few hundred digits) is bounded by `cTab i j`, rounded up to a multiple of `10⁻¹⁵`
    (`contrib_check_i_j`, 144 lemmas); only these short rationals are summed
    (`total_sum_check`), and `total_check` follows by `massTotal_le_of_cells` (new,
    `PairMassRat.lean`). Rounded total 38.79482120531866, exact total
    38.79482120531859, both below `massUpper`;
  * the logarithm enclosures of these checks are the new outward-rounded
    `logLoR`/`logHiR` (`Numerics/RatLogRounded.lean`, hand-written; `logR_bounds`):
    the argument reduction and 30-term series of `RatLog.lean` with every power and
    term rounded outward to a multiple of `10⁻⁴⁰`, so that no intermediate exceeds
    about 80 digits. The soundness theorem `MassCert.pairMassBetaIntegral_le_of_checks`
    (`PairMassCell.lean`) now states its grid and cell hypotheses with
    `logLoR`/`logHiR` (proof otherwise unchanged, via the new
    `le_rpow_of_logsR`/`rpow_le_of_logsR`).

  In isolation (export of `grid_endpoints`, `grid_checks`, `cell_checks`,
  `total_check`; 4 workers, same limits) con-ron checks the whole certificate in 142 s
  with a 0.70 GiB peak. With per-cell lemmas but the exact series of `RatLog.lean` it
  stayed below 0.3 GiB but needed about 25 s per cell check under the same load
  (stopped after 473 s).
* **Group-data certificates** (hand-written; statements unchanged, proofs split with
  `fin_cases … <;> decide +kernel`, as in the ℚ package's `DyadicCertificates.lean`):
  `GroupData/DyadicMaps.lean` `dyadicMapFn_step_coordinates_zero/_one` (per generator
  for the base part, per generator and central coordinate for the central part: 48
  kernel checks each, every one over all 32 elements of `D`);
  `GroupData/MagnusCertificates.lean` `third_row_certificate` (per row, 21);
  `GroupData/Universal.lean` `initial_certificate` (per initial, 7);
  `GroupData/Words.lean` `forms_zero_certificate` (per form, 21). In isolation these
  check in 92 s with a 1.38 GiB peak, no piece longer than 4 s.
* **`π₂ u = y⁸`** (`Discriminant/DyadicModel.lean`, regenerated by
  `scripts/sqrt241/generate_dyadic_certificate.py` from `dyadic_certificate.gp`):
  the explicit powers `y2M`, `y4M`, `y8M` (computed by PARI/GP) are new definitions,
  and `u_yM` (statement unchanged) is proved from four kernel checks of one product of
  two explicit elements each (`yM * yM = y2M`, `y2M * y2M = y4M`, `y4M * y4M = y8M`,
  `pi2M * uM = y8M`) and `ring`. In isolation (with `f_yM`, `h_uM`) NanoDa needs 10 s
  and 1.40 GiB for this module, con-ron under 1 s per product.

## Commands

From `lean-formalization/` (toolchain `.toolchain/bin`, Lean 4.35.0-rc2
`11acb17e…`, Mathlib `06535612…`):

```sh
./.toolchain/bin/lake build SolutionZeta241 ChallengeZeta241
export PATH=$PWD/.toolchain/bin:$PATH
lake env leanexport SolutionZeta241 -- \
  UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound \
  > .cache/conron241/solution241-r4.ndjson
sha256sum .cache/conron241/solution241-r4.ndjson

# con-ron: the unchanged scripts/diagnose-conron.py (runs `con-ron --verified --progress=1 EXPORT`)
verification/sqrt241-bounded-20260929/run-conron-standard.sh \
  .cache/conron241/solution241-r4.ndjson <sha256> .cache/conron241/standard-trace4
python3 verification/hosted-fit-20260929/diagnosis/pending_from_progress.py \
  --log .cache/conron241/standard-trace4/con-ron.stderr \
  --output .cache/conron241/standard-trace4/attribution.json \
  --pending-output .cache/conron241/standard-trace4/pending.jsonl

# NanoDa, with the configuration that `lake comparator` writes (nanoda-final/nanoda-config.json)
verification/sqrt241-bounded-20260929/run-kernel.sh .cache/conron241/nanoda-trace4 \
  .toolchain/bin/nanoda_bin .cache/conron241/nanoda-r4.json

# Lean's kernel as `lake comparator` runs it (`leanchecker --silent --from-export EXPORT`);
# here without --silent, which only suppresses the verdict line
verification/sqrt241-bounded-20260929/run-kernel.sh .cache/conron241/lean-trace4 \
  .toolchain/bin/lake env .toolchain/bin/leanchecker --from-export \
  .cache/conron241/solution241-r4.ndjson

python3 verification/sqrt241-bounded-20260929/summarize_run.py DIR --kernel KERNEL --export-sha256 SHA
python3 verification/sqrt241-bounded-20260929/compare_exports.py \
  .cache/conron241/solution241.ndjson .cache/conron241/solution241-r4.ndjson --output …
```

Each run was started detached (`setsid nohup … &`); only one kernel run or Lean build
ran at a time. `run-kernel.sh` and `run-conron-standard.sh` put the command in its own
`systemd-run --user --scope` with `MemoryMax=16G`, `MemorySwapMax=0`, `CPUQuota=400%`
and `taskset -c 0-3`; `observe_kernel.py` samples the scope's
`memory.current`/`memory.peak` every 0.5 s; `summarize_run.py` writes each
`summary.json` (with the sha256 of the logs that are not copied here) and
`memory-series.json` (largest `memory.current` per 10 s).

Exports (kept under `.cache/conron241/`, not in the repository):

| export | sources | sha256 | bytes |
|---|---|---|---:|
| `solution241.ndjson` | as committed (`91c566c7`) | `f15f9f927bb0f58046a35e7bad7868c34de3cb1aab925586cf51bff1001f399b` | 1,768,682,179 |
| `solution241-r2.ndjson` | + pair-mass restructuring | `8915da3f450b692aa2f52348217466385580a3ab0acaa6d71926e69fadeb732d` | 1,769,982,693 |
| `solution241-r3.ndjson` | + group-data splits | `318e2f74f2415066d7ee1666d6e7456cc593461728055121753cf068ce2d4b97` | 1,771,511,178 |
| `solution241-r4.ndjson` | + `u_yM` through explicit powers (final) | `f461d50658b41e48d112fc43cc64fa8ba9e5a9498882dd3da4d2df7c1a6bf26f` | 1,771,563,528 |

Tools: con-ron `4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`,
`nanoda_bin` `8241c5e6baa29490aa118d382f97961b208ae730fdb96545c2abed74c9ece5a8`,
`leanchecker` `9e36e955a251b1313c8eb5b7fa101282d51df109d34d8bb7c1cfdf51985aba29`,
`leanexport` `c5bc1a10a21e22cbb3671d65987cdef2076833b14182d823ccb2153adf2fa954`,
`lean` `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.

## Build and axiom audit

After the last change, `lake build SolutionZeta241 ChallengeZeta241 AuditSupport`
(6,963 jobs) is up to date without errors, and the root module `UnitDistance.Sqrt241`
and the eleven extra modules listed in `docs/sqrt241/SUBMISSION.md` build. The audit
scripts `audit/Sqrt241Audit.lean` and `audit/Sqrt241ExtrasAudit.lean` were run from a
scratch directory with `lake env lean -R <dir> <file>`:

* `#print axioms` of `UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound`,
  `UnitDistance.Sqrt241.target_of_canonical_genus_zeta_bound`,
  `UnitDistance.Sqrt241.Witness.uniform_margin` and
  `UnitDistance.Sqrt241.Witness.MassCert.pairMassBetaIntegral_le_massUpper`:
  `[propext, Classical.choice, Quot.sound]`;
* `UnitDistanceAudit.audit` over the 57,378 `UnitDistance` declarations in the closure of
  `SolutionZeta241` (including private auxiliaries and attributed ports) and over the 32
  submission declarations: the transitive axiom union is exactly
  `propext, Classical.choice, Quot.sound`;
* the same for all 7,258 declarations of `UnitDistance.Sqrt241` with the root module and
  the eleven extras imported.

The regenerated `PairMassTables.lean`, `PairMassData.lean` and `DyadicModel.lean` are
byte-identical to the committed files (`regeneration.txt`); `ChallengeZeta241.lean` and
`SolutionZeta241.lean` are unchanged (`source-hashes.txt`).

## Receipts

* `conron-trace1-oom/`, `conron-trace2-pass-14GiB/`, `conron-trace3-pass/`,
  `conron-final/`: `manifest.json`, `process.json`, `result.json`,
  `attribution.json`, `summary.json`, `memory-series.json` (and `con-ron.stdout`)
  of the four con-ron runs;
* `nanoda-trace3-oom/`: memory series, OOM journal lines, configuration and the
  diagnostic attribution of the failed NanoDa run;
* `nanoda-final/`, `lean-final/`: `result.json`, `summary.json`,
  `memory-series.json`, the kernel's output, and NanoDa's configuration;
* `export-comparison.json` (and its console output `export-comparison.log`):
  declarations of the committed and the final export that exist in only one of them,
  or whose statements (types up to binder names) or definition bodies differ;
* `audit/`: the two axiom-audit scripts and their logs;
* `regeneration.txt`: byte-for-byte regeneration of the changed generated files;
* `source-hashes.txt`: sha256 of every file of `UnitDistance/Sqrt241/`, of
  `ChallengeZeta241.lean`, `SolutionZeta241.lean` and of the changed generators;
* scripts: `run-conron-standard.sh`, `run-kernel.sh` (bounded launchers),
  `observe_kernel.py` (memory observer for NanoDa and Lean), `summarize_run.py`,
  `compare_exports.py`.

## Not covered

* The complete protected pipeline: a fresh build inside the bounded workflow, the
  protected Challenge export, the statement and definition comparison of
  `lake comparator` (`comparator-zeta241.json`) and its sandbox. The kernels here
  checked the export of the selected theorem's closure, not the comparator's export
  with its additional targets; the comparator runs the three kernels one after the
  other in one phase.
* Namespace (16 CPUs, 32 GiB), and a stress test at the Standard profile's 14 GiB
  minimum.
* H itself.
