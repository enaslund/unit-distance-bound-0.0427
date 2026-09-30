# Finite support needed for the additional Euler-defect saving

## Scope and result

This report combines source analysis with exact external replay of the stored
H7 complement-prime list. No new census enumeration or Lean build was started.
The target is the extra normalized actual Euler-defect saving needed after
using the existing order-four saving and the five-family completed-field
allowance.

The numerical endpoint is the first `387,955` primes from the H7
`complement_primes` list, ending at `163137359449`. The archived whole-bin
support contains one more prime, `163137534121`, for a total of `387,956`.
The crossing computation reports that the exact central-local-saving sum at
the `387,954` prefix is below `3801674/10^11`, while the `387,955` prefix is
above it by `5.447873151974326893…e-12`. This margin is a 256-bit Arb
computation, not a checked rational or Lean conclusion
([crossing script](../../../astra-sol-20260920/central-census/analyze_prime_list_crossing.py),
[result](../../../astra-sol-20260920/central-census/prime-list-crossing-analysis.json)).

There is an existing, more conservative rational route at the whole-bin endpoint:
the first 6,716 bins contain `387,956` complement primes and their checked
row lower sum (as recomputed by the exact threshold-analysis script) is
`1188023433326333206355837 / 31250000000000000000000000000`, exceeding the
required `48661213036396746910923 / 1280000000000000000000000000` by
`1.771817577040792282e-10`. The stored threshold audit says this is the
minimal bin-prefix receipt for that bound
([threshold analysis](../../../astra-sol-20260920/central-census/README.md#L84)).
This receipt is numerical table data until each finite prime's eligibility,
primality, and membership in the actual bin sets is proved in Lean.

An exact integer calculation in the replay adjusts those same table rows by
last row after omitting the 387,956th listed prime. With the table's existing
exponential numerator and the reduced final-bin floor-reciprocal numerator,
the maximal valid final lower numerator is `2123531948714460306391`. The
resulting 387,955-prime rowwise saving is
`38016743749819487316929750 / 10^30`, exceeding the post-refit required
rational bound by `1.7106513452879276e-10` and the direct Lean budget
`3801674/10^11` by `3.749819487e-12`; the guarded full replay below records
this result.

## Exact support predicate and provenance

The relevant actual-field certificate is
`RetainedZetaCentralRawCertificateAstra.Certificate`.
Its fields assert `p > 17`, seven genus Euler powers equal to one, all 17
catalog quadratic-algebra Euler powers equal to `±1`, all seven completed
word parities are even, and at least one of the 12 retained word parities is
odd ([raw certificate](../../../UnitDistance/RetainedZetaCentralRawCertificateAstra.lean#L19)).
The deterministic generic predicate `CentralCensusDeterministicRun20260920.eligible`
has exactly these conditions; it derives actual splitting-index facts from a
proof of that predicate, rather than from a Boolean census flag
([eligibility predicate](../../../UnitDistance/CentralCensusDeterministicRun20260920.lean#L18),
[actual-bin constructor](../../../UnitDistance/CentralCensusDeterministicRun20260920.lean#L93)).
The H7 generator applies the seven completed and twelve retained linear masks
to 17 field signs. The 387,956 listed primes are the complement among
completed-split candidates: the completed parities vanish and a retained
parity does not. The genus/full/completed/complement counts at the endpoint
are `51425975 / 51414883 / 51026927 / 387956`.

The stored prime list has SHA-256
`6e87d9e9a3f8cf4a77223a04b618128f373d00f923a7c679b6bf01ad43f9bb18`.
It was emitted by a derived one-thread C++ census from the publication H7
generator; the publication input and generator hashes, archive row matching,
and independent finite-field replay through `10^8` are described in
[the census README](../../../astra-sol-20260920/central-census/README.md#L1).
The publication H7 source `h7-census.cpp` is pinned there at
`3bf8a7af2e4b9d219e9ddc6f35631333fa67dc283291b0c1040332a1487be493`; the
derived prime-list C++ source SHA-256 is
`6cecc90f22c53edbb74648313ad4a61851d385c6e99fe0e2fb13ed08c1bb9dac`, and
its builder SHA-256 is
`42dd71244649d4ddedfa18f814fd5fc4d43051cc81c1c631a7ce2d4f7f10b08c`. The
endpoint C++ run took 187.76 seconds according to that report. The current
replay independently validates the selected list entries and row receipts;
this is reproducible finite computation, not a formal prime or number-field
certificate for the entire list.

## What Lean already proves

`CentralCensusActualSupport1000Run20260920b` composes 1,000 actual prime
certificates in ten 100-prime blocks, proves exact floor-reciprocal receipts,
and transports the local saving to the genuine completed/retained Euler
defect. Its checked lower saving is `2231824/10^11`; the source uses the
sharper-pair budget to require at least `3801674/10^11` from the central
support. The corresponding `target_of_support1000_and_grouped_completed`
still assumes the completed-field bound, and the 1,000-prime support does not
close this additional gap ([budget source](../../../UnitDistance/EulerLunaRun20260922Budget.lean#L35),
[1,000-prime assembly](../../../UnitDistance/CentralCensusActualSupport1000Run20260920b.lean#L1)).

The generic proof interface is already suitable for a larger explicit
support: for each listed prime, supply the raw `Certificate`; prove binwise
upper bounds and exact reciprocal receipts; then apply
`datum_centralSaving_lower` and sum the disjoint bins. The strongest compact
existing calculation is the 6,716-row / 387,956-prime table endpoint, not the
single global range estimate. The latter is too coarse: the proved
`centralLocalSaving_lower_two_pow38` coefficient `11973/12000` converts the
exact floor reciprocal receipt for the first 387,955 primes to only about
`3.7990528143e-5`, below the needed `3.8016572685e-5`.

## Smallest useful checker and proof interface

A compact exact *finite replay* can validate the sufficient subset without
scanning every prime to `1.63e11`:

1. Read the existing sorted complement list, take its first 387,955 entries,
   and verify strict order, the endpoint, and its placement in the first 6,716
   pinned archive/Lean rows.
2. For every entry, run a deterministic primality test valid below `2^64`
   (all inputs here are below `2^38`), then evaluate the exact modular powers
   for the seven genus tests and 17 catalog signs, followed by the seven
   completed and twelve retained parity tests.
3. Accumulate integer floors `10^30 / p` in each of the first 6,716 bins and
   compare with the archived row receipts. For the last bin, subtract the
   omitted 387,956th prime's floor receipt. Recheck the rational `Datum.Valid`
   inequalities from the pinned Lean table source; replace the last row's
   reciprocal and lower numerators by the exact values for the partial bin;
   then compare the rational weighted lower sum with the exact target.

The hardened v2 working runner is
[`replay_finite_support.py`](replay_finite_support.py). It has resumable
contiguous `replay --start/--stop` chunks (default maximum 5,000 primes per
chunk) and an `aggregate` command. It pins the prime list, arithmetic catalog,
archive, threshold manifest, and all 34 Lean table source hashes. Each chunk
replays deterministic 64-bit primality, all finite-field signs and masks, and
per-bin floor receipts. The aggregate verifies gapless chunk coverage,
compares each bin receipt directly to pinned Lean `Datum` reciprocal values,
checks the exact rational row inequalities, and computes the adjusted
partial-bin saving. The complete replay passed in five chunks:

| Index range (stop exclusive) | Primes | Replay seconds | Guard admission (host / cgroup GiB) | Receipt SHA-256 |
|---|---:|---:|---:|---|
| 0–1,000 | 1,000 | 0.5160 | 14.1 / 1.27 | `7ace5285707a3ab3a3ad7a7ae1c29e07cb70760b887fa62e4753c56b1497bcb2` |
| 1,000–101,000 | 100,000 | 53.0223 | 13.9 / 1.26 | `a3f25547c63543269cf3a6229bb5eaf81d1814a64d93550a171ea8009847ebe3` |
| 101,000–201,000 | 100,000 | 54.8626 | 14.6 / 1.20 | `8b809c15f23698fa7064b6b65e089a09173c0dae36e3f6e80afcf1918c3ddd76` |
| 201,000–301,000 | 100,000 | 55.9629 | 14.1 / 1.19 | `54f10de3f5b48542e64e7e940e5bd75473b056661758795c546f74ad61b70f7f` |
| 301,000–387,955 | 86,955 | 49.8258 | 15.5 / 1.19 | `0ef672d2ffea8c5b7b5036cbe49a8fcb40f85e79e71a605e2d5b76bc083548be` |

The first chunk spans primes `451201` through `350477689`; the final chunk
ends at `163137359449`. Guarded aggregate PASS SHA-256 is
`3f534d2b18ef29aef6aba54cd1a966bf236587eebab1edd0eb2168f957912ec0`.
It finished in `0.9456400555` seconds (guard admission 14.5 GiB host / 1.19
GiB cgroup). Its exact floor-reciprocal sum is
`38076205721896677243304421 / 10^30`. The adjusted rowwise lower saving is
`152066974999277949267719 / 4000000000000000000000000000` (equivalently
`38016743749819487316929750 / 10^30`). The exact margin to the post-refit
requirement is
`5474084304921368677 / 32000000000000000000000000000`; the margin to the
direct Lean threshold `3801674/10^11` is
`14999277949267719 / 4000000000000000000000000000`. Both comparisons are
strict. All chunk and aggregate claims remain exact external computation, not
Lean proof.

Replay inputs were pinned as follows: prime-list SHA-256
`6e87d9e9a3f8cf4a77223a04b618128f373d00f923a7c679b6bf01ad43f9bb18`,
arithmetic-catalog JSON SHA-256
`e26483aaaaa3caf0ca10f3872632b7653e000b85c5040bcb3100a013820e134c`, H7
archive SHA-256
`43669734971ae82bdf2980bbacd869a65224fe3cececb121cf2fbc14936813f2`, and
threshold manifest SHA-256
`82d4071437dbef99016cfd160549e7dae4094cd2195f2e2ed050f922774ecffd`.
The manifest pins all 34 Lean table source files; every hash is copied into
each chunk and the aggregate receipt. The v1 replay script SHA-256 is
`67fa2cf484aabadc32a3230e9ed521420bc57330b34d0c936f5ce96d7ca4a2f4`.

The first 1,000-prime chunk used this guarded command and the shared lock:

```sh
python3 automation/lean-formalization/guarded_build.py \
  --timeout-seconds 900 \
  --lock-path /tmp/lean-formalization-1000.build.lock \
  -- python3 lean-formalization/verification/sol-luna-20260923/factor-inventory/replay_finite_support.py \
  replay --start 0 --stop 1000 --max-chunk-size 5000
```

The seven-base Miller-Rabin test used by the script is deterministic for
inputs below `2^64`; every replayed prime is explicitly bounded by
`p < 2^38`. The four large chunks used the specified shared lock and 900-second
cap, serially. A first aggregate attempt reached all checks but exited on a
stale output-field name; after fixing the printer, the guarded aggregate above
passed. The unsuccessful invocation is a tooling failure, not a numerical
counterexample.

This replay validates a concrete list and all finite arithmetic without
floating point. It remains *external computation*: the Lean kernel
would not thereby know that the listed integers are prime or satisfy the raw
field certificate. A Lean endpoint must import proof terms for those facts,
form the explicit finite sets, and invoke the existing actual-index and
actual-defect bridges. Since the goal is a lower bound, no proof that the
list exhausts every eligible prime is needed; proving that these listed
primes belong to disjoint certified bins suffices.

## Feasibility and blockers

The earlier source-size estimate for PrimeCert plus packed residue/parity
data is about 228 bytes per prime, or roughly 88 MB for 387,955 primes before
compiled `.olean` artifacts. The current checked 1,000-prime support consumed
920 seconds for its final aggregate at 3.03 GiB peak RSS, after 109 direct
module checks had consumed 4,959.53 observer seconds. Those figures do not
justify a one-shot 388k Lean build under the 900-second/4-GiB policy. A
chunked approach would reduce per-job memory, but the repeated modular
certificate work remains on the order of hundreds of millions of exponent
steps (existing 1,000-prime benchmarks count 633,504 binary steps across the
24,000 powers). The uncompiled split-coordinate source offers a possible
constant-factor reduction, but not a checked or measured 388k-scale method.

The full exact replay completed in 214.19 seconds of chunk time plus 0.95
seconds for aggregation. Each job stayed within the 900-second timeout; guard
admission reported more than 1.19 GiB cgroup headroom throughout. This closes
the finite list-validation and exact arithmetic route as reproducible
external evidence. It does not close the actual-field theorem without Lean
prime and certificate terms.

### Lean completion strategy

The shortest proof route is an explicit finite support from these
387,955 primes, split into disjoint 100- or 1,000-prime blocks. For every
listed prime, generate a PrimeCert Pocklington proof, seven genus Euler-power
proofs, 17 catalog Euler-sign proofs, seven completed parities, and one
retained witness. Reuse the existing `Certificate`, then apply the binwise
`datum_centralSaving_lower` and actual-defect bridge. The finite support need
only be a certified subset; a completeness proof for all eligible primes is
unnecessary.

The representation is compact on disk but not compact to check. The
[PrimeCert review](../../../astra-sol-20260920/central-census/primecert-review.md#L67)
estimates PrimeCert plus packed residue/parity data at about 228 source bytes per
prime (roughly 88 MB before `.olean` files). The existing 1,000-prime
support took 4,959.53 observer seconds across direct checks, and its final
aggregate alone took 920.38 seconds at 3.03 GiB peak RSS. Linear extrapolation
places a 388k proof far beyond the remaining work window, even if split into
small jobs. The old 24-power representation accounts for roughly 246 million
binary exponent steps at this scale.

[`CentralCensusSplitCoordinateRun20260920b.lean`](../../../UnitDistance/CentralCensusSplitCoordinateRun20260920b.lean#L1)
is the prepared compression idea: derive a quadratic-algebra Euler power from one scalar split power,
norm-square and root receipts, Fermat, and two-root injectivity. The source is
uncompiled and unbenchmarked. It can reduce the cost of each of the 17 catalog
checks by replacing quadratic-algebra arithmetic with scalar arithmetic; it
does not remove per-prime primality, seven genus checks, or all finite support
membership. It is a possible constant-factor gain, not a plausible 388k
kernel proof under the measured time and 4 GiB policy. No such compile was
started.

## Worker usage

The five replay chunks used `214.18961997` script seconds; the successful
aggregate used `0.94564006` seconds (the first aggregate printer-error retry
is excluded). The successful summary SHA-256 is
`3f534d2b18ef29aef6aba54cd1a966bf236587eebab1edd0eb2168f957912ec0`; the
v1 checker source SHA-256 is
`67fa2cf484aabadc32a3230e9ed521420bc57330b34d0c936f5ce96d7ca4a2f4`. Every
job was
guarded with the shared `/tmp/lean-formalization-1000.build.lock`, a 900-second
cap, and unchanged guard thresholds. Worker CPU time and peak RSS are
unavailable, not zero; per-job guard admission metrics are listed above.
No Lean compile or kernel proof was run for this endpoint.

## Replay hardening follow-up (v1 receipts retained; v2 replay passed)

The independent source review found that the successful v1 runner used Python
`assert` statements for validation. Its documented `python3` runs had
assertions enabled and the completed v1 receipts remain valid evidence, but a
`python3 -O` run could remove those checks. The review also noted that v1
receipts did not bind themselves to a checker source hash.

Before changing the working runner, all v1 receipts were copied unchanged under
[`finite-support-replay-v1-20260923/`](finite-support-replay-v1-20260923/).
The five chunk and aggregate JSON files retain the hashes recorded above and
record historical runner hash
`67fa2cf484aabadc32a3230e9ed521420bc57330b34d0c936f5ce96d7ca4a2f4`. The
historical v1 source file itself is unavailable in the current workspace; the
recorded hash is provenance from the original run, not a claim that the source
was preserved here.

The v2 runner source hash is
`355ffb18c6111e971a1ccf51929042f3450fc05ba8086d4630e6af6f2bbf06c5`. Its
changes are limited to execution/evidence hardening: it immediately raises if
Python optimization disables assertions; records its source SHA-256,
`sys.flags.optimize`, and `__debug__` in each chunk and aggregate; and makes
aggregation reject chunks whose runner hash or interpreter mode differs. It
also checks the `Datum` upper bounds are strictly ordered. It keeps the same
mathematical checks, data inputs, and pinned input hashes, and writes to new
`finite-support-replay-v2-20260923/` and
`finite-support-replay-v2-summary.json` paths.

Offline checks passed: Python byte-compilation, normal-mode `--help`, a
subprocess check that `python3 -O ... --help` fails immediately with the
assertions-required error, and `git diff --check`. All five v2 chunks and the
aggregate then passed serially under
`automation/lean-formalization/guarded_build.py`, with explicit lock
`/tmp/lean-formalization-1000.build.lock` and a 900-second cap per job. Guard
admission and chunk receipt hashes were:

| Index range (stop exclusive) | Primes | Replay seconds | Guard admission (host / cgroup GiB) | V2 receipt SHA-256 |
|---|---:|---:|---:|---|
| 0–1,000 | 1,000 | 0.4833 | 14.1 / 1.39 | `7e1906b26d425b0d8ec0f75f90dad4c10f5281791fc91ab4ec3286c20b1f1592` |
| 1,000–101,000 | 100,000 | 53.3735 | 14.0 / 1.38 | `5b6ec56a5494bd8bd438f19f0f3d856f509f5a61f7a2939cf620c668937558a6` |
| 101,000–201,000 | 100,000 | 55.7574 | 15.0 / 1.20 | `2298fd817f59a121fb78e232e035b337300ec6e9127e17a7b58d0cb51d09eb2b` |
| 201,000–301,000 | 100,000 | 57.2602 | 14.0 / 1.19 | `28111d3c2c801b1e283f43d932ce4a9eea4017cc9b98e682ff6c93227e9e8dd4` |
| 301,000–387,955 | 86,955 | 50.5455 | 15.0 / 1.20 | `37b05cd84d6a7e6da4a91c5ab8660f8a0542dce5af42b48e7f9a79c246a473aa` |

The v2 aggregate passed in `0.93953846` seconds (guard admission 14.5 GiB
host / 1.19 GiB cgroup headroom), with SHA-256
`4dc185f54b27a773bca15a4d39eaae6de7c4d0488f3d90b9ea85c935b61da07d`. The
five chunk runs totaled `217.41979905` script seconds; all six jobs passed and
the lowest admission headroom was 1.19 GiB. Every chunk and aggregate records
the same source hash, optimization level zero, and debug assertions enabled;
the aggregate checked these fields before combining receipts. Its rowwise
saving is
`152066974999277949267719 / 4000000000000000000000000000`, with strict exact
margins `5474084304921368677 / 32000000000000000000000000000` above the
post-refit requirement and
`14999277949267719 / 4000000000000000000000000000` above the direct Lean
threshold. Worker CPU and peak RSS were not measured and are recorded as
unavailable, not zero. This remains exact external computation and does not
convert the result into a Lean proof.
