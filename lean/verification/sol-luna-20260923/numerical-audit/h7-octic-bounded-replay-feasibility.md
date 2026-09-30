# H7 mixed-octic bounded full-bin replay feasibility

Status: 256-bin pilot PASS and full 544-bin replay PASS under the guarded
helper. Both were finite coefficient/moment comparisons only.

## Candidate row

Use the mask 1824, twist +1 row in
`publication/nonabelian-dyadic-lower-bound/research/octic-arithmetic-h7-274.json`:

- degree 8, mixed gamma `[0,0,0,0,1,1,1,1]`, root number +1;
- no quartic Dirichlet phase (`quartic_exponent = 0`);
- conductor `208190684989647360000`;
- sigma `6001/6000` cutoff `N=360720360` from the evaluator's
  `floor(sqrt(Q)/40)` rule (with the stored minimum/cap);
- frozen sparse receipt has 548,127 nonzero coefficients and 544 bins,
  using degree-20 moments.

This is the smaller-conductor row of mask 1824. Its twist -1 partner has
conductor `53296815357349724160000` and is capped at `N=3000000000`; do not
include that partner in the bounded job. The 360-million cutoff is why a
literal dense coefficient vector is unattractive, but it does not prevent a
segmented computation.

The wrapper binds the selected arithmetic row to the existing moment row on
conductor, gamma signature, root number, all seven bad-prime denominator
polynomials, and first 128 coefficients. It selects exactly the `twist=+1`
row with `quartic_exponent=0`; no other mask-1824 row is accidentally
included. The cutoff agrees with the frozen bin layout: bins are adjacent,
start at 1, and end at 360720360. The first 256 original bins also form a
contiguous prefix, ending at `N=39746` in bin 521; their frozen nonzero counts
sum to 263, so this pilot checks beyond the first 128 coefficients.

## Independent full-bin method

The frozen sparse producer, `octic-sparse-moments.cpp`, recursively enumerates
the multiplicative support and accumulates all moments. The checker in
`h7_octic_segmented_direct.py` plus `h7_octic_segmented.cpp` uses a different
traversal: scan the integer interval in fixed-size blocks, factor each block
with a remainder array, multiply the local degree-eight Euler coefficients,
and immediately add nonzero terms to their frozen bin's exact signed and
absolute moments. Discard each block before advancing. This stores no
`N`-length coefficient vector and does not reuse the producer's support
recursion. Its default pilot mode checks the first 256 original bins; `--full`
selects all 544 bins and every integer through N.

For this row, the source arithmetic supplies the exact genus/norm data and the
row supplies its bad-prime denominator polynomials. The checker streams prime
classification into one byte of twisted local-code per integer through the
selected cutoff (about 361 MB only in full mode), then applies those labels in
the segmented local-factor scan. It does not retain the producer's temporary
vector of prime records alongside the table. This is a prime-character lookup
table, not a coefficient vector.
Compare the complete
544-bin structures (lo/hi/midpoint, mass, count, and all 21 signed and
absolute moments) and the nonzero count against the frozen receipt. This
checks substantially more than the first 128 coefficients; it covers every
integer through the cutoff and all frozen bins. Arithmetic-label construction
is shared input; coefficient accumulation and bin contraction are a new
implementation, so this would be a distinct cross-check but not a new analytic
kernel backend.

The degree-20 bins are AFE inputs, but this replay alone is only an exact
coefficient/moment cross-check. It does not recompute either finite AFE sum,
the interpolation/tail debit, bad-factor AFE multiplier, or log endpoint. The
tail script's use of `|a_n| <= d_8(n)` globally is not established by this
replay. It also does not prove the conductor, factor identification,
functional equation, or H.

## Cost and limits

At 360,720,360, the independent implementation makes two segmented prime
passes (label construction and coefficient/moment accumulation), each
`O(N log log N)` sieve work with roughly `N * sum_{p <= sqrt(N)} 1/p` small-
prime factor visits, then 548,127 nonzero moment updates. Block size is
`2^20`. Exact fixed-size C++ buffers are: code table 360,720,361 bytes;
remainder array 4,194,304 bytes; coefficient array 8,388,608 bytes; prime
label sieve scratch 1,048,576 bytes; genus lookup `2,042,040 * sizeof(int16_t)`
bytes; plus at most about 2,200 small primes and 544 bins of GMP accumulators.
Even allowing 10 MiB for all GMP limb storage and 64 MiB for process/runtime,
the source-level bound is below 0.5 GiB. These are not measured RSS. Runtime is
likely minutes rather than seconds; retain a conservative 600-second estimate
within the 900-second guard, one worker. Pilot mode ends at `N=39746` for 256
bins and uses about 40 KB for the code table, so it exercises the bounded
pipeline without a full-cutoff allocation. The existing producer receipt for
both mask 1824 twists reports 43.13 seconds, but that is not evidence for the
new independent scan and does not measure its resources.

The wrapper refuses `python -O`, always
compiles the pinned local C++ source itself, and records source hashes,
compiler command/flags, and the resulting executable hash. Compile, process,
and parser failures write diagnostic JSON before returning failure; no
arbitrary `--binary` path is accepted.

## Pilot execution record

The guarded pilot command was:

```sh
PYTHONPATH=/tmp/unit-distance-flint CPPFLAGS='-I/tmp/unit-distance-deps/usr/include -I/tmp/unit-distance-deps/usr/include/x86_64-linux-gnu' MOMENT_LDFLAGS='-L/tmp/unit-distance-deps/usr/lib/x86_64-linux-gnu -Wl,-rpath,/tmp/unit-distance-deps/usr/lib/x86_64-linux-gnu -lgmpxx -lgmp' python3 automation/lean-formalization/guarded_build.py --timeout-seconds 900 --lock-path /tmp/lean-formalization-1000.build.lock -- python3 lean-formalization/verification/sol-luna-20260923/numerical-audit/h7_octic_segmented_direct.py --pilot-bins 256
```

The first admitted attempt compiled but stopped immediately at a mistaken
internal assertion equating the twist squareclass with the sector mask. It
did not reach any coefficient scan. Its failure JSON is preserved as
`h7_octic_segmented_pilot_attempt1.json` (SHA-256
`6c609933e539214790e6bc47b35300d86eff0f3e55eac5ff5e7ab1410efffd4c`). The
assertion was corrected (`d=+1` has row squareclass 0; sector mask is 1824).

The corrected pilot attempt was admitted with 14.1 GiB host available and
1.46 GiB cgroup headroom. It passed all first 256 frozen bins through
N=39,746: the 263 nonzero terms, first-128 coefficient prefix, each bin's
boundaries/midpoint/mass/count, and all 21 exact signed and absolute moments
matched. No mismatches were reported. Script runtime including compile was
3.16236 seconds. Peak RSS was not available from the guard/tool output. The
successful JSON receipt SHA-256 is
`925196065e88f3a4e4d8a1df917c9229768aac2b5417d3c6675308e4021ae34d`; binary
SHA-256 is `cd5bda9679a0837791e7e7e5868db2d3c451cfe011ce8d7ce2fd964b8f616203`.
The successful pilot JSON at the default output path was subsequently
overwritten by the full-run JSON. Captured pilot metrics and hashes are
preserved in `h7_octic_segmented_pilot_summary.json`, whose preservation note
explains this limitation. The original first-attempt failure is preserved
byte-for-byte in `h7_octic_segmented_pilot_attempt1.json`.

The parent then allocated a full-row run using the same command with
`--timeout-seconds 1800` and `--full`. It was admitted with 13.9 GiB host
available and 1.44 GiB cgroup headroom. It completed in 35.166353 seconds
including compilation, with no guard stop. All 544 bins and all 548,127
nonzero coefficients matched; each bin's index/range/midpoint/mass/count and
21 signed plus 21 absolute exact moments agreed. The first 128 coefficients
also matched, and the mismatch list is empty. Peak RSS was not available.
Receipt SHA-256 is
`efaeeff42730d13cfb4e25ed94d551ba511f4f0604d059d6bca5b59af8883d28`; full
bin-layout SHA-256 is
`4591f7bdfdb363ea4402fa334ffe0c543723fc24a5ac32b33a7432dad97aeb21`; raw
stdout SHA-256 is
`b9dec5d2749ed76497297e4749ef2b194698b361e0a6eac4f0e638e49c06d385`. The
compiled executable hash and all inputs/source hashes are in the receipt.
The shared lock was released after successful exit. The binary's temporary
directory was cleaned, so its recorded hash could not later be recomputed. A
read-only post-run source review is in `h7-octic-segmented-review.md`; it
recomputed source hashes, confirmed row binding and counts, and found no
practical false-PASS path. The reviewer could not independently recompute
the metadata hash because `flint` was unavailable in that environment.

## Provenance pins

- `octic-arithmetic-h7-274.json`:
  `2c8d752f6206b6793b37d91ca9ad343b6c3c4ff92f61fed9ade9e307f0013836`
- `h7-octic-moments-1824.json`:
  `e61657ff8a8d112f1ac76941264bc74b98a2f30b8ed0d3c0fbf953a21b0f128d`
- `h7-octic-moments.py`:
  `429283aa8a909d554438da03c7c1edb6a4d62309809c4d0366c49ce9402d5e2c`
- `octic-sparse-moments.cpp`:
  `e886396848f72df09a78d3124de6cb1f08056dbdac644b630adf1354404bd755`
- `h7-octic5-moments.cpp`:
  `b8be7a287d732821f19a6d18d6ffc22b5dda8d437ae795448fc7ba6911755f00`
- `octic-sparse-tail.py`:
  `293ebc05500c0c8557f8bc76e3c8fd3b0b3857b440e3648866288ce45cf20e85`

The existing mask-1824 sparse receipt reports the selected row as
`N=360720360`, 548,127 nonzeros, and 544 bins; the existing producer reported
43.1276 seconds for both mask-1824 rows together. The segmented checker has
also passed its independent full-bin replay. Its prime-label scan reuses the
pinned source's arithmetic helper routines and copies its prime-classification
formulas into a streaming byte-table builder; its coefficient factorization
and full moment aggregation are separate.
