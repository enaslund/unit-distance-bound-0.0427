# Independent audit: H6 target batch aggregate

## Scope

Read-only audit of `h6_target_batch_aggregate.py` and its JSON receipt. I
recomputed file hashes and exact receipt equalities with Python `Fraction`;
I did not rerun either the batch evaluator or this aggregate. Checker SHA-256
is `9de12672586525793d728032579a4fb3b8f9329a939cb9a5e86e0d0204714d71`,
matching the receipt. Receipt SHA-256 is
`e65fa928f5a4c2d0568aff3aa9cf37fd6034838f353884601d55810b6b0e6609`.
All ten declared pins match their files.

## Findings

The receipt's exact rational arithmetic is internally consistent:

- The source, batch, and target tables are matched by twist; the receipt has
  32 unique twists with multiplicity total 32. The checker verifies each
  row's multiplicity, conductor, cutoff, row pass, exact frozen endpoint, and
  exact positive endpoint margin against the inherited target row.
- The weighted frozen and direct row sums recompute from all 32 row records.
  Their difference equals the sum of the 32 positive margins. The replacement
  delta is exactly `direct_row_sum - frozen_row_sum` and is negative.
- The inherited sector sum upper exceeds the frozen row endpoint sum by the
  exact nonnegative slack
  `671/5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448`.
  Retaining this slack while replacing the row endpoint sum is conservative.
- Adding the replacement delta to the old mixed-quadratic group upper gives
  the recorded new group upper exactly. The new slack against the unchanged
  group allowance is positive. The dimension normalization is `2/16384`;
  the normalized delta is negative.
- The exact `dimension × rounded group allowance / field degree` identity
  still matches the inherited table Y and remains below its Y allowance.
  The five-allowance formula reproduces the original final rational upper
  exactly, still below the ceiling, with slack
  `3025952523430771/50000000000000000000000000`.

The source binds the inherited target receipt in both consolidated replay
maps and pins the arithmetic table, both aggregation source files, the direct
32-row expint source and receipt, the one-row expint receipt, the historical
SplitKernels FAIL, and prior single-row aggregate PASS. Its checks align with
the pinned aggregation definitions: the mixed-quadratic group is the sum of
degree-two sector upper endpoints, and an inherited H6 sector endpoint is
the multiplicity-weighted sum of its row endpoints.

The PASS is specifically a **fraction-only conservative substitution**.
It does not lower the published rounded group allowance or change the final
H rational upper; it shows that substituting the accepted all-row direct
expint endpoints leaves the same allowance valid. It does not establish the
rows' factor identities, their analytic assumptions or coefficient bounds,
or H independently of the other pinned inherited receipts. The pointwise
SplitKernels strict-row FAIL remains separate and unchanged.

No expensive job was run; resource counters are unavailable, not measured as
zero.
