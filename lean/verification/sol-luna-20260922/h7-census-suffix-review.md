# H7 stored-census suffix replay

## Result

The independently written checker `h7_census_suffix_check.py` completed its guarded run and emitted `PASS independent finite-field suffix/bin replay`. The output receipt is `h7_census_suffix_check.json`. The checker compared every generated census bin touching the requested prime range `[10^7,10^8)` against the stored full-census table, including the full contents of the two bins that cross the requested endpoints. It also checked one distant complete bin containing `10^10`.

All 2,306 compared bins matched exactly: 2,304 nonempty rows and 2 bins whose expected and regenerated rows were both zero. Of the suffix bins, 2,303 are wholly inside `[10^7,10^8)`; they run from `(10,005,659,10,015,665]` through `(99,887,683,99,987,571]`. The two straddling bins were `(9,995,663,10,005,659]` and `(99,987,571,100,087,559]`. The additional distant bin was `(9,994,087,141,10,004,081,229]`.

For each bin the comparison covers total selected-prime count, the exact integer sum of `floor(10^30/p)`, and the completed/complement count and reciprocal-floor splits. The lower-boundary fragment `(9,995,663,10,000,000]` was also independently compared against the bundled 10^7 prefix data and matched in all eight row fields. Across the sieved intervals the script found 42,847 genus-split primes, 42,845 selected primes, 42,534 completed primes, and 311 complement primes. These totals include the entire straddling bins and the distant bin, not only primes inside the requested suffix.

## Method and provenance

The checker imports neither the original census producer nor the earlier prefix checker. It regenerates primes by a segmented sieve, recomputes the 180 allowed residue classes modulo 120120, evaluates all 17 stored norm-form characters by modular square roots and Euler's criterion, applies the 19 stored first-hit predicates, and accumulates the reciprocal floors using integer division. It reconstructs the geometric bin edges independently and uses the producer's `(lo,hi]` assignment convention. Each computed eight-field row is compared to the pinned table row; a missing row is compared to an all-zero row.

The run receipt pins these SHA-256 values:

- Full census table: `43669734971ae82bdf2980bbacd869a65224fe3cececb121cf2fbc14936813f2`.
- Census source: `3bf8a7af2e4b9d219e9ddc6f35631333fa67dc283291b0c1040332a1487be493`.
- Euler source receipt: `4f01e9ae1f0f79f6575955745c1bdf6ce349a03b6990e2e4189a5205426088af`.
- Independent prefix data: `fafbdaff49c1317d2606df81ca886fea6fb01200b4da7d490e7550bb84b342b3`.
- This checker in the run: `f0505fc9f074c364547862b2744efa63b053eb3bd11f71ad79d53a86e9d3f4c5`.

The Euler receipt is checked to bind both the table and census source hashes. For archive portability, the checker uses the bundled `numerics_h7_census_full.txt` if the research-tree table is absent. The source file itself may also be absent in an extracted package; in that case its pinned hash is still required to match the source hash recorded in the hash-pinned Euler receipt. The research-checkout path was exercised in the original run. The bundled-table fallback was subsequently exercised successfully in the extracted candidate-11 package: `verification/conditional-20260922/package-smoke-11.json` records `h7_census_suffix_check.py` with exit code 0 (archive SHA-256 `acffe3c96e8183e62631fa5351ac12b761f79bcb3cef627e7bcb9fb1e4576cf9`).

## Scope

This is a finite independent consistency check over the stated bins, not a proof of the infinite-prime statement or of every stored census row. The distant check covers just the one bin containing `10^10`. The exact finite comparisons depend on the correctness of the hash-pinned table/receipt and on the stated finite-field norm-form interpretation. The run does not establish that interpretation beyond reproducing the stored arithmetic predicates.
