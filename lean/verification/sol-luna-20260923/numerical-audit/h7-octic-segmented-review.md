# H7 segmented octic replay: independent post-run review

Read-only review of `h7_octic_segmented_direct.py`,
`h7_octic_segmented.cpp`, and the completed receipt
`h7_octic_segmented_direct.json`. No rebuild or replay was performed.

## Receipt checks

The receipt reports `PASS full independent segmented coefficient and exact
moment replay` for sector mask 1824, twist +1, conductor
208190684989647360000, through `N=360720360`. It checks all 544 of 544 bins
and 548127 nonzero coefficients; the frozen full count is also 548127. The
first 128 coefficients match and `mismatches` is empty. The frozen bin counts
sum to 548127, agreeing with the declared fixture count and replay count.

I recomputed the SHA-256 hashes of every source listed in the receipt; all
match. In particular, the checker hash is
`80a77de8c41a4f92f4fcd0bb9670dcdb6483fd9801d4be19212b4423ac1285da`, the
segmented C++ hash is
`170c443cc85821ea2bd1252df0b05b4322c20762692a410d8f9640cd721595bb`, and
the pinned arithmetic, frozen moments, moments helper, sparse producer, and
tail helper hashes match their recorded values. The receipt records binary
SHA-256 `cd5bda9679a0837791e7e7e5868db2d3c451cfe011ce8d7ce2fd964b8f616203`
and a compile command that builds the reviewed C++ source. The temporary
executable has since been removed, so its recorded digest could not be
independently recomputed. Metadata and bin-layout hashes are recorded in the
receipt; I did not regenerate them because importing the pinned helper fails
in this environment with `ModuleNotFoundError: flint`.

## Row binding and false-pass review

The squareclass correction is present. The arithmetic sector is selected by
mask 1824, while the C++ code derives the twist squareclass from the row's
`d=+1` and asserts `row.d==1 && row.mask==0`. The sector identifier and the
twist character squareclass are therefore checked independently.

The wrapper rejects Python optimized mode, has no prebuilt-binary override,
and compiles its own C++ source. It records the compile command and resulting
binary hash. Compile, process, and parse failures produce explicit failure
receipts. On success, the parser checks the output structure, and comparisons
cover row identity, cutoff, nonzero count, all fields in every selected bin,
and the first 128 coefficients. I found no practical false-PASS path in the
reviewed execution path. Source hashes are collected after the run, so they
would not detect a concurrent edit-and-restore during execution; no evidence
of such a condition appears in this receipt.

## Scope

This is a finite coefficient and exact moment cross-check for one H7 mixed-
octic row. It does not recompute an AFE endpoint or establish the global
coefficient bound, representation identification, conductor, functional
equation, or the target H claim. The receipt also states that prime-label
arithmetic helpers are shared with the pinned producer, while coefficient
factorization and full-bin aggregation use a separate traversal.
