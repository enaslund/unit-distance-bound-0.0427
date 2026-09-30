# H6 target-sigma expint receipt and Lean transcription review

Bounded read-only review of `h6_target_sigma_expint.json` against the frozen
target row and
`UnitDistance/H6TargetExpintRowArithmetic20260923.lean`. The expint source
implementation is being reviewed separately. No numerical or Lean job was
run.

## Target row and receipt binding

The receipt reports **PASS target-sigma independent expint H6 AFE row** for
mask 1586, twist +1, degree 2, multiplicity 1, conductor 240240,
`gamma=[0,1]`, root number +1, sigma 12001/12000, cutoff N=3922, 562 nonzero
coefficients, and 184 moment bins. The structural fields match the selected
H6-low target row in `h7-inherited-euler-12000.json`. The target JSON digest
matches the receipt's target digest and both source bindings in the
consolidated analytic replay; that replay records
`all_analytic_factors_reevaluated=true`.

All seven source hashes in the expint receipt match the current files. The
checker hash also matches. Key digests are:

- Expint receipt: `56aa4b9fddbe580d852119f79329635c06630d2833315857b581fe1aa0bb4e2f`
- Expint checker: `1f600865d5cf895d2895c54b871a64763c11ae7d197722fb7e7b67eff8e1d6c0`
- Lean arithmetic source: `a6138198cafd39d308589869a265f6bc112281e442ddb96482158d3c6a091e92`
- Frozen target row JSON: `b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f`
- Consolidated analytic replay: `34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e`

## Exact dyadic transcription

The Lean `expintRowUpper` exactly equals the receipt's direct `log_L_S_upper`
dyadic upper endpoint, and `frozenRowUpper` exactly equals the target
`log_abs_L_S_upper` dyadic upper endpoint. Their exact target-minus-direct
margin is the receipt's positive fraction:

`2645493595506194724895404576742654389806769595866372365059405955570979615756270591455023231129957 / 78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632`

This is approximately `3.3570544381928877e-20`. It is positive, matching the
Lean theorem's strict comparison direction and the receipt's `pass=true`.

## Separate prior SplitKernels result and scope

This expint row PASS is distinct from the prior target-sigma
SplitKernels pointwise replay, which remains **FAIL** by approximately
`4.4458065915680757e-26` and has a recorded interpolation consistency
discrepancy. The expint receipt explicitly preserves that prior status and
its receipt hash. The expint route derives weights using Arb's generalized
exponential integral instead of `SplitKernels`, but uses the same Arb/FLINT
interval backend; this review does not independently verify the formula or
the source implementation.

The Lean leaf certifies only rational comparison of the transcribed
endpoints. The external expint endpoint remains conditional on the row
identification and functional equation, the Mellin contour shift's stated
growth/decay conditions, complete bad Euler factors, the global coefficient
bound and tail estimate, and valid outward Arb/FLINT enclosures. Neither
receipt nor Lean leaf proves the global hypothesis H.
