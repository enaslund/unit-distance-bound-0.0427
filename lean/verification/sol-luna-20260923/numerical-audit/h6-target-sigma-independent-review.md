# H6 target-sigma replay: independent bounded review

Read-only review of `h6_target_sigma_direct.py`, its receipt, and the later
exact aggregate replacement receipt. No numerical or Lean job was run.

## Target row and binding

The target direct receipt identifies the H6-low sector mask 1586, twist +1,
degree 2, conductor 240240, cutoff N=3922, multiplicity 1, and sigma
12001/12000. These fields agree with the selected row in
`h7-inherited-euler-12000.json`. The target receipt hash is bound at both
locations in the consolidated analytic receipt: its printed-table source
map and the analytic replay input map. Both maps match the target receipt
SHA-256, and `all_analytic_factors_reevaluated` is true.

The direct checker reconstructs 3,922 coefficients, matches the complete
signed-vector hash, and checks all 184 exact moment bins. I verified all 12
source hashes and the checker hash recorded by the direct receipt against the
current files. The aggregate replacement receipt's five input hashes and
script hash also match the current files.

## Row comparison and aggregate replacement

At the target sigma, the direct row upper exceeds the frozen row upper by
exactly

`3503473977378734678796183364994491634330168811173005498416628575442218183323135852792921985 / 78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632`

or approximately `4.4458065915680757e-26`. The target row comparison remains
**FAIL**. One component consistency check also remains false: the direct
interpolation upper exceeds the target interpolation upper by exactly
`7 / 46517678354918840995156723704832290198633047083988355858015372747560914439257467092876227245680868195888801382801035387746214504231337984`,
approximately `1.5048042480950279e-136`. The other recorded consistency
checks pass. The direct endpoint and replacement are therefore presented
with this discrepancy visible, not as a row-level pass.

The target-sigma replacement receipt adds the direct row increment to the
exact mixed-quadratic group input. The new exact group upper remains below
the same rational group allowance, `0.400886873183882259`, with exact
remaining slack approximately `9.191335284030761e-19`. Its normalized exact
AFE increment is approximately `5.4270099994727486e-30`. Since the rounded
group allowance is unchanged, the receipt keeps the final rational upper at
`0.04216181893948094953138458`, below `0.042161819` with slack
`6.051905046861542e-11`. Thus the wider target-sigma row upper still fits the
target mixed-quadratic group allowance, while its individual row comparison
remains **FAIL**.

This is separate from `h6_aggregate_replacement.json`, which substitutes the
off-target-sigma row at 6001/6000 into the H6 low-degree sum. That older
aggregate pass does not establish the target-sigma result. The applicable
target-sigma group calculation is `h6_target_aggregate_replacement.json`.

## Evidence class and limits

Coefficient reconstruction, its vector hash, and the finite moment checks
are exact finite computations. The direct AFE endpoint uses external
python-flint/Arb interval arithmetic and reuses the pinned `SplitKernels`
implementation; the standard-library `Fraction` replacement propagates that
endpoint exactly into the group sum. This does not independently verify the
kernel derivation or the consolidated full-table replay.

The endpoint remains conditional on the row's representation/factor
identification, conductor, gamma and root data, functional equation,
completeness of removed bad Euler factors, the global `|a_n| <= d_2(n)` bound
and resulting Rankin tail, and validity of the pinned kernel remainder and
outward Arb computation. Neither receipt proves the global hypothesis H.
