# Exact target aggregation of all 32 H6 quadratic expint rows

## Result

The source-pinned Fraction checker **PASSES**. It substitutes the 32 direct
expint upper endpoints into their H6 inherited sector sum and the
mixed-quadratic group input, retaining the original sector-sum outward
rounding slack. Row multiplicities total 32 and match the inherited sector's
factor count; the row-wise frozen and direct endpoints match the batch
receipt exactly.

The sum of all 32 positive target-minus-direct row margins is exactly

`33042173493187893057900326884279802675077326081844816299084309047951299307003449420392482976918034241/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792`

(approximately `1.637873330160229e-18`). The updated exact mixed-quadratic
group upper remains below its rational allowance
`400886873183882259/1000000000000000000`. The updated group slack is

`196779691088030316751652087065885787076111131282221990375374954548870899369516153378449313484110681637934063338237/769570433523329672114825001955929957130463657626278255233365105551674253349554894754184887790721008609504452935680000000000000000`

(approximately `2.557006903021371e-18`). The normalized exact table
contribution changes by `2/16384` times the group change, approximately
`-1.9993570924807484e-22`.

Because the same rational mixed-quadratic allowance remains valid, the
published dimension-weighted table bound and inherited five-rational target
assembly are unchanged. The final rational upper remains
`2108090946974047476569229/50000000000000000000000000`
(`0.04216181893948094953138458`), below `42161819/1000000000`; the final
ceiling slack remains
`3025952523430771/50000000000000000000000000`.
Here `42161819/1000000000` is the tighter inherited manuscript ceiling. The
package H threshold is `42165819/1000000000`; the same final upper has package
threshold slack `0.00000400006051905046861542`.

## Provenance and resources

- Checker:
  [`h6_target_batch_aggregate.py`](h6_target_batch_aggregate.py), SHA-256
  `9de12672586525793d728032579a4fb3b8f9329a939cb9a5e86e0d0204714d71`.
- Result:
  [`h6_target_batch_aggregate.json`](h6_target_batch_aggregate.json), SHA-256
  `e65fa928f5a4c2d0568aff3aa9cf37fd6034838f353884601d55810b6b0e6609`.
- All pinned source and receipt hashes were independently rechecked. The
  consolidated analytic replay's two source maps contain the inherited
  H6 target receipt digest, and `all_analytic_factors_reevaluated` is true.
- The exact table assembler and inherited AFE evaluator are hash-pinned; the
  checker follows their mixed-quadratic grouping and row-multiplicity rules.
- Guard admission: 16.4 GiB host memory, 1.41 GiB cgroup headroom, 900-second
  timeout. The Fraction-only check completed in `0.11784284096211195`
  seconds and exited 0. Peak RSS was unavailable.

## Limits

This is exact rational aggregation of already computed direct upper
endpoints. It adds no independent AFE evaluation and does not prove the
expint row identities, functional equations, Dirichlet-series and
contour-growth conditions, global coefficient or tail bounds, or completeness
of bad Euler factors. Those remain conditional premises recorded in
[`h6-target-sigma-expint-report.md`](h6-target-sigma-expint-report.md) and the
32-row batch report
[`h6-all-quadratic-expint-report.md`](h6-all-quadratic-expint-report.md).
The earlier pointwise `SplitKernels` strict row **FAIL** remains unchanged;
this aggregate calculation and the direct expint endpoint passes are separate
evidence and do not prove `H`.
