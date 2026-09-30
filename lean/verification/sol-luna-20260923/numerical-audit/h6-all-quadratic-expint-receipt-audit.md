# Receipt audit: H6 all-quadratic expint replay

## Scope

Read-only audit of `h6_all_quadratic_expint.json` against the staged checker
and pinned inputs. I did not rerun Arb or the replay. The checker SHA-256 is
`060af68df4b7e1eb6dfba87e88ca13fa26cbccca16966c2c256b4fc8cd2116c3`, matching
the receipt. Receipt SHA-256 is
`54e9fe4921c92366da8644e27bd8d2217a04b678046dfa3c31701519b4c917ce`.
All nine declared source/receipt pins match the current files.

## Findings

The summary reports `PASS all 32 H6 quadratic rows by direct expint replay`,
with 32 row records, no endpoint failures, and no consistency failures. I
checked that all 32 twists are unique and that each row has
`row_comparison_pass: true`, `overall_row_pass: true`, and all four consistency
checks true. The aggregate counts are 164,712 coefficient positions,
22,776 nonzero coefficients, and 45,552 generalized-expint calls; precision
is 384 bits and the receipt records 6.48 seconds.

The smallest exact target-minus-direct margin is for twist `55`, conductor
`15015`, cutoff `N=981`:

`3245525081529026119997427115675961584931032609000350664991912407174015823332805420037904232523841 / 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264`

This is approximately `2.0592384721174497e-20`, strictly positive. The next
smallest margins are twist `13` at `2.0702940243441798e-20` and twist `−2`
at `2.202274143260157e-20`. The largest is twist `−10` at approximately
`1.2961086925710612e-19`. I found no failed or anomalous row among these
extremes. The twist `+1` batch entry agrees exactly with the prior one-row
expint receipt in its direct endpoint, target endpoint, exact margin, and
log upper.

This is a receipt audit of the conditional finite external replay, not a
proof of H or of the row identities, global coefficient bounds, or analytic
contour assumptions. It confirms that the PASS label accurately describes
all stored row comparisons and consistency checks.

No numerical rerun was performed. Worker CPU and memory counters were
unavailable, not measured as zero.
