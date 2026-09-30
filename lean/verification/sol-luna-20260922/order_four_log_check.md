# Independent order-four logarithmic allowance

`order_four_log_check.py` checks the manuscript's displayed finite allowance

```text
S4 = (1/4) Σ_{p∈P4} log((1+p^(-2σ))/(1-p^(-2σ)))
   > 0.00003724741189544274807446,   σ = 12001/12000.
```

It reads the 45-prime list in the sealed `euler.json`. The separate
`field_bridge_audit.py` independently reconstructed that exact list from the
Challenge's radicands, catalog rows and the manuscript's completed/retained
quadratic forms, through `10^4`. Thus this check tests the analytic value of
the reconstructed list rather than trusting the manuscript's recorded sum.

The calculation uses only integer and rational operations. For every prime,
it writes `p = 2^k m`, with `1 ≤ m < 2`, and bounds `log m` and `log 2` from
above by 35 terms of the `atanh` series plus an explicit positive geometric
tail. With the resulting rational `t ≥ log(p)/6000` and `0 < t < 1`, the odd
degree-nine alternating Taylor polynomial gives a lower bound for
`exp(-t)`. It rounds `p^(-2) exp(-t)` down, then applies
`atanh(x) ≥ x + x^3/3 + x^5/5` and rounds each term down again. All rounding
grids and the SHA-256 of the supplied prime data are in the JSON receipt.

The resulting exact lower bound is

```text
S4 ≥ 0.0000372474118954427480744667051484
   > 0.00003724741189544274807446
```

with strict rational gap `6.7051484 × 10^-27` above the printed allowance.
The checker exited zero. Its result is conditional on the supplied prime list;
the independent field-form reconstruction covers that list but does not prove
the Kummer interpretation of every form or the global fixed-field zeta
inequality. This finite check leaves the other analytic groups and infinite
tail untouched.
