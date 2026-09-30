# Source review: direct pure-quartic AFE checker

Reviewed `numerics_afe_pure_quartic_direct.py` and its pinned AFE, kernel,
arithmetic, coefficient-checker, fixture, moment, and AFE-table inputs. This is
a source-level review only; no numerical rerun was performed.

## AFE formula and tail

For the selected row the pinned AFE table says `gamma=[1,1,1,1]` and root
number `+1`. The checker sets `parity=1`, `t=π²/√Q`,
`b=(s+1)/2`, `dual=(2-s)/2`, and `F=t^(s+1)/Γ(b)^4`. Its weights are `a_n n`
and its two finite sums use `K_b(t²n²)` and `K_dual(t²n²)`. These agree with
the formula in the pinned `h7-pure-quartic-afe.py`; since the generated row
coefficients are checked real, omitting conjugation in the dual sum is valid.
The table's root number is checked to be `+1`, so combining as `A+B` has the
right phase.

For each `β`, the Rankin majorant `Σ |a_n| n^-β ≤ ζ(β)^4` follows from the
degree-four divisor bound, conditional on the stated finite-image local-root
assumption. With `C=(β+1)/2`, `β≥s` gives `C≥b,dual`. Positivity of `k₄`,
monotonicity of the integral kernel in its exponent and argument, and the
change of variables in `K_C` give

```text
F Σ_{n>N} |a_n| n K_a(t²n²)
 ≤ F (N+1)^(β+1) K_C(t²(N+1)²) ζ(β)^4,
```

for either side. The script uses this expression and takes the minimum of
valid candidates. At bad primes it evaluates the pinned denominator
polynomial `D_p(p^-s)` and adds `log D_p`, which is the correct sign for
restoring the removed factors `L^{S'}=L·∏_{p∈S'}D_p(p^-s)`. It checks each
denominator is real and positive and checks the resulting sum overlaps the
pinned `BAD7_log_removal` interval.

## Coefficients and metadata

The local coefficient rules match the pinned `five_space_data.py` recurrence:
the residue vector records `(-1/p)`, `(2/p)`, and the six odd-prime symbols
through 17; the form's polar vector and quadratic-refinement parity determine
the local trace code; the central sign is used when the polar vector is zero;
the twist multiplies the `±1` code; bad-prime denominators are read from the
arithmetic row; good-prime denominators are inverted to obtain prime-power
coefficients; and the resulting multiplicative sequence uses the least-prime
factor recurrence. The script checks all first 128 coefficients against the
pinned row and source arithmetic. This review found no local-rule discrepancy
in the code path for larger coefficients. The source-bounded identity remains
conditional on the pinned arithmetic row and its representation data.

The source hashes for the AFE helper, kernel, arithmetic source, AFE table,
coefficient checker, and fixture are pinned in the script. It uses the
arithmetic source row for bad-prime polynomials, because the AFE table omits
those polynomials, and cross-checks the restored log against the table's
`BAD7_log_removal` field. It also checks the conductor, gamma signature,
root number, and cutoff against the pinned AFE row.

## Checker defect found and corrected during the run

The initial script required the direct pointwise sums `A` and `B` to overlap
the raw `A_finite` and `B_finite` intervals from the moment-based AFE table.
That is too strong. In the pinned `h7-pure-euler.py`, `A_finite` and
`B_finite` are bin-moment approximations, while their pointwise discrepancies
are recorded separately in `one_side_interpolation_error`. The final stored
upper bound explicitly adds twice the interpolation error. Therefore a direct
pointwise value need only overlap the corresponding stored interval enlarged
by the interpolation-error upper endpoint. The reported first-run `A_finite`
overlap failure is consistent with this missing enlargement and is not by
itself evidence of a bad coefficient rule or an incorrect stored row. The
stored one-side interpolation allowance is about `2.96e-25`, however, so the
enlargement is very small: if the difference exceeds that amount, compare the
exact coefficient streams just past index 128 before revisiting the AFE
formula or the stored row.

Post-run status clarification (2026-09-23): the source with the hash below
already uses `contained_in_source_center_plus_error` for both sums. The
passing corrected run is recorded in
[the numerical report](numerics_afe_pure_quartic_direct.md). The defect
described above applies to the earlier attempts, not to that final source.

This source review does not certify the numerical output or the
representation-to-row identity. Checker SHA-256:
`8b51cd4e9584b7e48c715cf3cb279ee30da2ad16f955ee60d10fa40dd269ef34`.
