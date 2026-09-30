# Independent review: H6 mask 1586, twist −1 AFE row

## Finding

The direct-kernel checker is mathematically consistent for the selected
degree-two row. Its zero exit supports the stated one-row **conditional** upper
for `log |L_S(12001/12000)|`. It does not independently establish that the
selected row is the claimed Artin/Hecke L-function or prove its analytic
hypotheses.

The selected fixture values agree with the available source tables: conductor
15015, cutoff `N = 981`, the degree-two gamma data and root-number status, bad
Euler denominator polynomials, sector metadata, and complete signed
coefficient-vector hash. The independently reconstructed finite sums overlap
the pinned AFE finite-sum enclosures. The checker also reconstructs the
coefficient vector and checks its complete-vector SHA-256.

## Formula and interval audit

Arb documents `arb.expint(s)` as the generalized exponential integral
`E_s(x)`. In particular,

```text
E_(1-s)(x) = ∫₁∞ u^(s-1) exp(-xu) du
E_s(x)     = ∫₁∞ u^(-s)  exp(-xu) du.
```

These are the primary and dual kernels in the quadratic approximate functional
equation. With `t = 2π/√q`, the common factor `t^s / Γ(s)` is consistent with
the incomplete-gamma form of the two sums. The dual sum uses the conjugate
coefficients in the general formula; for this row the checker verifies that
all reconstructed coefficients are real.

For `s > 1`, put `δ = s − 1`. The pointwise bounds used by the checker follow
from `log u ≤ u − 1` and `u^(−s) ≤ 1` on `u ≥ 1`:

```text
E_(1-s)(x) ≤ exp(-x)/(x-δ),   when x > δ,
E_s(x)     ≤ exp(-x)/x.
```

The selected row uses `m = N + 1`. Under the stated coefficient bound
`|a_n| ≤ d₂(n) ≤ 2√n`, rewriting `n = m + k` and bounding the remaining
exponential sum geometrically gives the primary and dual tail expressions in
`quadratic_tail_bounds`. The checker verifies `t*m > δ` before using them.

For each removed prime, the script evaluates its denominator polynomial at
`p^(−s)` with Arb interval arithmetic and requires the resulting interval to
be strictly positive. The factors for this row (`1+z²`, `1±z`, and
`(1−z)²`) are positive at these arguments. Since
`L_S(s) = L(s) ∏_p D_p(p^(−s))`, multiplying the phase-free AFE upper by these
positive factors is in the correct direction.

Endpoint records are exact dyadic endpoints: the script takes
`x.upper().man_exp()` and reconstructs the stored mantissa times the power of
two. At 256-bit precision, the arithmetic operations, exponential-integral
weights, tails, polynomial evaluations, and logarithm are Arb enclosures. The
comparison is against the exact dyadic upper endpoint in the pinned AFE record.
In the reviewed replay, the computed `log L_S` upper was approximately
`0.04824325652403731253668746`, below the pinned upper
`0.04824325652403731259195653`.

## Conditions and limits

Interpreting the computed inequality as an upper for the actual selected
`L_S` requires the following inputs:

- the selected conductor, gamma factors, coefficient sequence, and bad Euler
  factors describe the intended row;
- that L-function satisfies the functional equation used by the degree-two
  AFE, with a root number of modulus one;
- the coefficient bound `|a_n| ≤ d₂(n)` holds for every `n`, including beyond
  the computed cutoff.

The finite arithmetic check verifies coefficients only through `N = 981` and
binds them to the compact fixture's complete-vector hash. It does not prove the
global coefficient bound or the row's Artin/Hecke identification, conductor,
functional equation, or root-number claim. Thus the result is one conditional
numerical upper, not an unconditional L-value bound.

## Source binding

When the full research tables are present, the checker verifies their pinned
hashes, compares the selected printed AFE fields to the AFE record, compares
the fixture row fields to the H6 moments row, and compares fixture sector
metadata to the H6 arithmetic sector. Compact-package mode instead relies on
the fixture SHA-256 and its embedded expected source hashes because the full
tables are absent.

The checker now explicitly asserts that fixture `row.conductor` and `row.N`
match the corresponding `printed_afe` fields, and that the fixture row's bad
Euler denominator polynomials and signed coefficient-vector hash match the
printed AFE selection fields. In full-table mode, the AFE record's conductor
and cutoff are also compared to those printed fields, while the moments row
checks every fixture row field. This resolves the previously noted
cross-row-consistency gap at source level; current pinned values are `15015`
and `981`.

The compact fixture still supplies the actual field values when the research
tables are absent. Its SHA-256 pins those fields, while the coefficient vector
is recomputed from the fixture and checked against its complete-vector hash.
Thus compact mode verifies the pinned fixture-based row and AFE allowance,
conditional on the provenance represented by that fixture.

## Replay provenance

I performed a short read-only replay with `PYTHONPATH` pointing to the
repository's temporary Python and python-flint installations. This replay was
**not run through the shared guarded helper** and is not a resource-compliant
receipt. It exited 0 in about 0.4 seconds and reported python-flint 0.9.0 /
FLINT 3.6.0. The main author's separate guarded full-source and compact-
package runs are the formal resource-compliant receipts. Their reported final
checks passed; this follow-up only inspects the new assertions and does not
rerun them.
