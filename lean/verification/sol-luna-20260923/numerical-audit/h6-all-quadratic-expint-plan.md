# All H6 mask-1586 quadratic rows: expint batch replay

## Feasibility

The pinned H6 arithmetic source contains one degree-two sector, mask 1586,
with **32 rows**. The target `H6-low` receipt and mask-1586 moment file each
contain exactly the same 32 twists. Every row has gamma signature `[0,1]`,
root number `+1`, and multiplicity 1; no root-sign branch is mixed into this
batch. The cutoff distribution is 8 rows with `N=981`, 8 with `N=3922`, and
16 with `N=7843`. Their corresponding nonzero counts are 277, 562, and 1,004.
Across all rows this is 164,712 coefficient positions, 22,776 nonzero
coefficients, and **45,552** generalized-expint evaluations (primary and
dual per nonzero coefficient). The maximum row cutoff is only 7,843.

The checker [`h6_all_quadratic_expint.py`](h6_all_quadratic_expint.py)
processes one row at a time, reconstructs its complete vector using the pinned
quadratic recurrence, verifies its full coefficient hash and exact moments,
then uses the same independent generalized-expint kernel and elementary
`d₂` tails established in the single-row replay. It checks every target
endpoint and A/B center consistency, and emits one row-level diagnostic per
twist before returning an overall status. It does not import or call
`SplitKernels`.

The guarded run completed serially in `6.480669` seconds, substantially below
the source-based ~15-second estimate. It was admitted with 15.9 GiB host
memory and 1.00 GiB cgroup headroom. Peak RSS was not reported. The checker
processed each row in turn; no full-table coefficient vectors were retained.

## Conditional analytic assumptions

Every row check assumes that its pinned conductor 15015, 240240, or 960960,
gamma `[0,1]`, and root number `+1` identify the intended primitive entire
degree-two factor with its stipulated conjugation-compatible functional
equation. The Mellin derivation needs the Dirichlet-series identity in a right
half-plane and sufficient vertical growth or contour decay to justify the
contour shift; the source-only review
[`h6-expint-formula-independent-review.md`](h6-expint-formula-independent-review.md)
states this qualification. Tail bounds require the global
`|a_n| <= d_2(n)` coefficient bound. The listed bad Euler denominator
polynomials must be complete for each removed factor. Arb/python-flint's
generalized expint and outward ball operations are also trusted assumptions.
The source files and the previous method-specific **PASS**, pointwise
`SplitKernels` **FAIL**, and exact aggregate **PASS** are hash-pinned. Finite
checks do not prove the global assumptions or H.

## Provenance

| Input | SHA-256 |
|---|---|
| H6 low-degree arithmetic | `b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771` |
| Mask-1586 moments | `a7e65537a05389f11115a8cf64c186ead6b1dc4973a8c5f862f31a34fdeb40f1` |
| Target H7 inherited Euler receipt | `b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f` |
| Consolidated analytic replay | `34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e` |
| Coefficient recurrence source | `3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329` |
| Single-row expint checker | `1f600865d5cf895d2895c54b871a64763c11ae7d197722fb7e7b67eff8e1d6c0` |
| Single-row expint receipt | `56aa4b9fddbe580d852119f79329635c06630d2833315857b581fe1aa0bb4e2f` |
| Preserved SplitKernels strict-row FAIL | `d35c52ea39918684b39c456c1e1fd6f3cdad3b61e177f0eeea06c5457e7eff58` |
| Preserved target aggregate PASS | `35ec8d17c01f716663e9e7c7b64862413efd65cbae6807851b3d06536e360f27` |

Batch checker SHA-256: `060af68df4b7e1eb6dfba87e88ca13fa26cbccca16966c2c256b4fc8cd2116c3`.
It passed `py_compile` and a read-only check of all pinned source hashes before
the guarded evaluation. The machine-readable result is
[`h6_all_quadratic_expint.json`](h6_all_quadratic_expint.json), SHA-256
`54e9fe4921c92366da8644e27bd8d2217a04b678046dfa3c31701519b4c917ce`.

The batch **PASSES all 32 strict target-row comparisons**, with no consistency
failures. Exact rational margins in the receipt range from

- minimum: twist `+55`, conductor 15015, `N=981`,
  `3245525081529026119997427115675961584931032609000350664991912407174015823332805420037904232523841/157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264`
  (about `2.0592384721174497e-20`);
- maximum: twist `-10`, conductor 960960, `N=7843`,
  `5106928273588569993060839659722063949105786213850732858326747907328104207226910522104709168641167/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816`
  (about `1.2961086925710612e-19`).

The receipt records all 32 exact margins and endpoints. It independently
checks 164,712 coefficients, 22,776 nonzero terms, and 45,552 primary/dual
expint calls, with root-number values `[1]`. The consolidated analytic source
maps bind the target inherited-Euler receipt in both locations and the global
`all_analytic_factors_reevaluated` flag is true.

The earlier single-row target `SplitKernels` comparison remains **FAIL**;
this full batch is a different analytic kernel method and every row passes by
that expint method. The single-row expint **PASS** and exact aggregate
substitution **PASS** remain separate and are hash-pinned. The batch does not
recompute the 836-factor total or prove `H`.

The executed command was:

```sh
python3 automation/lean-formalization/guarded_build.py --timeout-seconds 900 -- \
  env PYTHONPATH=/tmp/unit-distance-flint python3 \
  lean-formalization/verification/sol-luna-20260923/numerical-audit/h6_all_quadratic_expint.py
```
