# H6 target-sigma exponential-integral replay

## Feasibility and scope

The staged checker [`h6_target_sigma_expint.py`](h6_target_sigma_expint.py)
evaluates H6 mask 1586, twist `+1`, degree two at `sigma = 12001/12000`
using Arb's generalized exponential integral. It does not import
`nonpositive-afe.py`, `SplitKernels`, or the stored moment-bin evaluator. It
reconstructs all 3,922 coefficients from the pinned exact recurrence,
verifies the full signed-vector hash and each exact moment bin, then sums the
AFE weights term by term.

This is a distinct analytic-kernel derivation, not a new interval backend: it
uses the same `python-flint`/Arb implementation as earlier checks. The checker
pins the existing target-sigma receipts and verifies that the target row
receipt hash occurs in both the consolidated analytic receipt's table-source
map and replay-input map, with `all_analytic_factors_reevaluated = true`. It
also checks that the prior strict `SplitKernels` row **FAIL** and exact target
aggregate replacement **PASS** remain unchanged.

## Gamma normalization and AFE weights

For the supplied signature `gamma = [0,1]`, the completion uses
`Gamma_R(s) Gamma_R(s+1)`, where `Gamma_R(s) = pi^(-s/2) Gamma(s/2)`. The
duplication formula gives

`Gamma_R(s) Gamma_R(s+1) = 2 (2 pi)^(-s) Gamma(s)`.

For conductor `Q = 240240`, put `t = 2 pi / sqrt(Q)`. The AFE has common
prefactor `t^s / Gamma(s)`. With

`E_v(x) = integral_1^infinity exp(-x u) u^(-v) du`,

the finite primary and dual sums are

`A = (t^s/Gamma(s)) sum_{n<=N} a_n E_(1-s)(tn)` and
`B = (t^s/Gamma(s)) sum_{n<=N} conjugate(a_n) E_s(tn)`.

The reconstructed row is real coefficient by coefficient. Conditional on the
stipulated root number `+1`, the signed AFE is `A+B`; the checker uses its
positive lower endpoint to form an absolute-value upper. The row identity,
primitive entire completion, functional equation, conductor, gamma signature,
and root number are assumptions bound to the pinned source row, not
consequences of finite coefficient checks. The formula also requires
`L(w)=sum_n a_n n^(-w)` in a right half-plane and enough vertical growth or
contour decay to justify the Mellin-contour shift; entireness and the
functional equation alone do not supply that step. The source-only formula
review in
[`h6-expint-formula-independent-review.md`](h6-expint-formula-independent-review.md)
confirms the prefactor, sign, and tail inequalities under these additional
conditions, and identifies the contour-growth requirement.

## Tail bound

Assume the global degree-two coefficient bound `|a_n| <= d_2(n) <= 2 sqrt(n)`.
Set `delta = s-1`, `m=N+1=3923`, and `x0=t m`. Here `s>1`, and the checker
requires `x0 > delta`. For `x >= x0`, using `log u <= u-1`,

`E_(1-s)(x) = integral_1^infinity u^delta exp(-xu) du <= exp(-x)/(x-delta)`,

while `u^(-s) <= 1` gives

`E_s(x) = integral_1^infinity u^(-s) exp(-xu) du <= exp(-x)/x`.

With `sum_{n>=m} exp(-tn) = exp(-tm)/(1-exp(-t))`, `sqrt(n)>=sqrt(m)`, and
`(tn-delta)^(-1) <= (tn)^(-1)/(1-delta/x0)`, the checker computes outward
Arb bounds

`T_A = (t^s/Gamma(s)) * 2 exp(-tm)/(1-exp(-t)) /
       (t sqrt(m) (1-delta/x0))`,

`T_B = (t^s/Gamma(s)) * 2 exp(-tm)/(1-exp(-t)) / (t sqrt(m))`.

Thus the signed full value lies in `A+B +/- (T_A+T_B)`. This route does not
use the frozen interpolation debit or Rankin tail. The guarded run measured
primary, dual, and combined tail upper endpoints of
`3.6194820888110328854789838580062328069e-22`,
`3.6194760910429483288553315518332925882e-22`, and
`7.2389581798539812143343154098395253951e-22`, respectively. The combined
elementary tail is below the target's approximately `2.4e-20` one-side
Rankin tail. Exact outward intervals are serialized in the result JSON.

## Inputs and provenance

| Input | SHA-256 |
|---|---|
| H6 arithmetic source | `b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771` |
| Mask-1586 H6 moments | `a7e65537a05389f11115a8cf64c186ead6b1dc4973a8c5f862f31a34fdeb40f1` |
| Target inherited AFE receipt | `b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f` |
| Consolidated analytic replay | `34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e` |
| Independent coefficient recurrence | `3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329` |
| Prior target strict-row receipt (must remain FAIL) | `d35c52ea39918684b39c456c1e1fd6f3cdad3b61e177f0eeea06c5457e7eff58` |
| Prior target aggregate receipt (must remain PASS) | `35ec8d17c01f716663e9e7c7b64862413efd65cbae6807851b3d06536e360f27` |

Checker SHA-256: `1f600865d5cf895d2895c54b871a64763c11ae7d197722fb7e7b67eff8e1d6c0`.
The consolidated receipt keys this source relative to `publication/`; the
checker follows that convention and the actual key exists in both maps. It
passed `py_compile` and input-hash/source-binding checks before the numeric
run. The result receipt is
[`h6_target_sigma_expint.json`](h6_target_sigma_expint.json), SHA-256
`56aa4b9fddbe580d852119f79329635c06630d2833315857b581fe1aa0bb4e2f`.
The concise result handoff is in
[`h6-target-sigma-expint-report.md`](h6-target-sigma-expint-report.md).

## Run plan and risks

The guarded run evaluated 1,124 nonzero-term generalized-expint weights plus
the exact coefficient/bin replay in `0.3596545532345772` seconds. It was
admitted with 15.1 GiB host memory available and 1.81 GiB cgroup headroom and
exited 0. Peak RSS was unavailable, so no memory measurement is claimed. The
command was:

```sh
python3 automation/lean-formalization/guarded_build.py --timeout-seconds 900 -- \
  env PYTHONPATH=/tmp/unit-distance-flint python3 \
  lean-formalization/verification/sol-luna-20260923/numerical-audit/h6_target_sigma_expint.py
```

The method-specific target-row result is **PASS**. All 3,922 coefficients
were reconstructed, the signed-vector digest matched, all 184 moment bins
matched, both direct finite sums passed their target-center consistency
checks, the signed sum remained positive after the tail, and the bad-factor
interval overlapped the target interval. The direct expint log upper is
`0.13334973905073891147460919318615529122`; the target endpoint is
`0.13334973905073891150817973756808417`. The exact target-minus-direct margin
is
`2645493595506194724895404576742654389806769595866372365059405955570979615756270591455023231129957/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632`
(`3.3570544381928877e-20`).

This expint row comparison passes independently of the earlier pointwise
`SplitKernels` comparison, which remains a strict **FAIL** by approximately
`4.4458065915680757e-26`. Its receipt and label are preserved. The existing
exact target aggregate substitution remains a separate **PASS**.

Potential failure modes include library support or interval width for the
generalized `expint` at Arb-ball order/argument, a mismatch in the AFE
normalization, missing justification for the Dirichlet-series identity or
contour shift in the intended factor, and a direct endpoint that still exceeds
the target allowance.
The script writes JSON before its final failure exit, preserving diagnostics.
Even a method-specific row **PASS** remains conditional on the global
coefficient/tail bound and analytic factor data; it neither proves `H` nor
erases the distinct `SplitKernels` endpoint **FAIL**.
