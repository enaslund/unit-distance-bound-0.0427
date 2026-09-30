# H6 quadratic target-sigma batch: result

## Scope and outcome

The direct Arb expint checker replayed all **32** degree-two rows in H6 mask
1586 at `sigma = 12001/12000`. Every row has gamma `[0,1]`, root number
`+1`, and multiplicity 1. The batch **PASSES all 32 strict comparisons** with
the target frozen row endpoints; the receipt lists no row-comparison or
consistency failures.

| Batch measure | Result |
|---|---:|
| Reconstructed coefficient positions | 164,712 |
| Nonzero coefficients | 22,776 |
| Generalized expint evaluations | 45,552 |
| Maximum row cutoff | 7,843 |
| Minimum exact endpoint margin | `2.0592384721174497e-20` |
| Maximum exact endpoint margin | `1.2961086925710612e-19` |

The minimum margin is for twist `+55`, conductor 15015, `N=981`; its exact
fraction is

`3245525081529026119997427115675961584931032609000350664991912407174015823332805420037904232523841/157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264`.

The maximum margin is for twist `-10`, conductor 960960, `N=7843`; its exact
fraction is

`5106928273588569993060839659722063949105786213850732858326747907328104207226910522104709168641167/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816`.

These are exact rational differences of the target row upper endpoint and
the direct outward log upper. The receipt contains all row endpoints,
margins, coefficient hashes, finite-sum consistency checks, and tails.

## Method and provenance

The checker reconstructs each coefficient vector with the pinned recurrence,
checks its full signed-vector hash and every exact moment bin, then evaluates
primary and dual weights with the generalized exponential integral. It uses
the same Arb/FLINT backend as previous checks but does not import `SplitKernels`.
The row gamma normalization, plus sign, root number, and elementary tail
derivation are described in
[`h6-target-sigma-expint-plan.md`](h6-target-sigma-expint-plan.md).

- Checker SHA-256:
  `060af68df4b7e1eb6dfba87e88ca13fa26cbccca16966c2c256b4fc8cd2116c3`.
- Batch receipt SHA-256:
  `54e9fe4921c92366da8644e27bd8d2217a04b678046dfa3c31701519b4c917ce`.
- Target receipt SHA-256:
  `b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f`.
- Consolidated analytic replay SHA-256:
  `34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e`.
- All other source hashes are pinned in the checker and repeated in the batch
  receipt. Independent local rehashing confirmed the checker, receipt, and
  all pinned inputs match.

The guarded run used the shared slot with inherited resource limits, timeout
900 seconds, admission at 15.9 GiB host memory and 1.00 GiB cgroup headroom,
and completed in `6.480669` seconds with exit 0. Peak RSS was unavailable.

## Conditional scope and prior results

The AFE checks assume each source row is the intended primitive entire
degree-two factor with its pinned conductor, gamma signature `[0,1]`, and
root number `+1`; the stated conjugation-compatible functional equation and
the Dirichlet-series identity must hold. The Mellin derivation needs sufficient
vertical growth or contour decay to justify shifting its contour. The
infinite tails assume the global `|a_n| <= d_2(n)` bound; the listed bad Euler
denominators must be complete. The outward special-function and interval
operations in Arb/python-flint are also assumed sound. These conditions are
not proved by finite coefficient hashes or moment identities.

The earlier target-sigma pointwise `SplitKernels` strict row comparison for
mask 1586 twist `+1` remains **FAIL** and its receipt is unchanged. The single
row expint comparison is a method-specific **PASS**, and the exact target
aggregate substitution is a separate **PASS**; the batch pins both receipts.
This 32-row endpoint check does not recompute the complete 836-factor
allowance and does not prove `H`.
