# H6 target-sigma expint replay: result

## Result

The independent generalized-expint replay **PASSES** the frozen H6 target-row
endpoint at `sigma = 12001/12000`. The row is mask 1586, twist `+1`, degree
two, multiplicity 1, conductor 240240, gamma `[0,1]`, root number `+1`, and
cutoff `N=3922`.

| Quantity | Outward upper / value |
|---|---:|
| Expint direct log upper | `0.13334973905073891147460919318615529122` |
| Frozen target row endpoint | `0.13334973905073891150817973756808417` |
| Target minus direct | `3.3570544381928877e-20` |

The exact target-minus-direct margin is

`2645493595506194724895404576742654389806769595866372365059405955570979615756270591455023231129957/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632`.

The direct endpoint's exact upper fraction, target endpoint fraction, and
binary Arb endpoint enclosures are in the JSON receipt.

All 3,922 coefficients were reconstructed; the complete signed-vector hash
matches `245989a787ca8bfa916c030bff304a9337365c62e5d7bd4ed1d7fad2aa1ff489`;
all 184 exact moment bins match. Both direct finite sums are contained in the
target centers expanded by its interpolation debit. The signed A+B lower
endpoint remains positive after the tails, and the recomputed bad-factor
multiplier overlaps the target interval.

The independently bounded primary and dual tail uppers are
`3.6194820888110328854789838580062328069e-22` and
`3.6194760910429483288553315518332925882e-22`, with combined upper
`7.2389581798539812143343154098395253951e-22`. The receipt stores the complete
outward Arb intervals.

This result uses the exponential-integral kernel route, independent of
`SplitKernels`, with the same Arb/FLINT interval backend. It does **not**
overwrite or change the earlier target-sigma `SplitKernels` strict row
**FAIL** (receipt SHA-256
`d35c52ea39918684b39c456c1e1fd6f3cdad3b61e177f0eeea06c5457e7eff58`), nor
the exact target mixed-quadratic aggregate substitution **PASS** (receipt
SHA-256 `35ec8d17c01f716663e9e7c7b64862413efd65cbae6807851b3d06536e360f27`).
These are method-specific row evidence and a separate aggregate check.

## Provenance and resources

- Checker: [`h6_target_sigma_expint.py`](h6_target_sigma_expint.py), SHA-256
  `1f600865d5cf895d2895c54b871a64763c11ae7d197722fb7e7b67eff8e1d6c0`.
- Receipt: [`h6_target_sigma_expint.json`](h6_target_sigma_expint.json),
  SHA-256 `56aa4b9fddbe580d852119f79329635c06630d2833315857b581fe1aa0bb4e2f`.
- The receipt verifies the target inherited-evaluation SHA-256
  `b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f` in
  both consolidated analytic source maps, and checks
  `all_analytic_factors_reevaluated = true`.
- Inputs, coefficient source, and preserved old receipts are pinned in both
  checker and receipt; see the [plan and formula](h6-target-sigma-expint-plan.md).
- Guarded run: timeout 900 s, shared lock and inherited memory/CPU policy;
  admitted with 15.1 GiB host memory and 1.81 GiB cgroup headroom; process
  completed in `0.3596545532345772` seconds and exited 0. Peak RSS was not
  reported.

## Conditional scope

The gamma normalization and signed `A+B` formula are conditional on the
source row being the intended primitive entire factor with conductor 240240,
gamma `[0,1]`, root number `+1`, and the stated conjugation-compatible
functional equation. The Mellin derivation also requires that the factor is
represented by its Dirichlet series in a right half-plane and has sufficient
vertical growth or contour decay to justify the contour shift. The infinite
tail requires the global bound `|a_n|<=d_2(n)`. The listed bad Euler
denominators must be the complete removed factors, and Arb/python-flint
outward special-function and ball arithmetic must be sound. The independent
formula review in
[`h6-expint-formula-independent-review.md`](h6-expint-formula-independent-review.md)
checks the normalization, sign, and tail inequalities while identifying the
series and contour-growth requirements.

This finite conditional check does not prove the row identity, the global
coefficient bound, or hypothesis `H`.
