# Source audit: H6 target-sigma expint replay

## Scope

Read-only review of `h6_target_sigma_expint.py`, its seven pinned inputs, and
the current `h6_target_sigma_expint.json` receipt. No replay or Arb computation
was run. I checked actual input hashes, source/receipt hash agreement, JSON
field use, exact interval endpoint directions, and the tail inequalities.

## Findings

I found no source-level interval-direction, normalization, or tail bug that
would invalidate the recorded PASS, subject to the conditional analytic
hypotheses listed in the receipt.

- The `Gamma_R(s) Gamma_R(s+1)` identity gives
  `2 (2π)^(-s) Γ(s)`. With `t=2π/√Q`, this is the stated
  `Λ(s)=2 t^(-s) Γ(s)L(s)` normalization. The pinned H6 arithmetic row has
  `gamma=[0,1]`, conductor `240240`, and root number `+1`; the script checks
  these values, target sigma `12001/12000`, and target row identity at lines
  195–209. Its direct sums use `E_(1-s)` and `E_s`, multiply each by
  `t^s/Γ(s)`, and add them (121–138), matching the plus-sign formula reviewed
  separately.
- Tail directions are valid for `s>1` and `x> s−1`: from
  `u^(s−1) ≤ exp((s−1)(u−1))`, it gets
  `E_(1-s)(x) ≤ e^(−x)/(x−(s−1))`; from `u^(−s)≤1`, it gets
  `E_s(x)≤e^(−x)/x` (141–164). For `m=N+1`, it checks `tm>s−1`.
  Multiplying `|a_n|≤2√n` by either kernel bound, using `n≥m` in the
  denominator and square root, and summing `e^(−tn)` gives the two tail
  formulas in `primary` and `dual`. The outer Arb operations are outward ball
  operations; their endpoints are used as upper bounds.
- The finite A/B intervals are checked inside the pinned target center plus
  the upper interpolation debit (80–89, 229–234). The target debit interval
  is positive in the pinned JSON. `abs(signed).upper()+error.upper()` bounds
  the signed finite sum plus its absolute tail (235–238). Each removed local
  denominator is evaluated as an Arb complex polynomial; zero is excluded,
  and the product of local absolute values is a positive multiplier (240–250).
  Multiplying the modulus upper by that multiplier, taking `.upper()`, and
  then the logarithm preserves the upper direction (251–255). The comparison
  is direct-upper `≤` frozen target upper, encoded as nonnegative exact
  `Fraction` margin (253–256). The frozen `bad_multiplier_modulus` is only an
  overlap consistency check; the final upper uses the independently computed
  Arb multiplier.
- All seven input files match the script's SHA pins. The actual checker hash
  is `1f600865d5cf895d2895c54b871a64763c11ae7d197722fb7e7b67eff8e1d6c0`,
  matching the receipt. The receipt reports 384-bit Arb, all A/B and bad
  multiplier checks true, and PASS. Its direct log upper is
  `0.13334973905073891147460919318615529122`; the frozen target upper is
  `0.13334973905073891150817973756808417`. The stored exact margin is
  positive, about `3.3570544381928877e-20`.

The checker fails closed under `python -O` because `main` rejects
`not __debug__` before doing work (167–169). The script records input hashes,
target consolidated-replay binding, prior receipt hashes, and its own source
hash in the output. The result is a finite external numerical replay for one
H6 mask-1586, twist-`+1` row, not a proof of the global condition H or of the
analytic assumptions. In particular, its own receipt lists as conditional:
the row's primitive entire degree-two identity and FE, the Dirichlet-series
identity, sufficient strip growth for the Mellin shift, completeness of the
removed bad Euler factors, the global coefficient bound, and rigorous Arb
backend semantics. The finite coefficient/hash/bin checks do not prove those
global statements. The direct kernel is independent of the SplitKernels
evaluator but shares the Arb/FLINT interval backend.

No costly job was run; worker CPU and memory counters were unavailable, not
measured as zero.
