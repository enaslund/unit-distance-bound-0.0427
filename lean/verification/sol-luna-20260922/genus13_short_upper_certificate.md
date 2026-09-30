# Short exact upper bound for the conductor-13 deleted value

## Result and scope

The short checker
`genus13_short_upper_certificate.py` proves an exact rational upper bound
below 1 for the selected-prime-deleted conductor-13 value at
`s = 12001/12000`. It uses only 52 finite terms, a coarse rational estimate
for those terms, and the period-tail bound. It does not reuse the 13,000-term
logarithm/exponential interval computation. Its source and run receipt is
`genus13_short_upper_certificate.json`.

The checker is independent numerical evidence, not a Lean interval proof. The
identification of the period with the actual primitive character is bound to
the two listed Lean source hashes and their text anchors when those files are
present. The common-level interpretation uses the established local deletion
formula. No conductor-13 manuscript row allowance is pinned by the materials
used here, so no per-row allowance comparison is claimed. This does not bound
the completed AFE factor, the completion integral, or the genus aggregate.

## Finite sum and tail

The character period is
`(1,-1,1,1,-1,-1,-1,-1,1,1,-1,1,0)`. Its sum is zero and its cyclic partial
sums have absolute value at most 2. Euler's criterion independently checks
the listed values modulo 13. Use `N=52=4·13`, so the finite sum contains four
complete periods and the shifted tail has the same partial-sum bound.

Write `n^(-s) = n^(-1) exp(-log(n)/12000)`. For a `+1` coefficient,
`n^(-s) ≤ 1/n`. For a `-1` coefficient, use `exp(-x) ≥ 1-x` for `x≥0`
and `log(n) ≤ n-1` to get

```text
n^(-s) ≥ (1/n)(1 - log(n)/12000)
       ≥ (1/n)(1 - (n-1)/12000).
```

Negating reverses the inequality. Summing these signed rational bounds for
`1≤n≤52` gives

```text
Σ_{n≤52} χ₁₃(n)n^(-s)
  ≤ 70334919167156019061867/105950239461401596800000.
```

Summation by parts with shifted character partial sums bounded by 2 gives
`|Σ_{n>52} χ₁₃(n)n^(-s)| ≤ 2·53^(-s) < 2/53`, since `s>1`. Therefore

```text
L(χ₁₃,s) <
  3939651194782072203878951/5615362691454284630400000.
```

## Selected-prime correction

The selected primes and character values are
`(2,3,5,7,11,13,17)` and `(-1,1,-1,-1,-1,0,1)`. The deletion factor is
`C=∏(1-χ₁₃(p)p^(-s))`. For `χ(p)=-1`, `p^(-s)<1/p`, so the factor is less
than `1+1/p`. For `χ(p)=1`, use
`p^(-s) ≥ (1/p)(1-(p-1)/12000)`, again from `log(p)≤p-1` and
`exp(-x)≥1-x`, to upper-bound `1-p^(-s)`. At `p=13`, the factor is 1.
Multiplying these positive rational bounds gives

```text
C < 13093091/9296875.
```

The multiplication is valid without importing positivity of the primitive
value from the longer interval check. The actual correction factor is strictly
positive: each `χ=1` factor is `1-p^(-s)>0`, each `χ=-1` factor is positive,
and the `χ=0` factor is 1. If the primitive value is nonpositive, then the
deleted value is nonpositive and is already below the positive rational upper
bound displayed next. If the primitive value is positive, multiplication by
the positive correction preserves the primitive upper inequality, and the
correction upper inequality then gives the same product bound.

Combining the primitive and correction upper bounds yields

```text
L_deleted <
  4689291963776399684905241675231/4745938638374004765750000000000
  = 1 - 56646674597605080844758324769/4745938638374004765750000000000
  < 1.
```

The margin is exact and positive. This is a deliberately coarse short
certificate: its role is only to establish the strict `<1` comparison.

## Run record

The guarded command in the JSON receipt exited 0, admitted with 17.3 GiB
available, and completed in about 0.9 seconds. The checker SHA-256 is
`4d2580b537d1039c07dde85ca12a31674ef49bd33267b59e60061b10f92272d2`.
