# Quartic-field reconstruction of unramified composite coefficients

`quartic_field_composites_check.py` extends the finite field check in
`quartic_field_trace_check.py`. It uses the selected mixed quadratic row
(`mask=1586`, twist `-1`, cutoff 981) and the derived polynomials

```text
F: X² + 35,    K: X⁴ + 34X² + 429.
```

If `u = -(17 + 2√-35)` in `F`, then `Norm(u)=429`. Since 429 is not a
rational square and `u` generates `F`, `u` is not a square in `F`; adjoining
its square root gives a degree-four field with the displayed quartic
minimal polynomial. At every prime outside `2,3,5,7,11,13`, the quartic
discriminant is nonzero. The difference between quartic and quadratic root
counts modulo `p` gives the trace of the corresponding degree-two Artin
permutation-character difference. Root counts over `F_(p²)` give its squared
Frobenius trace, and Newton's formula gives

```text
a_(p²) = (trace(Frob_p)² + trace(Frob_p²))/2.
```

Every integer `n≤981` supported on those good primes has prime exponents at
most two. Multiplicativity therefore reconstructs all such coefficients from
the prime and prime-square values. The checker compares each reconstructed
coefficient with the pinned complete 981-entry row. It excludes all `n`
divisible by one of the six ramified primes; prime 17 is unramified here,
although the manuscript handles its selected Euler factor separately.

The finite check depends on the mathematical identification of the quartic
minus quadratic permutation character with the manuscript's selected
two-dimensional analytic row. It does not prove that representation identity,
the global Artin product, an AFE bound, or the fixed-field zeta hypothesis.
The [independent source review](quartic-composites-review.md) assesses the
finite factorization and trace formulas separately.

## Guarded result

The checker was run through the master `guarded_build.py` with a 900-second
timeout; admission reported 17.6 GiB available, and the process exited 0 in
under one second. Its durable
[JSON receipt](quartic_field_composites_check.json) records 186 matching
unramified-support coefficients through 981: 159 prime cases, all five
eligible prime squares, 21 other composites and `n=1`. The remaining 795
integers are divisible by one of the six excluded ramified primes. The
complete pinned coefficient-vector hash was
`baec4879c9e60ab3f2e657ff9f4d9cac64a39eebc3aa123495844f19e3ef654c`;
both full research source tables were present and hash-matched. The checker
source SHA-256 was
`d560bb554f46b082bcec1ad3328f243e97b7c3dcf8a2ec4001b6c0dff71f1fa4`.
This finite comparison still has the mathematical identification limits
described above.
