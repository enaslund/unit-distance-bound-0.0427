# Plus-field bridge for H6 mask 1586

## Artifact and status

The staged source is
[`HeckeManuscriptMixedQuadratic1586PlusFieldBridge20260923.lean`](../../../UnitDistance/HeckeManuscriptMixedQuadratic1586PlusFieldBridge20260923.lean).
It remains **uncompiled**. One guarded compile was admitted, then Lean exited
134 after about 50 seconds with
`lean::memory_exception: excessive memory consumption detected at 'interpreter'`.
The exact command was `lake env lean -j1 -M2560 -o
.lake/build/lib/lean/UnitDistance/HeckeManuscriptMixedQuadratic1586PlusFieldBridge20260923.olean
UnitDistance/HeckeManuscriptMixedQuadratic1586PlusFieldBridge20260923.lean`.
Admission was 14.9 GiB host available and 1.86 GiB cgroup headroom, with the
900-second timeout. The combined run log is
[`plus-field-bridge-lean-run-20260923.log`](plus-field-bridge-lean-run-20260923.log),
SHA-256 `cccadd2045c57af3cb912a7df4cfc3bd23c9bc7fee8296826baa936fd657ebd7`.
No `.olean` was produced, and the `#print axioms` requests are not audit
results. No retry was run. The source contains no `sorry`, `admit`, or
declared axioms.
Current SHA-256: `0c20b83bbe4ed3f8f948b31664d350f2c952216a826cfd66a04c21c440555605`.

## Declarations staged

The imported arithmetic source already proves `norm_eta : Algebra.norm ℚ eta
= 429` and `rational_429_not_isSquare`. `eta_nonsquare` applies the field norm
to a hypothetical `eta = x^2`, then derives a rational square root of 429.
The resulting `Fact (Nonsquare eta)` permits `PlusFactorField := Extension eta`,
and `plusFactorField_relative_degree` is the direct `relative_finrank eta`
specialization. The named nonsquare `Fact` instance is public for downstream
use. The file also proves `plusFactorField_absolute_degree = 4` by the tower
formula and the existing degree of `BaseField`.

`plusFactor_local_euler` specializes the existing
`UnitDistance.NumberFieldAnalysis.quadratic_primeFiber_factor_product` to
`BaseField` and `PlusFactorField`. Its scope is each height-one prime of
`𝓞 BaseField`, and it includes the relative ramified case. It is not yet an
Euler-factor theorem over rational primes and does not match any H6 row data.

## Limits

This endpoint establishes only a quadratic extension and its relative local
prime-fiber factor identity, once compiled. It does not prove the row's
rational-prime Euler table, the all-prime induced two-dimensional local
eigenvalue formula, equality of its coefficient sequence with the quotient,
or the global `|a_n| ≤ d₂(n)` majorant. In particular, the H6 table entry at
17 remains part of the local matching obligation although 17 does not divide
the listed conductor.

The two-eigenvalue local estimate is separately compiled in
[`TwoEigenEulerCoefficientBound20260923.lean`](TwoEigenEulerCoefficientBound20260923.lean).
For a local inertia-invariant eigenspace of dimension zero or one, its
eigenvalue list must be padded with zero eigenvalues to length two before
applying that estimate. The remaining representation-to-row and
prime-power-to-global coefficient steps are not discharged by this field
bridge.
