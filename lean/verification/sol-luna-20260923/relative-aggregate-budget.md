# Actual relative aggregate budget interface

`ZetaSolRelativeAggregateBudget20260923.lean` reduces the completed-field
imprimitive analytic estimate to two direct bounds:

```text
genusLinearLogAtSigma ≤ 7.337578130846530221,
log ‖actualRelativeEulerValueAtCertificatePoint‖ ≤ -0.040875140862019542.
```

The relative value is the *actual* quotient of the completed imprimitive
zeta Euler product by the coherent 128-character genus product, with a
convergent prime product already proved in the earlier checked module
`ZetaLunaActualRelativeLogRun20260923.lean`. The new statement uses that
exact log split and the existing degree-16384 normalization. It does not
assert either numerical premise and does not identify the quotient with the
manuscript's four non-genus analytic row families. It is an alternate direct
target for future bounds; the selected conditional theorem and H are
unchanged. The arithmetic identity for the weighted non-genus allowance is
`2*mixedQuadratic + 4*mixedQuartic + 4*pureQuartic + 8*mixedOctic =
-40875140862019542/10^18`.

## Guarded Lean checks

The source SHA-256 is
`21aa3fbfd987f1d8571e877c5342bfbf3464f398c6b984f77fe3b686c0dbcdc3`;
the focused audit source SHA-256 is
`7878470506f8f28a878a171bf83426c4ab373acd17c104e89278d09c33b32e62`.
Both were checked with the pinned Lean toolchain through the master
`guarded_build.py` and shared `/tmp/lean-formalization-1000.build.lock`,
using `-j1 -M2560`, the inherited disk-backed temporary directory and a
900-second per-job timeout. The final source compile exited 0 and wrote its
`.olean`; the separate audit exited 0. Each of its three printed declarations
depends only on `propext`, `Classical.choice` and `Quot.sound`.

Two earlier admitted source compiles exited 1 on ordinary name-resolution
errors, first an unopened `normalizedRationalPrimeEulerContribution`, then an
unopened `selectedRationalPrimeSet` silently introduced as an implicit
variable. The final source opens both defining namespaces and sets
`autoImplicit false`; neither correction changed the intended fixed-set
statement. Guard admission for these attempts reported at least 14.3 GiB
host availability and 1.20 GiB cgroup headroom. Worker peak RSS and CPU
time were not measured and are unavailable. No selected Challenge/Solution
proof input was changed by this research theorem.
