# Actual coherent conductor-13 norm bound

## Checked statements

Source: [`ZetaLunaConductorThirteenFinalNormRun20260923.lean`](../../UnitDistance/ZetaLunaConductorThirteenFinalNormRun20260923.lean)

SHA-256: `5ee168c335fe8318ba1c79909e116fb60e470c016df01eaca3ec97a2e33c48ff`.

At the certificate point `certificatePoint = ((12001 / 12000 : ℝ) : ℂ)`,
the checked norm endpoint is:

```lean
theorem conductorThirteen_coherentEulerValue_norm_le_shortCertificateUpper :
    ‖coherentGenusEulerValue conductorThirteenIndex certificatePoint‖ ≤
      shortCertificateUpper
```

Here `shortCertificateUpper` is the exact rational endpoint already defined
in `ZetaLunaConductorThirteenShortBoundRun20260923`. This theorem has no
additional numerical hypothesis. The proof combines the strict upper on the
primitive short `LSeries` real part, the positive-real primitive-value
theorem, and the checked positive finite deletion correction. The actual
coherent value factors as the primitive `LSeries` times that correction. The
positive-real representation of the coherent value turns its norm into its
real part, and positivity of both factors allows multiplication of the two
upper bounds. The exact rational assembly is
`shortBudget_eq_certificateUpper`.

The module also derives the factor-level log consequence:

```lean
theorem genusLinearLogAtSigma_lt_otherRemainder_of_actualShortCertificate :
    FixedZetaGenusLinearFactors.genusLinearLogAtSigma <
      otherCoherentLogRemainder
```

This follows from the checked log-split theorem and the norm bound above. It
only isolates the conductor-13 factor contribution and does not establish a
bound for the remaining 127 factors.

## Verification

The pinned Lean compile used `guarded_build.py`, `-j1 -M6144`, and the
preserved build `TMPDIR`; it was admitted with 16.3 GiB available and exited
0. A separate guarded `#print axioms` audit was admitted with 16.1 GiB
available and exited 0. Both exported theorems report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The compiled artifact is
`.lake/build/lib/lean/UnitDistance/ZetaLunaConductorThirteenFinalNormRun20260923.olean`.

## Scope

This is an actual coherent genus-character factor bound, not an arbitrary
`genusLinearEulerValue` slot identification. It gives a negative contribution
to the genus log after splitting off this factor. The full genus inequality
and target `H` remain open because the complementary 127-factor remainder is
not bounded here.
