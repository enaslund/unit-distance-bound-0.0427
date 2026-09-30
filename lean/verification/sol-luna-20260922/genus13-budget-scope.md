# Budget scope of the conductor-13 `<1` bound

## Conclusion

The checked short certificate gives a genuine negative contribution from the
coherent χ₁₃ factor, but it does not by itself lower the currently assembled
five-family numerical upper bound for (H). The subsequent checked
mask-64 theorem and pinned source identify the corresponding publication
character row as `D=13`; that stored row's log enclosure near
`−0.069118609` is much stronger than the new Lean short saving near
`−0.012`. The current allowance `7.337578130846530221` bounds the
*whole* linear component. To improve it using χ₁₃, one needs a better
χ₁₃ enclosure than the stored row and a compatible bound for the other
127 coherent log contributions. Neither follows from a bound on the
total plus an upper bound on one negative summand.

## What the checked bound supplies

The exact short-certificate endpoint is

```text
U = 4689291963776399684905241675231/4745938638374004765750000000000
  = 1 - δ,
δ = 56646674597605080844758324769/4745938638374004765750000000000 > 0.
```

The external rational checker first gave the selected-prime-deleted χ₁₃
value below `U`; its source review checks the 52-term coefficient bounds,
period tail, selected correction and sign case. The later checked Lean
`ZetaLunaConductorThirteenFinalNormRun20260923` theorem proves
`‖coherent χ₁₃ value‖ ≤ U` with no numerical premise, by combining the
actual coefficient prefix, actual tail, primitive positivity and exact
deletion correction. The earlier short-bound interface still has its
conditional statement, but the final-norm theorem supplies its premise and
derives

```text
genusLinearLogAtSigma
  = log ‖coherent χ₁₃ value‖ + otherCoherentLogRemainder
  < otherCoherentLogRemainder.
```

The checked `ZetaLunaConductorThirteenShortLogSavingRun20260923` corollary
also proves `log ‖coherent χ₁₃ value‖ < -δ` by log monotonicity and
`log(1-δ) < -δ`. This is a strict saving for that one actual coherent
term, not a bound on the remaining sum.

The checked index-free product theorem identifies the product of all 128
coherent genus values with the product of the existing 128 linear Euler
values. It equates their total log contribution to
`genusLinearLogAtSigma`; it does not identify χ₁₃ with a particular literal
`genusLinearEulerValue i`, or bound the other 127 coherent terms separately.
The checked intrinsic mask alignment identifies publication character
row 64 but not a fixed primewise literal Euler slot. Its weaker short
upper cannot improve the printed row allowance.

## H budget and numerical gap

In the five-family identity the genus linear component has multiplicity 1,
then the whole completed-field log is normalized by degree 16,384. If a
separate argument supplied `otherCoherentLogRemainder ≤ B_R`, the conductor-13
estimate would give a linear upper at most `B_R - δ`, and thus a potential
normalized reduction of at least `δ/16384`, with all other terms fixed. This
is conditional arithmetic only: no such numerical `B_R` is present here, and
the full completed-field local-factor/row-grouping bridge remains open.

The existing replay still has the full linear-row allowance
`7.337578130846530221` and its unchanged five-family assembled upper
`0.04216181893948094953138458`. Its slack remains
`3025952523430771/50000000000000000000000000` to the printed manuscript
threshold `0.042161819`, and
`200003025952523430771/50000000000000000000000000` to the selected Lean
ceiling `0.042165819`. The `<1` factor result does not change either gap in
the checked assembly. (H) remains unproved in Lean.

## Sources and limits

- `genus13_short_upper_certificate.py` / `.md` / `.json`: exact external
  rational value bound and its assumptions.
- `ZetaLunaConductorThirteenShortBoundRun20260923.lean`: conditional transfer
  of the numerical norm bound to a negative χ₁₃ log contribution.
- `ZetaLunaConductorThirteenFinalNormRun20260923.lean` and
  `ZetaLunaConductorThirteenShortLogSavingRun20260923.lean`: checked
  unconditional actual χ₁₃ norm endpoint and exact rational negative-log
  saving, outside the sealed candidate-14 proof-input closure.
- `ZetaLunaConductorThirteenManuscriptRowRun20260923.lean` and
  `conductor13-manuscript-row64.md`: checked mask/discriminant alignment,
  with external pinned inherited AFE row 64 source binding.
- `ZetaLunaConductorThirteenLogSplitNonzeroRun20260923.lean` and
  `ZetaLunaCoherentGenusComponentRun20260922.lean`: actual log split,
  nonvanishing, and index-free equality of the coherent genus product with
  the existing linear product.
- `ZetaLunaImprimitiveLogRun20260922.lean`:
  `completed_imprimitive_hfactor_of_grouping`, whose actual local-factor and
  five-row grouping hypotheses remain separate.
- `analytic-replay-20260922.json` and `numerics.md`: current printed group
  allowance and exact five-family assembly.

This assessment is read-only mathematical scope analysis. It does not rerun
the short certificate, regenerate AFE factors, or prove a row-to-Artin
identification.
