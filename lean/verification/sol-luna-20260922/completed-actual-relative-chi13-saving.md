# Checked completed-field log bound with the actual relative factor

`UnitDistance/ZetaLunaCompletedChi13LogSavingRun20260923.lean` proves
the no-premise endpoint

```lean
Real.log completedImprimitiveZetaValue <
  otherCoherentLogRemainder +
    Real.log ‖actualRelativeEulerValueAtCertificatePoint‖ -
      conductorThirteenShortLogSaving
```

The saving is the exact rational
`56646674597605080844758324769 / 4745938638374004765750000000000`.
The endpoint is
`completed_imprimitive_log_lt_other_remainder_add_relative_minus_short_saving`.
The argument combines the checked actual completed-field log split, the
unconditional χ₁₃ log split for the 128 coherent genus factors, and the
checked actual χ₁₃ short-log-saving theorem. No premise is added. The theorem
concerns only the completed imprimitive log; it does not imply the full H
bound or identify the remaining genus/relative terms with the manuscript's
other Artin rows.

The guarded compile and focused axiom audit both passed. The endpoint uses
only `[propext, Classical.choice, Quot.sound]`.

| File | SHA-256 |
| --- | --- |
| `UnitDistance/ZetaLunaCompletedChi13LogSavingRun20260923.lean` | `9cb3662498fe8b7847c89fe62dea951cd84a91cd23574985ab76c1ce7e847b29` |
| `UnitDistance/ZetaLunaCompletedChi13LogSavingRun20260923Audit.lean` | `43fc4353682c60eeaa8b0684a8d27d90915ed963e050f51fd468d8e878f6530f` |

The pinned `-j1 -M6144` source compile exited 0 (guard admitted at 13.3 GiB);
the separate guarded audit exited 0 (15.9 GiB).
