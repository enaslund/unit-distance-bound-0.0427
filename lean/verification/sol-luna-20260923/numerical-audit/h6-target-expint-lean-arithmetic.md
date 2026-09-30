# H6 independent expint row: Lean arithmetic check

The external guarded expint receipt `h6_target_sigma_expint.json` has SHA-256
`56aa4b9fddbe580d852119f79329635c06630d2833315857b581fe1aa0bb4e2f`.
`UnitDistance/H6TargetExpintRowArithmetic20260923.lean` transcribes its exact
dyadic log upper and the frozen H6 mask-1586 twist-`+1` row upper as rationals.
Its theorem proves the first is strictly below the second. An
[independent transcription review](h6-target-expint-transcription-review.md)
matched both rationals and the exact positive margin to the receipt.

The guarded source compile exited **0** with `-j1 -M2560`, after admission
at 14.7 GiB host available and 1.45 GiB cgroup headroom. A separate guarded
focused audit exited **0** after admission at 14.7/1.46 GiB and reported only
`propext`, `Classical.choice`, and `Quot.sound`. Both used the pinned Lean
4.32 toolchain, disk-backed build TMPDIR, the shared lock, and a 900-second
timeout. Source SHA-256:
`a6138198cafd39d308589869a265f6bc112281e442ddb96482158d3c6a091e92`;
audit SHA-256:
`9817445a800121b95515db2c5fbc2bf5ccc2f4c67b1cab43d54cdd028864832f`;
`.olean` SHA-256:
`4ecca1125530e1ccbc436209ece3bba731bfd472814abaf7d32ce27418b1a769`.

This proves exact arithmetic on the transcribed external interval endpoints.
It does not certify the Arb intervals, the AFE formula or its hypotheses, the
global coefficient bound, the factor identity, or the fixed-field inequality
H. The earlier SplitKernels row comparison remains a separate **FAIL**.
The research leaf is outside the selected Challenge/Solution proof closure.
