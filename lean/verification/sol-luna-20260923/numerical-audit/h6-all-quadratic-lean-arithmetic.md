# All 32 H6 quadratic rows: Lean endpoint arithmetic

The guarded batch receipt `h6_all_quadratic_expint.json` has SHA-256
`54e9fe4921c92366da8644e27bd8d2217a04b678046dfa3c31701519b4c917ce`.
`UnitDistance/H6AllQuadraticExpintArithmetic20260923.lean` transcribes all
32 direct and frozen target log upper endpoints from that receipt as exact
rationals. It proves each strict comparison separately, then proves the
`Fin 32` aggregate `all_32_rows`. This certifies arithmetic on transcribed
endpoints, not the external analytic intervals or their assumptions.

The first guarded compile (source SHA-256
`4742f54381affa2fcd2e8b85b792a561bc0ce6ae994b0cc22bd3f58cb73ba5d2`)
exited 1 on a missing `Fintype (Fin 32)` instance in `fin_cases`; the 32
individual `norm_num` proofs had no diagnostics. Adding the direct
`Mathlib.Data.Fintype.Fin` import resolved that ordinary elaboration error.
The repaired source compile exited **0** under the pinned Lean 4.32
toolchain, `-j1 -M2560`, disk-backed TMPDIR, shared guard/lock and a
900-second timeout; guard admission was 16.1 GiB host available and
1.31 GiB cgroup headroom. A separate focused audit exited **0** after
admission at 15.9/1.30 GiB and reported exactly `propext`,
`Classical.choice`, and `Quot.sound` for `all_32_rows`.

Final source SHA-256:
`ceee599a2ad3ed1ed5528e58c4ad9330e60cca9ea737079b9320508136ebcbf1`;
audit source SHA-256:
`5a814cf2ce9d36fac91a286d25b420f271782455277f0a2509436f31cbff44cb`;
`.olean` SHA-256:
`bc35a86892c6c9c6fd291f09c3ee3ccbc5f8a7368196c1601fb198b31a845721`.
An [independent transcription review](h6-all-quadratic-expint-lean-transcription-review.md)
matched all 64 rational constants to the receipt's exact dyadic endpoints,
checked the 32 index/twist cases, and found every margin positive.

The research leaf is outside the selected Challenge/Solution proof closure
and is checkout-only. The source archive ships this check report and the
external batch receipt, while preserving exact historical selected-proof
inputs. No full selected verifier run was performed for this leaf. The
row-specific factor identities, functional equations, contour conditions,
global coefficient bounds, and fixed-field H inequality remain open.
