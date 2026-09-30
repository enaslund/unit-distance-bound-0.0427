# H6 all-quadratic expint: Lean transcription review

Read-only comparison of
`UnitDistance/H6AllQuadraticExpintArithmetic20260923.lean` with the pinned
external receipt `h6_all_quadratic_expint.json`. No Lean or numerical job was
run for this review.

## All 32 row pairs

The receipt SHA-256 is
`54e9fe4921c92366da8644e27bd8d2217a04b678046dfa3c31701519b4c917ce`, matching
the hash pinned in the Lean source. I parsed all 64 Lean endpoint literals
and compared them with each row's exact direct and target endpoint strings
and with the outward dyadic upper endpoints in the receipt. All 32 pairs
match exactly; all 32 exact target-minus-direct margins are positive. The
smallest is for twist 55, approximately `2.0592384721174497e-20`.

The Lean theorem comments and endpoint-index maps match the receipt order,
which also matches the arithmetic source and target evaluator row orders:

```text
-1, 1, -2, 2, -3, 3, -5, 5, -6, 6, -10, 10, -11, 11,
-13, 13, -15, 15, -22, 22, -26, 26, -30, 30, -55, 55,
-65, 65, -110, 110, -130, 130
```

Each row theorem has the strict direction `direct_i < target_i`, matching the
positive margin. The receipt reports 32 rows, no strict endpoint failures,
and no consistency failures. The Lean `all_32_rows` theorem covers every
`Fin 32` index: it splits all 32 cases and applies the corresponding row
theorem after unfolding the matching endpoint maps. Its default map branch is
unreachable for `Fin 32`.

## Provenance and scope

All nine source hashes in the external receipt match the current files; the
receipt's checker hash also matches. The single-row twist +1 entry agrees
exactly with the previously reviewed target-sigma expint receipt. The final
Lean source SHA-256 is
`ceee599a2ad3ed1ed5528e58c4ad9330e60cca9ea737079b9320508136ebcbf1`; the
companion axiom-audit source SHA-256 is
`5a814cf2ce9d36fac91a286d25b420f271782455277f0a2509436f31cbff44cb`. The
audit source imports the arithmetic leaf and prints the axioms of
`all_32_rows`. Its check report records successful guarded compilation and a
focused audit with only `propext`, `Classical.choice`, and `Quot.sound`; I did
not rerun either job.

The external receipt reports **PASS all 32 H6 quadratic rows by direct
expint replay**. This is a conditional external numerical result, not a Lean
proof of the analytic endpoints. It uses Arb/FLINT and assumes the row
identities, functional equations, contour-growth conditions, complete bad
Euler factors, and global degree-two coefficient bound. The prior
single-row SplitKernels strict FAIL and the target aggregate replacement
remain separate receipts; this batch receipt does not change them or prove
the global hypothesis H.
