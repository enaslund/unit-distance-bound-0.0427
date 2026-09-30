# Independent terminal exponent arithmetic

`geometry_margin_audit.py` recombines the exact rational endpoint bounds
proved in the six Lean source files whose SHA-256 hashes it pins. It uses
Python `Fraction`, with no floating-point number in the decision. It checks
the coefficient signs in the formula for `Witness.margin`, including the
negative root-discriminant cost, and independently verifies that the margin is
increasing for every admissible signature ratio `θ ≥ 4095/8192`.

At the worst ratio, the conservative rational endpoints give

```text
margin(θ) − 4ε ≥ 53378026654746585869453 / 12800000000000000000000000000
              ≈ 0.00000417015833240208.
```

After the selected ceiling is raised by exactly `0.000004`, the remaining
lower bound is the positive rational

```text
2178026654746585869453 / 12800000000000000000000000000
≈ 0.000000170158332402077.
```

The script exited 0 on 2026-09-22; `geometry_margin_audit.json` records its
source hashes and exact result. This is a separate arithmetic check of the
last scalar implication. The quoted input bounds are Lean theorems in the
selected closure and are covered by the existing archive-07 pinned pass and
archive-08 proof-input identity check. This script does not prove the pair
integral bounds from scratch or the fixed-field zeta hypothesis.
