# Independent review: short conductor-13 upper certificate

## Scope

This is a source-level mathematical review of
`genus13_short_upper_certificate.py` and its accompanying note. It is not a
Lean proof, a rerun receipt, or an audit of the long interval computation.

## Findings

No substantive flaw was found in the stated short upper-bound argument.

- For a `+1` coefficient, `n^(-σ) ≤ 1/n` follows from `σ>1` and `n≥1`.
  For a `-1` coefficient, `exp(-x)≥1-x` and `log n≤n-1` give the stated
  lower bound on `n^(-σ)`; negating it gives an upper bound for that signed
  term. The exact rational finite sum is formed term-by-term from this
  inequality.
- The cutoff `N=52` is four complete periods of length 13. The character sum
  through `N` is therefore zero, so the shifted tail partial sums inherit the
  ordinary period partial-sum bound 2. Summation by parts gives an absolute
  tail bound `2·53^(-σ) < 2/53`.
- Euler's criterion `a^6 ≡ 1 (mod 13)` for nonzero residues correctly
  distinguishes the quadratic residues; the code checks the full period and
  the selected-prime signs against it.
- The deletion factors have the right directions: `χ=-1` gives
  `1+p^(-σ) < 1+1/p`; `χ=+1` uses the lower bound on `p^(-σ)` to upper-bound
  `1-p^(-σ)`; `χ=0` gives 1. Each actual factor is positive. The separate
  sign split for multiplying the primitive-value and correction upper bounds
  is valid: nonpositive primitive value is already below the positive final
  bound, while for positive primitive value both positive upper bounds may be
  multiplied.

## Source-binding limit

When both Lean source files are present, the checker verifies their pinned
SHA-256 values and text anchors. If neither is present, `source_binding()`
returns successfully with the message that Lean source files are absent; in
that standalone case, the actual χ₁₃-to-Lean-row identification is not
rechecked. The script still checks its embedded period and selected-prime
values by Euler's criterion, but this is not a substitute for source binding.
The accompanying note states this limitation conditionally (“when those
files are present”), so its claim is scoped accurately.
