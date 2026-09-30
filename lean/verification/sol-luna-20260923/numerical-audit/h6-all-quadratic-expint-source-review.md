# Source review: H6 all-quadratic expint checker

## Scope

Read-only review of `h6_all_quadratic_expint.py` and its plan before the
guarded numerical run. No computation was run. The checker SHA-256 is
`060af68df4b7e1eb6dfba87e88ca13fa26cbccca16966c2c256b4fc8cd2116c3`;
all nine source/receipt pins in the script match the current files.

## Findings

No blocker found. In the pinned arithmetic, moment, and target JSON files, all
three tables contain the same 32 unique twists. The arithmetic rows all have
gamma `[0,1]`, root number `+1`, and multiplicity `1`; conductor counts are
8 at 15015, 8 at 240240, and 16 at 960960. The script iterates all arithmetic
rows and matches each twist into both other tables, checking conductor,
gamma, root number, multiplicity, cutoff, target kind, and target PASS status.

For each row it reconstructs the full coefficient vector, checks its hash and
exact bin moments, then evaluates both expint sums and tails using the reviewed
single-row helpers. The interval directions are consistent: `abs(A+B)` is
enlarged by the tail upper; bad Euler factors are evaluated as Arb complex
polynomials with zero excluded; the positive modulus bound is multiplied by
their absolute values before taking an upper endpoint and logarithm; and the
direct log upper is compared against the target upper with a nonnegative
exact margin. Per-twist comparison and consistency failures are accumulated
into the output; if those occur, the script writes all row diagnostics before
exiting with status 1.

Two implementation caveats:

- It checks that each twist map has length 32, but does not explicitly test
  uniqueness or equality of the arithmetic, moment, and target twist sets.
  Those properties hold for the current hash-pinned inputs; adding explicit
  set checks would make the invariant self-documenting.
- Unexpected exceptions during a row (for example, malformed data or a
  failed Arb operation) abort before `OUTPUT.write_text`, so diagnostics are
  saved for comparison/consistency failures but not arbitrary exceptions.

The replay remains a conditional finite external calculation, not a proof of
H or of the global coefficient and analytic assumptions. No expensive work
was run.
