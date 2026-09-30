# Literal fixed-field bridge audit

`field_bridge_audit.py` compares the sealed conditional candidate 08's
`ChallengeZeta.lean` with the manuscript's retained-field section. It first
checks that both source files in the archive are byte-identical to the working
copies. It then parses the field data directly from Lean and TeX, without
importing the manuscript's `check_field.py` or `reproduce.py`.

The script checked all 17 catalog rows: each Lean root-mask product has square
equal to the manuscript's integer radicand, the two Lean coefficients match the printed
coefficients, and the exact norm identity `x² − A y² = B z²` holds. It checked
that the twelve retained word masks agree literally. For each word it evaluated
the associated quadratic character product on every vector in `F₂⁷`, recovered
the 28 square and cross coefficients, and compared the resulting hexadecimal
mask with the manuscript. Integer row reduction gave ranks 7 and 12 for the
completed and retained form lists, and placed the first span inside the second.
It also compares the 17 field rows and all 19 parity predicates in the pinned
`numerics_h7_census_prefix.txt` with these source-derived rows and word masks.
Together with the separate prefix replay, this binds that finite census check
to the literal field presentation in the Challenge and manuscript.

The script also independently sieves primes through `10^4`, computes their
seven genus Legendre symbols, and evaluates the seven completed and twelve
retained quadratic forms on each Frobenius vector. The resulting 45 primes
where the completed forms vanish but a retained form does not agree exactly
with `retained_forced_primes` in the manuscript's `euler.json`. Under the
proved Kummer interpretation of those forms, these are the primes with
completed residue degree two and retained degree divisible by four used in
the positive `S₄` correction. The computation itself is finite integer
arithmetic and does not re-prove that Kummer interpretation.

Command and result:

```sh
python3 lean-formalization/verification/sol-luna-20260922/field_bridge_audit.py
```

The command exited 0 on 2026-09-22. Its exact source hashes and counts are in
`field_bridge_audit.json`. The archive SHA-256 is
`2cf8ff138ff678a2b9f52de20286808a2371bf3a16e5362bdd780dec64ec1385`.

This is a finite-data cross-check of the field's literal presentation. The
Lean theorem `CanonicalRetained.equiv` proves the actual field isomorphism
internally; the script does not independently prove that theorem, the Kummer
injectivity used in the degree argument, the general actual-field local-index
theorem, or the fixed-field zeta inequality.
