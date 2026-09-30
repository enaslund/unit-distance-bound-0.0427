# Independent source review: H7 all-row Hecke prefix checker

I reviewed `hecke_all_rows_prefix_check.py`, its full-row fixture, and its
receipt after the independent review/check had completed. This is a source
audit; I did not rerun the 28,416 coefficient comparison.

## Selection and counts

The research-input path pins the canonical H7 Euler receipt, three group
receipts, three arithmetic tables, and the coefficient helper. It checks that
the top receipt binds the group receipts, and that each globbed per-sector
moment file is uniquely hash-bound by its group receipt. It joins each moment
file to the arithmetic sector by mask and each row by twist, then compares all
copied arithmetic-row fields before saving the moment coefficients only as
expected values (`research_inputs`). Mixed-quartic and octic files are selected
by their filename prefixes; the pure-quartic family uses its single named
moment file.

The pinned fixture contains 222 distinct `(family, mask, twist)` keys and
28,416 expected coefficients of length 128. Its family counts are 136 mixed
quartic, 8 pure quartic, and 78 octic; the weighted multiplicities are 168,
8, and 84, respectively, for 260 factors total. The script checks these
per-family row and multiplicity totals at runtime. The H7 note's 836 total
adds 576 inherited factors; this checker covers only the 260 new factors.
While the checker does not itself assert global uniqueness of all moment-row
keys, the inspected fixture has 222 unique keys and the source rows are
hash-pinned.

## Coefficient reconstruction

The 28,416 values are actually recomputed; the stored prefixes are not copied
into `got`. For every row, `recompute` builds the form action table from the
literal sector form, computes residue vectors from the pinned helper, uses the
base radicands and eta coefficients for the central-sign fallback, applies the
quadratic twist, and constructs local factors through the largest prime power
at most 128. It uses the literal denominator at listed bad primes. At good
primes it calls the rank-four or rank-eight local-denominator formula, then
raises the exact Gaussian-integer quartic phase to the row's quartic exponent
and local degree. It inverts each local denominator by an exact recurrence and
combines prime-power coefficients multiplicatively. Only then does it compare
against `expected_first128`.

The local formulas are internally consistent with the intended models:
`code = ±2` gives the split/inert quadratic-pair polynomials, while `code = ±1`
gives `(1 − sign·T)^4` or `(1 − sign·T)^8`; multiplying the degree-`j`
denominator coefficient by `phase^(exponent·j)` implements the stated quartic
twist. The mod-5 table sends 2 to `i`; the mod-13 table uses powers of 2, a
primitive root, with phases cycling through `1,i,−1,−i`. The pinned fixture
exercises 38 nontrivial phase rows: 32 mixed-quartic rows, 2 octic rows at
modulus 5, and 4 octic rows at modulus 13. The prime divisors of those
moduli are handled through the literal bad-prime factors.

Thus the comparison is independent of the original moment producer's
coefficient-generation routine, but it is not independent of all arithmetic
inputs: the finite form conventions, eta data, bad Euler polynomials, and
family-to-row recipes are trusted literal inputs. Agreement over the first
128 coefficients is finite evidence; it does not establish global Euler
factor identities or the Artin-factor identification.

## Full sources and compact fixture

There are two source-verification paths. Running the script with
`--make-fixture` calls `research_inputs`, which checks live full-source hashes
and their receipt chain, then writes the compact fixture. Normal replay calls
`fixture_inputs`: it verifies the fixture's pinned SHA-256 and schema and then
recomputes all coefficients from that fixture. It does **not** call
`research_inputs` or re-hash the full research tables. Consequently a normal
compact replay proves the stated comparison against the pinned fixture and its
embedded source-hash provenance; it does not independently verify that the
current full research files still match that provenance. The fixture is
339,343 bytes and is pinned by SHA-256
`a28de6177ddb0ce6513c3520cbc2c342fcb109ab94868a1775aafe7c9fe933be`.

The reviewed final checker,
`hecke_all_rows_prefix_check.py` SHA-256
`9e75bf624a62e9948071707a5ba739227771c13d27f7bd929d25da1603ab56db`,
unconditionally checks the helper source before importing it:
`numerics_hecke_coeff_check.py` SHA-256
`3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329`.
This helper check runs in both full-source and compact-fixture modes. The
final guarded fixture regeneration, research replay, and standalone fixture
replay all passed; the fixture bytes and hash remained unchanged. Receipts are
`hecke_all_rows_prefix_fixture_generation.json`,
`h7_all_new_coefficients_check.json`, and
`hecke_all_rows_prefix_package_smoke.json`.

The checker records its own source hash in the output receipt, but does not
compare that hash against a second pinned value before execution. The finite
reconstruction remains reviewable from the checked-in source; a portable
receipt should be read together with the exact checker source version stated
above.

## Scope

The checked source supports a 128-term exact coefficient-prefix comparison
for each of the 222 supplied new rows and confirms their stated 260-factor
multiplicity. It does not prove row construction, the global Artin-factor
identity, local factors beyond the finite inputs checked, functional
equations, AFE tail bounds, or the final H7 inequality. The existing
[`hecke_all_rows_prefix_review.md`](hecke_all_rows_prefix_review.md) correctly
states these mathematical limits.
