# Independent exact-arithmetic check of the replay endpoint

`numerics_check.py` independently checks selected exact-arithmetic identities
in `verification/external-zeta-20260922/analytic-replay-20260922.json`.
`numerics_h7_prefix_check.py` adds an independent recomputation of the
10-million H7 finite-census prefix. `numerics_hecke_coeff_check.py`
independently recomputes four representative Hecke rows, one from each mixed
quadratic, mixed quartic, pure quartic, and mixed octic family. Those three
checkers use the Python standard library and do not import or execute manuscript
certificate code.
The one-factor analytic supplement `numerics_afe_one_factor.py` uses
`python-flint==0.9.0`; its direct-kernel method and runtime requirements are
documented separately in `numerics_afe_one_factor.md`.

Run from any directory with:

```sh
python3 lean-formalization/verification/sol-luna-20260922/numerics_check.py
python3 lean-formalization/verification/sol-luna-20260922/numerics_h7_prefix_check.py
python3 lean-formalization/verification/sol-luna-20260922/numerics_hecke_coeff_check.py
```

## H7 finite-census prefix

`numerics_h7_census_prefix.txt` is the raw 181,812-byte prefix table copied
from the sealed manuscript data archive. Its SHA-256 is
`fafbdaff49c1317d2606df81ca886fea6fb01200b4da7d490e7550bb84b342b3`, matching
the replay's recorded source hash. The upstream census source is bundled as
`numerics_h7_census_source.py`, pinned at SHA-256
`3bf8a7af2e4b9d219e9ddc6f35631333fa67dc283291b0c1040332a1487be493`, and
never executed. The checker also confirms this source hash is recorded by the
bundled replay JSON.

The checker sieves every prime in `[17, 10,000,000)` with its own byte-array
Eratosthenes sieve, derives the genus splitting residue classes by quadratic
residue tests modulo `3, 5, 7, 11, 13`, and evaluates all 17 recorded quadratic
character forms at each of the 4,980 split primes. It obtains square roots by
its own Tonelli-Shanks implementation and computes the two conjugate Legendre
symbols directly. It then applies the 19 recorded parity predicates and
rebuilds each nonempty census bin and its `10^30/p` floor reciprocal sums.

Observed result:

```text
PASS independent H7 census-prefix recomputation
prime_range=[17,10000000); genus_split_primes=4980
field_character_evaluations=84660
first_hit_predicates=19; matching_nonempty_bins=2308
full=4980; completed=4949; complement=31
comparison=every bin endpoint, count, reciprocal sum, class split, and first-hit count matched
```

This independently checks the finite enumeration and all stored prefix bins
for the pinned field forms and predicates. Those forms/predicates are read
from the data table, not independently reconstructed here; the independent
generator-table review is separate. The check does not validate the
infinite-prime tail or establish the zeta hypothesis (H).

## Hecke coefficient rows

`numerics_hecke_coeff_check.py` recomputes the first 128 coefficients in the
pure H7 sector 1920, twist `-1`, conductor `57715257600`. It derives the
residue-vector action from the pinned quadratic form, evaluates central
characters over the four square-root embeddings when needed, expands the
recorded bad-prime Euler denominators, and multiplies local coefficients over
prime powers. These calculations use exact integer and modular arithmetic.
The compact `numerics_hecke_coeff_fixture.json` supplies only the selected
sector metadata, row Euler factors, expected coefficient prefix, and SHA
bindings to the original full moment and arithmetic tables. It is 7,258 bytes;
the full moment table is not needed for standalone replay. When the original
tables are present in a research checkout, the checker verifies their hashes
against the fixture bindings before using it.

Observed guarded result:

```text
PASS independent H7 Hecke coefficient prefix
moment_table_sha256=c999ec7882f758e72f683fc3572406ed0d325ff674958e23a0349f322ecd84bf
arithmetic_source_sha256=e1d892ba20f90bf6ea15e52f710ead0b8806a6db50d95792a76ebe2552183948
fixture_sha256=db0e2050cf3e9a3d1f0b79f4481b55609b52fb071a2ade4c93acfc21e864a1ae
sector=1920; twist=-1; conductor=57715257600; coefficients=128
comparison=all 128 complex coefficients matched exactly
```

It also checks three representative rows:

- Mixed quadratic: H6 mask 1586, twist `-1`, degree 2, conductor `15015`.
  The source has no displayed prefix, so the checker recomputes all 981
  coefficients recorded for `N=981` and matches the SHA-256 of the complete
  signed coefficient vector:
  `baec4879c9e60ab3f2e657ff9f4d9cac64a39eebc3aa123495844f19e3ef654c`.
- Mixed quartic: H7 mask 274, twist `-1`, degree 4, conductor `9234441216`.
  All 128 complex coefficients match its stored prefix exactly.
- Mixed octic: H7 mask 307, twist `-1`, degree 8, conductor
  `3331050959834357760000`. All 128 complex coefficients match its stored
  prefix exactly.

`numerics_hecke_family_fixture.json` stores only these selected sectors and
rows, with SHA-256 bindings to the six full arithmetic/moment JSON sources.
It is 4,703 bytes; its SHA-256 is
`5fd9c83deb0fcdef56d314657ae8e1c7408c5508e652834e32cdabc3de234200`. The
source pairs are pinned as follows: H6 arithmetic/moments
`b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771` /
`a7e65537a05389f11115a8cf64c186ead6b1dc4973a8c5f862f31a34fdeb40f1`; H7
mixed-quartic arithmetic/moments
`4453a7fe7549ec3e189817e9081bb24c1d3244c3b1249604ab811ab289bf554f` /
`0777fc81c8a9a6bcff795371e3f7f42095d86e268f141c0dba72777b40e82227`; H7
mixed-octic arithmetic/moments
`2c8d752f6206b6793b37d91ca9ad343b6c3c4ff92f61fed9ade9e307f0013836` /
`1249e9d714685fb0b92ce09c78578248b5d7a1d2a4dfab68252056ed7887063d`.
When available, the checker verifies those source hashes before using the
compact fixture. The independent recurrences use quadratic residue symbols,
the encoded Frobenius quadratic form, eta evaluations for scalar factors,
the row twists, and the recorded bad-prime Euler denominators.

Guarded family result (exit 0; admitted with 14.1 GiB available; 13.9 seconds):

```text
pure quartic mask1920: 128/128 matched
mixed quadratic mask1586: all 981 coefficients bound by complete-vector hash
mixed quartic mask274: 128/128 matched
mixed octic mask307: 128/128 matched
```

These checks validate selected finite coefficient rows, not field
identification, complete moment bins, or any AFE enclosure. The quadratic
full-vector SHA comparison binds recomputed coefficients to the pinned table
record and remains conditional on that record.

The checker pins the replay JSON by SHA-256, then checks the five AFE group
labels/degrees/counts. For each group it verifies, as an exact rational
identity, that the recorded rational allowance equals the exact input upper
endpoint plus the recorded rounding slack, and that the allowance is an upper
rounding on the `10^-18` decimal grid. It independently combines the five
printed allowances with signs

```text
Y_upper + bad_upper - order_four_lower - central_lower + debit_upper
```

and checks equality with the recorded final rational and decimal upper bounds.
It verifies the manuscript-threshold slack identity and separately computes
the selected Lean ceiling `42165819/10^9` minus the same rational endpoint.
This is an arithmetic comparison with the displayed H hypothesis ceiling,
not a proof of H. The checker also decodes the fresh dyadic
ball endpoints as rationals, checking that the rational endpoint lies in the
ball and that the ball's upper endpoint is the table's original assembled
upper and remains below the stated ceiling.

Observed result:

```text
PASS independent exact rational analytic-table checks
record_sha256=34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e
afe_groups=5
assembled=2108090946974047476569229/50000000000000000000000000
ceiling_slack=3025952523430771/50000000000000000000000000
selected_lean_ceiling_slack=200003025952523430771/50000000000000000000000000
```

## Scope and limitations

The endpoint check audits arithmetic encoded in the replay record; it does not
regenerate AFE receipts or an analytic tail. The census check does regenerate
the finite prefix from the listed forms, but does not derive those forms or
predicates or regenerate the full `10^12` prime census. The Hecke check covers
only the stated coefficient prefix. Hashes pin these checks to supplied
records; they do not authenticate their mathematical inputs. None proves the
zeta hypothesis (H), so the conditional theorem retains that explicit
numerical hypothesis.

## Standalone package inputs

The standalone zeta source package can replay the checks with these files
under `verification/sol-luna-20260922/`:

- `numerics.md` and `numerics_check.py`;
- `numerics_h7_prefix_check.py`, `numerics_h7_census_prefix.txt`, and
  `numerics_h7_census_source.py`;
- `numerics_hecke_coeff_check.py`, `numerics_hecke_coeff_fixture.json`, and
  `numerics_hecke_family_fixture.json`.
- Optional one-factor interval replay: `numerics_afe_one_factor.py`,
  `numerics_afe_one_factor_fixture.json`, and
  `numerics_afe_one_factor.md`. This optional replay needs python-flint; the
  other three checkers above use only the Python standard library.

The endpoint and census checks also read
`verification/external-zeta-20260922/analytic-replay-20260922.json`, already
selected by the exporter's existing external-zeta directory entry. The fixture
avoids bundling the 16 MiB full moment JSON and is below the exporter's
per-file reference cap. The full moment and arithmetic tables are optional
outside the research checkout because the fixture carries their expected
SHA-256 values. The endpoint checker resolves the replay record from the
project root; the census checker resolves its data and producer copy beside
itself and checks the replay's producer binding.

The conditional package selects these files through the one-level reference
glob in `docs/CONDITIONAL_SUBMISSION.md`; no exporter code change is needed.
No other research files are runtime dependencies. The minimal simulated
package contained the eight listed files plus the already selected external
replay JSON. All three checkers passed under one guarded run (admitted with
13.3 GiB available, exit 0, 5.96 seconds). In package mode the family checker
uses the compact hash-pinned fixture because the six full research JSON files
are absent. The separate research-checkout run matched every copied field to
the six full source files.
