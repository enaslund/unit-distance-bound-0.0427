# Portable fixture path review

Static review only; I did not run the updated checker.

## Extraction paths

The three-level layout is consistent with the intended package tree. For the
research checkout, `Path(__file__).resolve().parents[3]` resolves to
`lean-formalization`, and its parent is the repository root. For an extracted
package where the script is at
`unit-distance-zeta/verification/sol-luna-20260923/genus-all-characters/`,
`parents[3]` resolves to `unit-distance-zeta`. The fixture is colocated with
the script, so `with_name("genus_comparison_fixture.json")` is portable. In
package-only mode, `RESEARCH_ROOT/publication/...` is a sibling path outside
the package and should be absent; Lean source candidates first try that
research-root layout, then the package's `UnitDistance/...` layout.

## Pins and projections

The comparison fixture's SHA-256 is checked before parsing; its schema, sigma,
source-hash map, archived-data hash, and 128-row count are checked. If the
original receipt exists, its SHA-256 and sigma are checked, its aggregate
interval is compared exactly, and each row is projected to the five expected
fields (`mask`, `D`, `conrey_number`, `L`, `log_L_S`) before exact fixture
comparison. The direct character/L computations use the fixture only for row
labels and endpoint comparisons; it is not used to calculate the L-values or
deleted factors.

In an extraction without Lean sources, missing files are tolerated and the
returned `source_hashes_verified_in_this_run` list is empty. In an extraction
without the archived JSON, `inherited_archive_verified_in_this_run` is false.
The fixture hash and `archived_sha256` field still bind the embedded
comparison data, so the result can honestly report a portable fixture replay
without claiming that absent Lean sources or the original archive were
re-read. A partial Lean-source set is also tolerated; the returned list shows
which paths were verified.

## Reporting caveat

The current checked-in `genus_full_direct.json` predates the portable-output
fields: it does not contain `source_hashes_verified_in_this_run`,
`inherited_archive_verified_in_this_run`, or
`portable_comparison_fixture_sha256`. It is not a result from the updated
fixture-fallback script and should not be cited as evidence that a package-only
run reported missing sources/archive honestly. A fresh run is needed before
using those new fields as a recorded receipt.

On a fresh package-only run, `all_row_values_inside_inherited_intervals: true`
means containment in the hash-pinned intervals embedded in the fixture; it
does not mean the original archive was available. The separate false archive
flag disambiguates this, but `all_row_values_inside_comparison_fixture` would
be a clearer field name. Similarly, an explicit list of missing source files
would make an empty verified-source list easier to interpret. These are
reporting clarity suggestions; I found no path or hash/projection defect in
the fallback logic.
