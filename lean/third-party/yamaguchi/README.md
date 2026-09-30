# Yamaguchi pro-p and cohomology source port

This source slice comes from [Naganori Yamaguchi, SawinTotallyRealTowers](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers), commit `3a455e1aa9140dbbe7b7d68f508392a69c86d0f4`, under Apache-2.0. The included `LICENSE` is the original license. No upstream NOTICE file was present.

The manifest (`manifest.json`) lists 1,309 modules; this package ships the
1,287 of them in the selected import closure (the other 22 are listed with
their hashes but are not imported by the selected closure and are not
shipped). The modules cover the finite-stage transgression, actual continuous cohomology, relation-rank/H² comparison, relative pro-p Nakayama, profinite presentation definitions, actual finite and maximal extensions with finite ramification support, finite abelian composita, local valuation and ramification foundations, and signed quadratic generators and discriminants. Their isolated dependency closures were checked under this project's earlier Lean 4.32.0 pin after the recorded API adaptations. Their original declaration namespaces and mathematical statements are retained. Upstream uses Lean 4.33.0.

The separate `lean-v4.35-migration.patch` records later source migration
edits, including the `IwasawaIndexing.lean` import relocation from
`Mathlib.Logic.Denumerable` to `Mathlib.Basic.Denumerable`. The manifest's
`sha256` records each currently vendored file; its `compatible_sha256` and
`upstream_sha256` preserve the pre-migration compatible source and original
upstream source. The 4.35 patch reverses before the historical
`compatibility.patch` is reversed. Its exact changed-file set is checked
against the manifest and source by the provenance checker.

A Lean 4.35 adaptation of `FormalCoreBase/PowerSeriesComposition.lean`
replaces local formal log/exp composition proofs with results from
`Mathlib.RingTheory.PowerSeries.Log`. The selected source's in-file notice
states this proof replacement explicitly. The migration manifest records
its exact source hash, and the 4.35 patch reverses the change. This
distinguishes a proof-source replacement from a routine import relocation.

`compatibility.patch` records all changes before local import relocation; it touches 88 files, and the manifest's `compatible_sha256` differs from `upstream_sha256` for exactly those 88. Each vendored file additionally has its local imports prefixed with `UnitDistance.Upstream.Yamaguchi` and a modification notice. The manifest records the original, compatible, and final source hashes. Builds require no separate upstream checkout; the selected dependency pins are in the package lockfiles.

The paragraphs that follow are historical records of the earlier slices of
this port (95, 130, 509, 511, 517, 596, 803, 831, 838, 842, 856, 1,029,
1,262 and 1,309 modules). The module counts and pending/queued statuses in
them describe the manifest at the time of each build or audit, not the
current 1,309-entry manifest, and the cited `verification/` logs are the
receipts of those earlier runs.

The isolated 95-module build and its complete transitive axiom audit passed. The proper build of the relocated sources also passed (2,786 jobs), followed by the complete 2,891-declaration imported-project audit, including private and foreign-namespace port declarations. It uses only `propext`, `Quot.sound`, and `Classical.choice`; see `verification/yamaguchi-slice-build-and-audit.log`. Independent kernel replay is a separate check. This slice does not prove the arithmetic six-relation bound, construct the required infinite tower, or discharge the arithmetic family of fields that the research project's goal (an explicit unit-distance exponent) requires.

The 13 quadratic modules compile byte-for-byte unchanged before import relocation. Their isolated imported-source audit checked 64 declarations with the standard three axioms. The original 95-module build remains the historical checkpoint described above; the added proper build is recorded separately.

The added quadratic slice passed the relocated proper build (2,082 jobs) and
64-declaration imported audit. The two Frattini/fixed-field modules also
retain the original proofs unchanged; their proper build passed 2,322 jobs
and their complete imported audit checked 1,532 project declarations with
only the standard three axioms. See `verification/yamaguchi-quadratic13-*`
and `verification/yamaguchi-frattini2-build-and-audit.log`.

The additional 14 tower/cyclic cohomology modules include field-unit H²
inflation injectivity, the restriction kernel theorem, and the cyclic
coefficient-norm comparison. Their isolated build and 273-declaration audit
passed. One lemma needs a local elaborator transparency setting, recorded in
the compatibility patch; its statement and proof text are unchanged.
The relocated proper build and complete imported-source audit also pass; see `verification/yamaguchi-tower-cyclic14-build-and-audit.log` (273 declarations, only the standard three axioms).

The six actual free-source construction and minimal-epimorphism modules also
compile unchanged before import relocation. Their normal build passed
2,232 jobs and their complete imported audit checked 2,142 declarations,
with only the standard three axioms. See
`verification/yamaguchi-free-source6-build-and-audit.log`.

The expanded maximal-extension closure contains 400 modules, including 34
compatibility-modified sources. Its isolated build passed in full, and its
complete 13,053-declaration audit uses only the standard three axioms. The
additional `RationalRamificationSupport` leaf also compiles unchanged. All
130 previously public files retain their recorded hashes; the merge adds
379 files, giving 509 in total. See
`verification/yamaguchi-port-maximal-extension-fifth.log`,
`verification/yamaguchi-port-maximal400-audit.log`, and
`verification/yamaguchi-public130-premerge-manifest.json`. The expanded
relocated build passed (4,447 jobs), and its complete imported-project audit
checked 15,465 declarations with only the standard three axioms; see
`verification/yamaguchi-maximal-build.log` and
`verification/yamaguchi-maximal-audit.log`. This closure constructs genuine
maximal extensions; it does not prove the sharp six-relation bound needed
for the complex arithmetic tower that the research project's goal requires.

Two further unchanged pinned leaves, `AdicCompletionMap` and
`MultiplicativeInducedShapiro`, have passed isolated checks and are staged
for the actual tensor-cohomology adapters. The public manifest now has 511
modules at that checkpoint. The normal tensor-adapter build passed (4,402
jobs), including both leaves, and its scoped 145-declaration transitive
audit uses only the standard axioms; see
`verification/actual-tensor-h2-{build,axioms}.log`.

Six unchanged Hilbert ramification leaves (`RealLowerGroups`,
`UniqueExtensionIntegralClosure`, `Polynomial`, `Monogeneity`,
`UniformizerGradedHom`, and `CompleteDVF`) have also passed isolated Lean
checks. They are staged for the actual odd-tame local relations; their
relocated build passed (2,646 jobs), and the complete imported-source audit
checked 1,029 declarations using only the standard axioms; see
`verification/yamaguchi-tame6-{build,audit}.log`. The manifest had 517
modules at this checkpoint.

A further 79 checked upstream leaves cover supported-idele localization and
actual completion/ramification comparison. They support the four checked
project adapters recorded in `supported-idele-adapters.json`. The normal
build passed (4,518 jobs), and the full imported-source audit checked
14,287 declarations with only the standard axioms; see
`verification/supported-idele-{build,audit}.log`. The manifest contained
596 modules at this checkpoint.

The actual totally-complex field-unit detector and unrestricted finite
inertia/stage adapters passed direct checks and a combined 115-declaration
transitive axiom audit with only the standard axioms. Their 207 additional
upstream dependency leaves are independently checked and now staged,
bringing the manifest to 803 modules. The adapters are recorded in
`complex-detector-adapters.json`; their relocated normal build and full
imported-source audit are pending in `verification/complex-detector-*`.

The complete 674-module finite-Kummer/localization closure now passes the
isolated build and a full 20,181-declaration imported-source audit, using
only the standard axioms. Its exact source freeze is `kummer674` under the
port cache; the audit is `verification/yamaguchi-port-kummer674-audit.log`.
Adding its 28 remaining leaves brings the public manifest to 831 modules.
The relocated checkpoint now passes 4,805 normal build jobs and the full
imported audit of 20,181 declarations, with exactly the standard three
axioms (`verification/yamaguchi-kummer-{build,audit}.log`).

The offline command `python3 scripts/check-yamaguchi-provenance.py` verifies
every current vendored hash, reverses the recorded Lean 4.35 import relocation
for `IwasawaIndexing`, then reverses local import relocation and the recorded
compatibility patch in a temporary directory, and checks every recovered
source against its pinned upstream hash. This provenance check is separate
from Lean builds and axiom audits.

Seven further checked local-Artin and unramified-reciprocity leaves support
the actual inertia/norm-index adapters. They bring the manifest to 838
modules. Their relocated normal build now passes (4,133 jobs), with a complete
imported audit of 8,774 declarations and only the standard three axioms
(`verification/local-artin-bridges-{build,axioms}.log`). The seven exact staged sources
are recorded in `verification/yamaguchi-local-artin7-public-stage.json`.

Four checked finite-quotient/profinite-integer/local-unramified H² leaves
support the actual absolute-inertia restriction adapters. The manifest has
842 modules; their relocated checks remain separate and pending. Exact
files are in `verification/yamaguchi-local-absolute4-public-stage.json`.

Fourteen checked finite-stage/continuous-Kummer cohomology leaves support
the actual maximal-group H² reduction. They bring the manifest to 856
modules; relocated checking is tracked through that reduction. The exact
addition is `verification/yamaguchi-finite-stage14-public-stage.json`.

The full 886-module finite-Kummer/global-Artin union now passes the isolated
Lean 4.32 check. Its transitive imported audit covers 25,791 declarations
and reports only `Quot.sound`, `Classical.choice`, and `propext`
(`verification/yamaguchi-port-cohomology886-audit.log`). The 798-module
global-Artin subclosure is separately frozen. A further 173 checked sources
bring the public manifest to 1,029. The relocated normal build now passes
4,988 jobs, and its complete imported audit checks all 25,791 declarations
with exactly the standard three axioms; see
`verification/yamaguchi-global-artin-{build,audit}.log`.
Exact changes are in `verification/yamaguchi-cohomology173-public-stage.json`;
the original source clone is unchanged.

The full 1,262-module absolute-kernel dependency union is now isolated-checked
and frozen (88 source files in the final manifest require compatibility
edits; `compatibility.patch` touches the same 88 files). The final 280
new sources bring the attributed public manifest to 1,309. Relocated normal
verification is queued; the offline provenance reversal passes all 1,309.
The actual unrestricted adapters `AbsoluteProPFactor`, `CentralLiftCorrection`,
and `ProTwoH2AbsoluteKernel` have also passed direct Lean checks and are
public. Their separate adaptation record is `absolute-kernel-adapters.json`
and its accompanying patch.

The final isolated 1,262-module imported audit covers 34,273 declarations
with exactly the standard three axioms; see
`verification/yamaguchi-port-absolute1262-audit.log`. The three new actual
absolute-kernel adapters additionally pass a scoped audit of 68 declarations
(`verification/absolute-kernel-direct-audit.log`).

The relocated 207-module detector extension and its three actual arithmetic
adapters now pass the normal build (4,873 jobs) and complete imported audit
(22,109 declarations, exactly the standard three axioms); see
`verification/complex-detector-{build,audit}.log`.
