# Arithmetic cleanup — 2026-09-21

Eight Lean files were changed. The pre-edit sources and hashes are preserved
in [before/](before/) and [before-source-hashes.json](before-source-hashes.json).
[source-review.json](source-review.json) records the current hashes and a
textual check that all 109 existing public theorem/definition signatures were
retained. The Lean source changes remove 191 lines in total.

- `CentralCensusIntegerReciprocalAstra` now supplies certificate routing and
  integer-receipt addition for unions. The data-bearing `Certificate` is
  routed by a decidable membership split. Receipt addition separately requires
  disjointness.
- `CentralCensusActualSupport1000Run20260920b` reuses those helpers for its nine
  assembly stages. The prime data, finite checks, endpoints, cardinalities,
  and reciprocal numerators are unchanged.
- `GenusDirichletRootNumberSignHelpersRun20260920b` exposes the shared complex
  half-power/square-root normalization. The existing public names in
  `GenusDirichletGaussCoprimeRun20260920b` are preserved as theorem wrappers.
  The conductor 3, 5, and 7 modules use the sign helpers and the older general
  `primeQuadraticCharacter_isQuadratic` theorem directly.
- `CentralCensusActualSupport1000SharperBudgetRun20260920b` now rewrites the
  support's sum of quotients as a quotient of a sum before adding the
  order-four bound. This repairs the previously unvalidated conditional
  endpoint without changing its hypothesis or conclusion.

The maintained generator is
[generate-central-support-aggregate.py](../../../scripts/generate-central-support-aggregate.py).
It generates only the aggregate, using the twenty existing Lean block-source
and summary files. It supports `--check` and `--output-dir`; both the ordinary
check and generation into a separate directory reproduced the current source.
The historical generators, manifests, and numerical data remain preserved.
[generator-bindings.json](generator-bindings.json) records the generator,
aggregate, historical generator, and all input hashes.

From `lean-formalization`, reproducibility and compilation use:

```sh
python3 scripts/generate-central-support-aggregate.py --check
python3 verification/cleanup-20260921/arithmetic/check.py MODULE_NAME
```

The compilation runner checks the recorded configuration and compiler hashes,
sets `LEAN_NUM_THREADS=1`, and invokes the pinned Lean directly with `-j1` and
`-DElab.async=false`. It uses the shared
`.cache/cleanup-20260921/analytic` overlay, preserving the original project
artifacts and making both cleanups available to the integration consumer.
Each attempt has a source snapshot, log, and receipt with the command, hashes,
elapsed time, and exit status. [results.json](results.json) indexes all twenty
attempts: fourteen module compilations and three audit compilations succeeded;
three initial failed attempts are retained.

Every edited module passed. The checked consumers include the actual census
indices/defect consequence, the conductor 11/13 and two-primary Gauss atoms,
the datum composition, all 128 actual genus root numbers, and the combined
`GenusAnalyticConsumersCoreRun20260920b`. The repaired sharper-budget module
and its conditional `Target` endpoint also passed.

| Audit | Owned declarations | Result |
| --- | ---: | --- |
| [CensusAudit.lean](CensusAudit.lean) | 89 | permitted axiom closure |
| [GenusAudit.lean](GenusAudit.lean) | 393 | permitted axiom closure |
| [SharperBudgetAudit.lean](SharperBudgetAudit.lean) | 11 | permitted axiom closure |

All 493 owned declarations, including private auxiliaries, have transitive
axiom closures contained in `propext`, `Classical.choice`, and `Quot.sound`.
The public census, genus-root, and conditional-target endpoints were printed
separately. These are direct Lean source and axiom checks; independent kernel
replay remains a separate verification step.

The original census audit source used partial final name components such as
`UnitDistance.CentralCensusActualSupport1000`. Lean's `Name.isPrefixOf` compares
whole components, so that selector does not match
`UnitDistance.CentralCensusActualSupport1000Run20260920b`. The historical report
correctly says its full ownership audit was not run. The new audit uses exact
module names and the shared audit helper now rejects empty selections.

The extra mixed-character consumer attempt first encountered the absent
`Mixed1586JacobiThetaReflectionRun20260920b.olean`. Checking that unchanged
source exposed missing namespace qualifications for `primeQuadraticCharacter`
and `normalizedEvenCoefficientTheta`, together with an unsolved zero-value
side condition. Its failed source check is retained as
[Mixed1586JacobiThetaReflectionRun20260920b-01.log](Mixed1586JacobiThetaReflectionRun20260920b-01.log).
This arithmetic receipt makes no pass claim for that mixed consumer; its repair
belongs to the separate mixed-character cleanup.

The mathematical conclusions retain their original scope. The census proves
membership, cardinality, range, and reciprocal/saving lower bounds for a
selected 1,000-prime support. No census completeness theorem was added. The
normalized actual Euler-defect saving is `2231824 / 10^11`. The genus result
proves positive root numbers for all 128 primitive characters using exact
finite signs, CRT composition, and conductor/lift identification. The sharper
target theorem still assumes the completed-field imprimitive value is at most
`42965707 / 10^11`; that analytic inequality remains an input.
