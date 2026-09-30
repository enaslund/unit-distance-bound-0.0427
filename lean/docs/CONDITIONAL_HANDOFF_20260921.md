# Conditional submission handoff — September 21, 2026

**The source and review package are prepared. Fresh NanoDa acceptance and a
complete standard-profile pass remain outstanding.** Both new NanoDa attempts
were terminated by the host's `earlyoom` service during shared-host memory
pressure. Their failed results are preserved; this is not an official Palomar
report or an editorial acceptance.

## Artifacts

- [Source candidate](../dist/conditional-20260921/conditional-source-06.tar.gz),
  SHA-256 `b66d145655281f2088996e04697cfad04446cb4f0b368fa3272fb48b7c41e70b`.
- [Portable review evidence](../dist/conditional-20260921/conditional-review-07.tar.gz),
  SHA-256 `aba8048e9ef6e15f4d53b0c1965a7d1cc4e97af183285f92c072a4d0d1010a9e`.
- [Bundle integrity receipt](../verification/conditional-20260921/review-bundle-07.json)
  and [successful portable reproduction check](../verification/conditional-20260921/review-bundle-reproduction-07.json).

The source archive extracts to `unit-distance-zeta`, a standalone project with
2,217 files and the complete selected proof closure. Select
`comparator-zeta.json` and `formalization.yaml`. Its exact unpublished local
commit is `241260852846445f010be2edfaa313b4c2ed8d0c`, in
`.cache/conditional-20260921/review-source-06`;
[every Git blob and file mode was checked](../verification/conditional-20260921/git-tree-06.json).
Nothing was published or submitted.

## Mathematical scope

The sole displayed fixed-field zeta inequality in `ChallengeZeta.lean`, with
ceiling `0.042165819`, implies a sequence of finite sets in the ordinary complex
Euclidean plane whose cardinalities and unordered unit-pair counts divided by
`cardinality^(2083647/2000000)` both tend to infinity. The exponent is exactly
**1.0418235**. This is not a bound at every sufficiently large cardinality.

The nineteen-radical field is independently specified in the Mathlib-only
Challenge. Its degree `524288`, arithmetic family, discriminant bound, analytic
transfer and geometric construction are internal theorems. The numerical
inequality remains **unproved**, with no verified enclosure for its full
left-hand side. There is no additional GRH or tower-existence hypothesis.
The unrestricted unconditional goal remains open.

Read the [exact statement and proof map](CONDITIONAL_SUBMISSION.md),
[provenance](SUBMISSION_PROVENANCE.md), and
[scoped source review](../verification/conditional-20260921/MATHEMATICAL_REVIEW.md).
The manuscript is available locally, but public access to its cited GitHub
location could not be confirmed. Novelty is unknown. Earlier library and AI
contributions are credited. This preparation used one agent and launched no
other AI agents; no human proof review is claimed.

## Verification

| Check | Actual result |
| --- | --- |
| Final-source metadata, deterministic export, payload hashes, local intake and Git tree | Passed; receipts are in the [run ledger](../verification/conditional-20260921/README.md). The exact license detector accepted the unchanged Apache-2.0 license. |
| Fresh source build and canonical Challenge isolation | Completed across the original execution and its confined continuation, with authenticated public dependencies and repeated confinement probes. |
| Stock statement/axiom comparison, Lean kernel replay and quotient check | Passed in the continuation; [stage classification and integrity record](../verification/conditional-20260921/post-execution-integrity-05.json). |
| Complete fresh axiom and semantic audits | [Passed](../verification/conditional-20260921/fresh-audits-05.json): 52,219 project declarations and all 36 wrapper declarations use only `propext`, `Quot.sound`, and `Classical.choice`. Direct checks cover Euclidean coordinates, unordered counting, field degree, zeta-domain conditions and the sequence consequence. |
| New NanoDa checks | Both failed with exit 143: [stock continuation](../verification/conditional-20260921/continued-05b.json) and [four-thread supplemental retry](../verification/conditional-20260921/nanoda-parallel-05b.json). Host journals identify earlyoom as the sender in [both](../verification/conditional-20260921/earlyoom-diagnosis.json) [cases](../verification/conditional-20260921/earlyoom-parallel-diagnosis.json). |

The earlier accepted NanoDa export is
[byte-identical to the fresh Solution export](../verification/conditional-20260921/export-identity-05.json).
The [historical transfer check](../verification/conditional-20260921/historical-nanoda-transfer-05.json)
binds its actual acceptance receipt, log, guarded logical configuration and
identical checker binary. This remains separate evidence; it is not a new
standard-profile pass. No host service or unrelated job was changed.

Execution and fresh audits concern archive 05. Final archive 06 changes only
manuscript-availability provenance, associated prose and generated hash records.
[Exact identity checks](../verification/conditional-20260921/documentation-transfer-06.json)
cover all 2,165 Lean files and every verification/build/dependency configuration
file. Final metadata and intake were checked separately. A second full
compilation/replay of 06 was not performed.

## Remaining human review and verification

Review the independent Challenge, the substantial numerical assumption, proof
map and source attribution. Before treating this as a standard-profile pass,
rerun the pinned verifier on a host with adequate available memory and no
competing memory-intensive work. [Reproduction instructions](PALOMAR_REPRODUCE.md)
include public dependency pins and fresh work/report paths. The tested Landrun
build used Go `1.24.0` and `CGO_ENABLED=0`; include the exact Licensee check.

Public heads rechecked during this run were PalomarPolicy
`792c7c0b9e798bd02719e795ef11fa2b5929e067` and PalomarSubmission
`3561d237dcc4b28482558ad28a64d767d7cc8615`. Recheck current requirements before
publishing the exact reviewed source payload and requesting Palomar's own
mechanical and editorial reports. Publication, submission and registration
remain separate human actions. The requested fresh verification objective was
not fully achieved in this run.
