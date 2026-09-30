# Candidate 14 compatibility with current Palomar intake

**Later public-head recheck, 2026-09-23 11:24 UTC.**
`git ls-remote` and a fresh shallow checkout found PalomarSubmission `main`
at `1703d7babd984ccc3831cdf89c28221abe34808f` (merge of PR #151).
Its `toolchains.json` still sets the minimum to `v4.35.0-rc2`, and
`scripts/verify_submission.py:176–207` still raises
`toolchain.unsupported` below that floor. Thus the candidate's `v4.32.0`
pin remains a preparation blocker at this later head. A bounded
[candidate-15 current-head smoke](current-policy-smoke-15-head1703.json)
subsequently passed the new metadata parser and returned precisely
`toolchain.unsupported`; it did not run intake or compilation. The original
candidate-14 and -15 smoke receipts below used the earlier `e48a86d`.
The [smoke driver](current-policy-smoke.py) records archive and policy hashes
and calls only the current metadata parser and toolchain-floor function.
The current-head source is
[toolchains.json](https://github.com/PalomarRegistry/PalomarSubmission/blob/1703d7babd984ccc3831cdf89c28221abe34808f/toolchains.json)
and [supported_toolchain](https://github.com/PalomarRegistry/PalomarSubmission/blob/1703d7babd984ccc3831cdf89c28221abe34808f/scripts/verify_submission.py#L176-L207).

Assessment against PalomarSubmission `main` at
`e48a86d0495356b5131a92c9406aa6e27cf99e56` (the same commit recorded in
[`current-policy-smoke-14.json`](current-policy-smoke-14.json)). This is a
read-only source and metadata review. No current intake, Lean build, proof
replay, or registration was run.

## Finding

Candidate 14's metadata passes the current formalization metadata contract,
but candidate 14 is **not ready for current intake as-is**. Its project
toolchain is Lean `v4.32.0`; current Palomar requires at least
`v4.35.0-rc2`. The current `supported_toolchain` function rejects a version
below that floor with `toolchain.unsupported` ([`verify_submission.py:176-206`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/scripts/verify_submission.py#L176-L206)). The current policy file records the floor explicitly ([`toolchains.json:1-4`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/toolchains.json#L1-L4)); the candidate pins v4.32.0 in both the project toolchain file and its hydrated Mathlib checkout ([`lean-toolchain:1`](../../lean-toolchain), [Mathlib `lean-toolchain:1`](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/lean-toolchain)).

Version ordering is explicit: release candidates sort before the release
they precede, but v4.32.0 is still below v4.35.0-rc2 ([`verify_submission.py:132-158`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/scripts/verify_submission.py#L132-L158)). The candidate's toolchain reaches this check through `toolchain_commit` ([`verify_submission.py:251-259`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/scripts/verify_submission.py#L251-L259)). During preparation, intake reads the project or repository `lean-toolchain` and calls that function ([`verify_submission.py:1405-1425`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/scripts/verify_submission.py#L1405-L1425)). Any preparation issue produces a failed preflight report and sets `ready=false` ([`verify_submission.py:1469-1484`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/scripts/verify_submission.py#L1469-L1484)). Full mode only proceeds to toolchain installation and proof steps if preparation is ready ([`submission.yml:164-179`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/.github/workflows/submission.yml#L164-L179), [`submission.yml:201-218`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/.github/workflows/submission.yml#L201-L218)). Thus the current intake floor is a blocker before Challenge/Solution compilation.

The current-policy smoke records that candidate 14 passes
`load_formalization_metadata`; it explicitly did not run current intake, proof
compilation, Comparator, kernel replay, or Palomar registration
([`current-policy-smoke-14.json:1-38`](current-policy-smoke-14.json)). The
same record shows the formalization profile is unchanged, while the toolchain,
execution, and verification profile files differ from the previously pinned
policy ([`current-policy-smoke-14.json:14-34`](current-policy-smoke-14.json)).
So the metadata pass is useful and narrow: it does not establish current
toolchain compatibility or full policy compatibility.

The smoke also records a changed execution and verification profile: current
defaults are 19,800 seconds, 350 minutes, and 30,064,710,272 minimum host
memory bytes, under `palomar-namespace-16x32-v1` ([`current-policy-smoke-14.json:6-18`](current-policy-smoke-14.json)). No current capacity check was run, so this review does not predict whether a full candidate build fits that runner profile.

## Migration and grandfathering

There is a bounded, non-build **preflight mode**: current Palomar's `preflight`
and `full` modes both call `verify_submission.py prepare`; full mode starts the
expensive steps only after preparation succeeds ([`README.md:75-83`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/README.md#L75-L83)). A current preflight on the unchanged candidate should report the toolchain floor issue without entering the proof build. This is a safe diagnostic route, not a compatibility exception.

No toolchain grandfathering path appears in the current intake code. The
optional `existing_id` is checked for shape and recorded, while
`supported_toolchain` is applied unconditionally to the candidate toolchain
([`verify_submission.py:1191-1195`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/scripts/verify_submission.py#L1191-L1195), [`verify_submission.py:1409-1425`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/scripts/verify_submission.py#L1409-L1425)). The exceptional registry-correction mode is narrower: its permitted changed fields are title, abstract, authors, classifications, and provenance; `lean-toolchain` is not among them ([`submission_contract.py:130-139`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/scripts/submission_contract.py#L130-L139)). The guided repair fields likewise concern formalization metadata, not the Lean toolchain ([`submission_contract.py:56-70`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/scripts/submission_contract.py#L56-L70)).

The practical migration route is a new source revision that selects at least
v4.35.0-rc2 and pins a Mathlib revision built with that same Lean version.
Current verification checks the submitted project toolchain against the
authenticated Mathlib checkout and requests that both the toolchain and
pinned Mathlib revision be aligned, with `lake-manifest.json` regenerated
([`verify_submission.py:2065-2088`](https://github.com/PalomarRegistry/PalomarSubmission/blob/e48a86d0495356b5131a92c9406aa6e27cf99e56/scripts/verify_submission.py#L2065-L2088)). Candidate 14 currently pins Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997` in both `lakefile.toml` and `lake-manifest.json` ([`lakefile.toml:8`](../../lakefile.toml), [`lake-manifest.json:10`](../../lake-manifest.json)); its hydrated Mathlib tree also selects v4.32.0. Therefore changing only the root `lean-toolchain` cannot satisfy the later dependency check. The source must be migrated and checked under the newer compiler and corresponding dependency revision; no source/API compatibility result is inferred here.

**Recommendation:** keep candidate 14 marked metadata-compatible only. If pursuing the current Palomar path, first use its current pinned `preflight` as a low-cost diagnostic. For actual submission, prepare a new commit with a matched v4.35-or-later toolchain and Mathlib pin, regenerate the manifest, then check compiler/API compatibility before considering the full verification run. No evidence supports a grandfathered v4.32 route.

## Scope and provenance

- Current verifier source: PalomarSubmission main `e48a86d0495356b5131a92c9406aa6e27cf99e56`.
- Candidate identity: archive SHA-256 `4d4e657cbb557049b1d8281321941c1940053af40a2669d0435ed5388b500199`.
- Metadata evidence: `candidate14_metadata_contract_passed: true`, checked at `2026-09-23T06:59:09.890288+00:00`.
- Constraint: no Lean/toolchain/manifest modification and no expensive build or verifier run.
