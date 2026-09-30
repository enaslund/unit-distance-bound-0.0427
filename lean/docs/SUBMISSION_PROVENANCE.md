# Provenance of the conditional submission

The source mathematics is Eric Naslund's *A lower exponent of 1.0418235 for
planar unit distances*, in the research repository at commit
`eec70fd25ebe045c5df1c98370d613eaa3719c0c`, under
`publication/unit-distance-1.0418235/`. This submission keeps its exact
sequence conclusion but explicitly assumes the fixed-field inequality (H).
The newer sufficient pair bound permits threshold `0.042165819`; the
manuscript's older threshold is `0.042161819`. The exponent is unchanged.

The manuscript is included in this package under `docs/manuscript/`. The
research repository it comes from was private as of 2026-09-22, so the
citation is an account of source provenance rather than of public
literature. The manuscript's title note says it was entirely written with
AI tools; it is an unrefereed preprint. No novelty, priority or
research-interest claim rests on it. The independent Challenge and the
submitted proof are the evidence for the conditional implication itself.

The development is source-based and extensively uses Mathlib. The following
substantive ports retain their original notices and Apache-2.0 licenses.
The paths under `third-party/` preserve upstream and local source hashes,
patches and scope notes; the verification records they reference are
shipped under `verification/` in this package. Such records attest only to
their recorded snapshots; the current package has its own receipts.

| Upstream and exact revision | Reuse and adaptation |
| --- | --- |
| [Mathlib](https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55) | Matched dependency for Lean `v4.35.0-rc2`; the full selected build passed for the exact source digest in the [September 24 receipt](../verification/conditional-20260924/accepted-selected-build-20260924.md). Archive and verifier results require separate receipts. Its own pinned dependencies remain external public dependencies. |
| [sum_product](https://github.com/mathlib-initiative/sum_product/tree/80e4127a67742659d521466204c6d2d7e0ca2b3f), Formal Frontier Team | Multidimensional Poisson summation in `ThirdParty/PoissonSummation.lean`; ideal-series and Euler helpers from `DedekindZeta/Statements.lean` in `DedekindEuler.lean`; selected trace-dual proofs from `DedekindZeta/Theta.lean` in `MinkowskiTrace.lean`. The ideal-counting port of `SumProduct/EulerBound.lean` (`IdealCounting.lean`) exists in the research repository but is not in this package's import closure and is not shipped. Local namespaces and Mathlib inertia-degree APIs are adapted. The local ideal-series identity is strengthened to `HasSum`; the full Euler-product assembly and Euclidean trace normalization are local developments. License: `third-party/sum_product/LICENSE`. |
| [AINTLIB](https://github.com/CBirkbeck/AINTLIB/tree/a302aeacd86053f9d5f991fbbf664e1cc1051d08), Chris Birkbeck | Completed Dedekind-zeta continuation, functional equation and explicit-formula foundations, ported to `Upstream/AINTLIB` (29 files in this package). Compatibility patches and extraction scope: `third-party/aintlib/`. Relative-Hecke entireness and the final numerical hypothesis are not supplied by this port. |
| [SawinTotallyRealTowers](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/tree/3a455e1aa9140dbbe7b7d68f508392a69c86d0f4), Naganori Yamaguchi | Profinite presentations, local algebra and continuous pro-p cohomology, relocated under `Upstream/Yamaguchi`. Of the 1,309 files in the port manifest, 1,287 are in this package's import closure and shipped; the 22 others are neither imported nor shipped. Original declaration namespaces are retained. The local import/API adaptations are recorded in `third-party/yamaguchi/`. New local arguments assemble the required complex pro-two relation bound and growing arithmetic family. |
| [erdos-unit-distance](https://github.com/logical-intelligence/erdos-unit-distance/tree/b6493074dd103ca32ea4f5e9b0bc9cb3a0379f2e), Erdős unit-distance formalization contributors | Selected `openNormalChain` and actual fixed-field construction proofs from `Internal/ClassFieldTheory/Witness.lean`, adapted in `ProfiniteQuotientTower` and `GaloisQuotientTower`. Records: `third-party/erdos-unit-distance/`. Its headline theorem and arithmetic hypotheses are not imported as assumptions. |
| [RiemannHypothesis-Formalization](https://github.com/alejandrozu/RiemannHypothesis-Formalization/tree/753938937e624d1c8bbe4c208517660a672d1b8e), Tristen Harr | Generic entire-function and Hadamard-product lemmas under `Upstream/Hadamard` (12 files in this package), plus selected pairing/divisor adaptations. Records: `third-party/entire-hadamard/`. No xi-specific result or Riemann Hypothesis assumption is used. |

Some preserved provenance manifests describe larger historical port slices
than the selected theorem imports. `SELECTION.json` is the authoritative
module list for this package (2,163 modules in the selected closure).
Omitted port files are not proof dependencies.

The proof development, scripts and exposition were produced with AI tools
under Eric Naslund's direction. Earlier runs used GPT-6 Astra and collaborating
GPT-5.6 Sol agents; their contributions are inherited, not attributed anew.
The September 21 conditional-preparation run used one GPT-6 Astra agent at
the user-requested Max reasoning setting and launched no other AI agents.

On 2026-09-22, Claude Fable 5.1 (Anthropic), running through Claude Code
with subagents under the owner's direction, audited the package against the
research repository and the public record, and edited the documentation,
the export script and the provenance records accordingly (including the
manuscript-availability statement, the sum_product and Yamaguchi rows above,
and the verification-record references). It changed no Lean proof text;
its only Lean edits are comments. It ran no Palomar verification and claims
no pass.

The September 24 continuation uses a GPT-6 Sol lead, one GPT-6 Astra Ultra
specialist, two GPT-6 Sol collaborators, and GPT-6 Luna collaborators under
Eric Naslund's direction. Their current work spans the Lean 4.35 migration,
provenance repair, policy checks and local package preparation. These are
AI-produced changes. The dated host bootstrap and archive-17 preparation
checks establish only their recorded scopes. A new selected build or current
verifier result must be read from its exact source or archive receipt;
neither proves H.

On September 27 a GPT-6 Sol lead, one GPT-6 Astra Ultra mathematics worker,
two GPT-6 Sol Ultra Lean workers, and GPT-6 Luna High research and review
workers continued the conditional development. They produced checkout-side
research drafts, independent source reviews, and a read-only package/policy
audit. Those new drafts are outside this package's selected proof closure;
their presence is not a Lean check or a proof of H. The team kept heavy jobs
queued while the separately owned candidate-20 verification reservation was
held. Candidate 20's exact fresh verifier attempt ended with resource
exhaustion after build and export, and no current full pass is claimed.

`formalization.yaml` records these stages. Eric Naslund is the directing
owner and responsible maintainer; this does not assert that he manually
wrote or reviewed the proofs. No human peer review or Palomar editorial
outcome is claimed. The root [NOTICE](../NOTICE) and [LICENSE](../LICENSE)
apply to the submitted source snapshot without changing upstream licenses.

The historical local receipts in this package used PalomarSubmission
`3561d237dcc4b28482558ad28a64d767d7cc8615`. On 2026-09-22 that repository's
`main` moved to `0b068c1f` (PRs #144 and #146:
a cgroup-v2 supervisor and bubblewrap confinement replacing systemd
transient units and the outer landrun); PR #147, open on that date, would
make the 16-CPU/32 GiB `palomar-namespace-16x32-v1` profile the default
with the same 19,800 s budget. PalomarPolicy
`792c7c0b9e798bd02719e795ef11fa2b5929e067` and the trusted tool pins were
unchanged. See [PALOMAR_REPRODUCE.md](PALOMAR_REPRODUCE.md).

On 2026-09-27, the public PalomarSubmission head was
[`a59f25bd8a66bf6faf3a4f4260d412989c0185ea`](https://github.com/PalomarRegistry/PalomarSubmission/tree/a59f25bd8a66bf6faf3a4f4260d412989c0185ea),
the policy revision used for the candidate23 archive-only metadata gate.
Its default execution profile is `palomar-namespace-16x32-v1`; the local
phase-aware verifier plan selects Standard. Candidate23 export and
archive-only metadata gate passed (archive SHA-256 `a8b47796a275a598e2be85c9f6d4e28b560782047b4b7d6e8ea6c5c3f3d7132d`), but no full verifier
run has been made for that archive. Candidate22's archive-only gate also
passed. Candidate21's preserved archive gate failed metadata because its
wrapper omitted the explicit revision. Candidate20's full verifier stopped
with comparator memory exhaustion; retry2 ended at 148,000/149,249 checks on a
host-memory guard stop, with no kernel verdict. The dated September 24
source-head account below remains historical.

The current PalomarSubmission source head rechecked on 2026-09-24 was
[`1703d7babd984ccc3831cdf89c28221abe34808f`](https://github.com/PalomarRegistry/PalomarSubmission/tree/1703d7babd984ccc3831cdf89c28221abe34808f),
which requires Lean `v4.35.0-rc2` or later. The selected source tree pins
Lean `v4.35.0-rc2` and
Mathlib commit [`065356127b1dc0016f66b7283ce0ce2c4055aa55`](https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55)
and passed a full selected build on the source digest in the
[accepted build record](../verification/conditional-20260924/accepted-selected-build-20260924.md).
Candidate export and current Palomar verification require separate
archive-bound receipts. This document claims no current
verifier pass or proof of H.
