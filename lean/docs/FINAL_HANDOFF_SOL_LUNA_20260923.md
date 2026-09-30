# Final Sol/Luna handoff — 23 September 2026

**Post-run status:** this handoff was saved before a model-capacity error
ended the run at 14:04 UTC, about 37 minutes before its deadline. Candidate
18's export did not complete; candidate 17 remains the latest sealed archive.
The [post-run assessment and next steps](SOL_LUNA_EIGHT_HOUR_ASSESSMENT_20260923.md)
distinguish this run's new results from inherited work and give the current
conditional-submission blocker. The host limits below describe this run.

This is the short entry point for the eight-hour run. The detailed running
[handoff](CONDITIONAL_HANDOFF_SOL_LUNA_20260923.md), [assumption ledger](ASSUMPTIONS.md),
and [exact goal](../GOAL.md) retain the mathematical and receipt details.
No remote publication or Palomar registration occurred.

## Locally prepared conditional candidate

The latest sealed source archive is
[`conditional-source-17.tar.gz`](../dist/conditional-20260923/conditional-source-17.tar.gz),
SHA-256 `3e369cb1cdc367fbb396946b9b69c1898a99d69cbb534b9b0d5ebe8cc29f1672`
(7,226,450 bytes). The [candidate record](../verification/conditional-20260923/candidate17-packaging-preparation.md)
contains export and post-export receipts. The guarded post-export pipeline
passed deterministic archive/snapshot and metadata checks, exact selected
proof-input comparisons with archive 07 and 14, all 17 extracted finite
scripts, and both extracted 128-mask genus/atom finite checks. The selected
Lean/proof inputs are byte-identical to archive 07, which passed a full
*old-pinned local verifier* run. Candidate 17 received no new full verifier
replay. The independent [final receipt audit](../verification/sol-luna-20260923/independent-final-audit.md)
checked hashes, scopes and the archive boundary. Post-export receipts and
this handoff are checkout-side; they are not members of the sealed archive.
The [candidate 17 post-seal errata](../verification/conditional-20260923/candidate17-postseal-errata.md)
correct supporting analytic-prose normalization and field naming inside
the immutable archive. Its exact H statement and selected proof inputs are
unchanged. Use the corrected checkout notes for mathematical review.

The selected [SolutionZeta](../SolutionZeta.lean) proves the sequence
unit-distance exponent exactly `2083647/2000000 = 1.0418235` from one
explicit scalar zeta inequality **H** for an independently defined degree
524288 field. H is unproved in Lean. The [assumption ledger](ASSUMPTIONS.md)
displays its exact formula and distinguishes finite evidence from proof.
The research modules added in this run are outside the selected proof closure.
The checked proof dependencies on the inherited selected closure are only
`propext`, `Quot.sound`, and `Classical.choice`; archive 17 relies on exact
input identity with the prior old-pinned verifier pass for that claim.

Current public PalomarSubmission head
`1703d7babd984ccc3831cdf89c28221abe34808f` was rechecked at 13:26 UTC.
Its minimum Lean version is `v4.35.0-rc2`; candidate 17 pins `v4.32.0`.
The [direct head smoke](../verification/conditional-20260923/current-policy-smoke-17-head1703.json)
passed metadata validation then returned `toolchain.unsupported` before
intake, proof compilation, comparator, or kernel replay. A matched
Lean/Mathlib migration and full current-policy verifier run remain necessary
for a current Palomar submission.

## New evidence for H

The 32 mask-1586 H6 quadratic rows passed a guarded direct maximal-order
PARI replay after one GP syntax failure. The corrected run matched **164,712**
finite coefficients, all 32 complete vector hashes, and **224/224** bad-prime
factor cross-products using 21,520 quartic and 991 shared-base prime
ideal decompositions. The [status](../verification/sol-luna-20260923/factor-inventory/h6-all32-quartic-zeta-quotient-status.md),
[raw receipt](../verification/sol-luna-20260923/factor-inventory/h6_all32_quartic_zeta_quotient.json),
and [independent audit](../verification/sol-luna-20260923/independent-final-audit.md)
give the source, tool and input hashes. This check ran after candidate 17
was sealed; the checker and 9 MB raw receipt are **not** in that archive.
The separate plus-row attempt-4 result (3,922 coefficients and seven factors)
*is* included in candidate 17 and has its own [report](../verification/sol-luna-20260923/numerical-audit/h6-quartic-zeta-quotient-report.md).

A [paper derivation](../verification/sol-luna-20260923/factor-inventory/h6-all32-good-prime-derivation.md)
handles every good-prime H6 twist factor, and the [plus-row derivation](../verification/sol-luna-20260923/factor-inventory/h6-plus-all-prime-euler-and-analytic-data.md)
combines that with exact finite exceptional factors for the `D=1` row.
The direct all-32 replay checks every exceptional factor at the seven
listed primes. Separate source-level notes now derive the local denominator
rules for all seven primes and compare them with all 224 pinned entries;
they are paper calculations, not Lean proofs. Exact completed-field factor
placement remains open. Standard relative Hecke consequences
(entireness, FE, analytic conductor, growth and all-`n` divisor bound) are
paper-level theorem invocations under field/discriminant identification;
see the [analytic audit](../verification/sol-luna-20260923/factor-inventory/h6-all32-analytic-independent-audit.md).
No analytic factor or AFE tail was proved in Lean by this finite check.
The [completed-field placement audit](../verification/sol-luna-20260923/factor-inventory/h6-all32-completed-field-placement.md)
distinguishes the degree-16384 completed field from the degree-524288
retained field and gives a concrete source-level squareclass route for all
32 H6 quartics: the H6 radicand differs by a genus-field square from
retained word 512, which has a proposed completed-word decomposition.
The requisite Lean root map and 32-factor decomposition do not yet exist.
An additional [paper conductor derivation](../verification/sol-luna-20260923/factor-inventory/h6-all32-conductor-paper-derivation.md)
uses the local quadratic extensions to get relative discriminant norm
`429·4^e` with dyadic exponent `e=0,2,3`. The rational degree-two
conductors are `35·429·4^e`, matching all 32 pinned values
`15015,240240,960960`. This is source-level mathematics with an exact
table comparison, not a Lean proof. A separate fresh PARI discriminant
checker was prepared but its admitted first version had GP API errors and
corrected retries were deferred by the shared guard; it has no successful
discriminant receipt.

Separately, guarded Arb replays passed the expint enclosure for all 32 rows
under their analytic and all-`n` coefficient premises. A checked Lean leaf
verified the exact rational endpoints, and a Fraction aggregate replacement
retained the final ceiling `0.04216181893948094953138458`, below H's
`0.042165819` threshold. These are conditional numerical/endpoint results;
see the [batch report](../verification/sol-luna-20260923/numerical-audit/h6-all-quadratic-expint-report.md)
and [assumption ledger](ASSUMPTIONS.md). They neither establish the other
factor families nor prove H.

Other checked research advances include a conductor-13 actual Euler bound,
relative product and coherent-genus lemmas, a generic multiplicative
`d₂` bridge, and a full 128-mask finite genus replay. The detailed handoff
lists their exact compiled sources, audits, and limits. χ7/χ5 integration,
the full 128-row Lean table, and the plus-field Lean bridge remain incomplete;
some guarded compilations exited with Lean interpreter memory error 134 and
others had ordinary source errors or resource deferral 75. Treat uncompiled
sources as drafts.

## Resume order and host policy

1. Formalize the paper-level all-prime H6 family local identities and
   relative discriminant derivation, then connect the Hecke quotients to exact
   factors of the degree-16384 completed field inside the degree-524288 retained
   field. Apply the AFE with proved growth and tails.
2. Finish the remaining H7/mixed and genus factors, χ7/χ5 integration, and
   certified aggregate/finite-prime savings needed to prove H in Lean.
3. Migrate the selected proof closure to a supported Lean/Mathlib pair and
   run the current Palomar verifier on a locally sealed candidate. Keep the
   exact hypothesis statement and proof-input identity records visible.

All descendants must use the master
`automation/lean-formalization/guarded_build.py` for expensive Lean,
export, kernel or numerical work, with the inherited lock and memory policy:
4 GiB cgroup max, 3 GiB high, CPU 150%, no swap, host admission at least
10 GiB available and 1 GiB cgroup headroom; stop below 6 GiB/512 MiB.
Lean checks should be incremental with `-j1 -M2560` and the inherited
disk-backed TMPDIR. Exit 75 is a resource deferral, not a proof failure.
Preserve sealed archives, prior receipts, and unrelated edits. The
[team usage record](../verification/sol-luna-20260923/TEAM_USAGE.md)
records available usage and check outcomes.
