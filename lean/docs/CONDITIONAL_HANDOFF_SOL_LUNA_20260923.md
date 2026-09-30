# Sol/Luna formalization handoff — September 23, 2026

This continuation began at 06:41 UTC and must stop by 14:41:17 UTC. Its exact
target is [GOAL.md](../GOAL.md). The selected theorem in
[ChallengeZeta.lean](../ChallengeZeta.lean) and
[SolutionZeta.lean](../SolutionZeta.lean) proves the planar sequence conclusion
with exponent `2083647/2000000 = 1.0418235` **conditional on the displayed
fixed-field zeta inequality (H)**. H is still unproved in Lean. No new
unconditional exponent, official Palomar report, remote submission or
registration is claimed.

## Stable starting checkpoint

The sealed [candidate 14](../dist/conditional-20260922/conditional-source-14.tar.gz)
has SHA-256 `4d4e657cbb557049b1d8281321941c1940053af40a2669d0435ed5388b500199`.
Its 2,165 Lean files and every proof input were byte-identical to archive 07,
which passed the complete **old pinned local** Palomar verifier in 11,378
seconds. Candidate 14 itself did not receive a full verifier replay. Its
deterministic export, metadata smoke, proof-input identity and 17 extracted
finite checks passed; the exact records are in the
[September 22 handoff](CONDITIONAL_HANDOFF_SOL_LUNA_20260922.md) and
[archive ledger](../verification/conditional-20260922/README.md).

PalomarSubmission at the candidate-14 smoke revision
`e48a86d0495356b5131a92c9406aa6e27cf99e56` requires Lean at least
`v4.35.0-rc2`. A public-head source recheck at `1703d7b` at 13:26 UTC on September 23
11:24 UTC found the same floor and rejection rule. Candidate 14 pins
`v4.32.0`, so preparation rejects its toolchain before compilation. Its
metadata passed the `e48a86d` parser. A later bounded candidate-15 smoke
also passed the `1703d7b` metadata parser and returned
`toolchain.unsupported`; it did not run intake or proof compilation.
See the [compatibility assessment](../verification/conditional-20260923/current-policy-compatibility.md),
[smoke result](../verification/conditional-20260923/current-policy-smoke-14.json),
and [migration assessment](../verification/conditional-20260923/toolchain-migration-assessment.md).
An isolated migration copy under `.cache/build-tmp/conditional14-v435-migration/`
is a diagnostic, not a checked candidate; the source edits are recorded in
[migration preparation](../verification/conditional-20260923/toolchain-migration-preparation.md).
The official `v4.35.0-rc2` toolchain was subsequently installed in a
workspace-local environment. Targeted pinned Mathlib cache retrieval and one
missing Mathlib artifact build enabled a guarded successful compile of the
patched `IwasawaIndexing` leaf. This checks the relocated Denumerable import
and that one module, not the selected Challenge/Solution closure or current
Palomar verification.

The newer sealed [candidate 15](../dist/conditional-20260923/conditional-source-15.tar.gz)
has SHA-256 `7585c6dcd7806503237142df9a8544561a08d2cb9291e684991981d6b6cf4632`.
Its selected Lean files and all other proof inputs are byte-identical to both
candidates 14 and verifier-passed 07. Deterministic check-only, pinned
metadata, and all 17 extracted finite-script checks passed. Extracted runs of
the new full-genus fixture and atom-formula checker also passed; those are
finite numerical checks with absent research Lean source pins reported
explicitly. The [candidate 15 record](../verification/conditional-20260923/candidate15-packaging-preparation.md)
lists the checks and receipts. A bounded current-policy check passed metadata
validation and then returned `toolchain.unsupported` for the same v4.32 pin;
there was no current-policy Lean build, verifier replay, or submission.

The subsequent sealed [candidate 16](../dist/conditional-20260923/conditional-source-16.tar.gz)
has SHA-256 `3bf000814f099995db227476caea0147211928386a19ccd8b9095eff8c15721b`.
It includes the later all-32 H6 expint and aggregate records and the finite
plus-quartic PARI check. Its deterministic check-only, exact proof-input
identity with verifier-passed archive 07, 17 extracted finite scripts, and
extracted full-genus/atom checks passed. A direct current-head metadata
smoke again returned `toolchain.unsupported` for the v4.32 pin. One unrun
quartic checker draft entered this archive through a broad research-script
glob; the [candidate 16 record](../verification/conditional-20260923/candidate16-packaging-preparation.md)
identifies its hash and excludes it from the checks. Candidate 16 received no
fresh selected-proof build, current-policy verifier pass, or submission.

## September 23 numerical evidence

The guarded [full-genus replay](../verification/sol-luna-20260923/genus-all-characters/REPORT.md)
passed once at 512-bit Arb precision. It reconstructed all 128 mask-derived
fundamental discriminants and primitive Conrey characters, checked all
677,376 values across their complete periods against a separate Kronecker
implementation, and freshly evaluated each primitive value and seven-prime
deletion. Every value and deleted logarithm fell strictly inside its
inherited dyadic row enclosure. Their total log sum is enclosed near
`7.3375781308465302206470681816905033421281`, strictly below the genus
allowance `7.337578130846530221`. The Python script, compact comparison
fixture, result and reviews are in that directory. The successful numerical
run was repeated after a portable-fixture script edit; the second full
128-row guarded run passed, verified the four pinned Lean source hashes and
the archived JSON against the compact fixture. Fixture-only execution from
extracted candidate 15 passed all 128 rows and 677,376 period values, while
explicitly recording that the four research Lean source pins were absent
from the package. The replay shares FLINT's
Dirichlet-L backend with the inherited computation. The **all-mask pointwise
Lean primitive-character to Kronecker/Conrey identification remains open**;
the [bridge review](../verification/sol-luna-20260923/genus-all-characters/lean-bridge-review.md)
and [attempt note](../verification/sol-luna-20260923/genus-all-characters/kronecker-bridge.md)
explain the exact gap. This numerical result therefore has not become a Lean
bound on the actual 128 coherent values.

A small [checked Lean arithmetic leaf](../verification/sol-luna-20260923/portable-aggregate-arithmetic.md)
proves that the copied aggregate dyadic numerator is strictly below the genus
allowance, with only the three standard axioms. It does not prove that the 128
fixture endpoints sum to this numerator, nor does it supply any actual-row
analytic bound. The complete portable row-table source remains uncompiled;
its [compile ledger](../verification/sol-luna-20260923/factor-inventory/portable-row-table-first-compile.md)
records six ordinary source failures and the latest offline repair.

A separate guarded [atom-formula check](../verification/sol-luna-20260923/genus-all-characters/genus_atom_bridge_check.md)
computed the explicit two-primary times five optional odd Legendre values
for all 128 masks and all 677,376 residue classes in their conductor
periods. Every value agreed with both a separate Kronecker routine and the
FLINT Conrey character. It ran in 4.261 seconds after three admission
deferrals and one admitted Python API-fix failure; the final run recorded
all 12 present source pins. This is finite evidence for the paper-level
assembly formula, not a Lean theorem or an independent analytic L backend.
The generic [pointwise product lemma](../verification/sol-luna-20260923/dirichlet-pointwise.md)
compiled under `-M2560` and passed its three-standard-axiom audit. The
lighter [all-mask atom expansion](../verification/sol-luna-20260923/primitive-atom-expansion-light.md)
also compiled and passed its focused audit with only `propext`,
`Classical.choice` and `Quot.sound`. It identifies the actual primitive
character with a product of lifted local primitive atoms for every integer,
including nonunits. The older root-number-heavy expansion draft is still
uncompiled. No generic atom-to-Kronecker/Conrey identification is proved;
the [scope note](../verification/sol-luna-20260923/primitive-atom-expansion.md)
describes that remaining step.

An [exact external finite-support replay](../verification/sol-luna-20260923/factor-inventory/finite-support-design.md)
then checked the first 387,955 listed complement primes, through
`163137359449`, in five guarded chunks. It independently rechecked
deterministic primality below `2^38`, the seven genus modular tests, 17
quadratic-algebra signs, seven completed and 12 retained parities, and the
per-bin floor-reciprocal receipts against 6,716 pinned Lean table rows. A
guarded aggregate computed the adjusted 387,955-prime rowwise lower saving
as the exact rational
`152066974999277949267719 / 4000000000000000000000000000`. Its exact
margin over the direct Lean threshold `3801674/10^11` is
`14999277949267719 / 4000000000000000000000000000 > 0`; it also exceeds
the post-refit requirement. This establishes a reproducible finite
calculation, not the 387,955 individual Lean prime/eligibility certificates
or their actual-field support theorem. The existing checked Lean support
still covers only 1,000 primes. A hardened V2 replay reran all five chunks
and the aggregate under the same shared guard. Its checker refuses `python -O`
and records source hash and assertion mode in each receipt; the exact saving
and margins matched the earlier run. The
[V2 aggregate](../verification/sol-luna-20260923/factor-inventory/finite-support-replay-v2-summary.json)
and [independent receipt review](../verification/sol-luna-20260923/factor-inventory/finite-support-independent-review.md)
record its provenance and external-computation limit.

Two guarded outward-Arb replays of the inherited direct-check scripts
recomputed one H6 quadratic AFE row and one H7 pure quartic AFE row strictly
below their printed allowances. The copied AFE scripts changed only their
relative research-root path, so these passes show repeatability of the prior
independent method, not a new analytic algorithm.
A third guarded replay reconstructed all 192,193 coefficients of an H7
mixed-quartic row, checked all 306 exact moment bins and directly summed its
2,255 nonzero terms. Its direct log upper
`-0.0198192193582759991782967947679641976` is below the frozen row upper
by about `4.24e-18`. This adds a finite-summation check, but shares the
pinned split kernel and Arb backend with the inherited evaluator.
An additional H6 mixed-quadratic twist `+1` pointwise replay passed its full
coefficient hash, 184 moment bins, and intermediate interval checks, but its
upper endpoint exceeded the frozen row upper by about `4.44e-26`. It is a
**failed strict row comparison**, not a contradiction between an upper and
a lower bound. Replacing that one row in the H6 low-degree aggregate with
the wider direct upper still passes the separate H6 cap by exact rational
arithmetic, with `8.9287764792885897e-24` slack at `σ = 6001/6000`. This
does not transfer to the five-family receipt at `σ = 12001/12000`. The
[diagnostic](../verification/sol-luna-20260923/numerical-audit/h6_mixed_quadratic_direct.json),
[replacement](../verification/sol-luna-20260923/numerical-audit/h6_aggregate_replacement.json),
[review](../verification/sol-luna-20260923/numerical-audit/h6-mixed-quadratic-direct-review.md),
and [cross-sigma audit](../verification/sol-luna-20260923/numerical-audit/h6-row-cross_sigma-transfer.md)
give exact scope. These files postdate candidate 15's seal.

A further [target-sigma H6 replay](../verification/sol-luna-20260923/numerical-audit/h6-target-sigma-direct-report.md)
evaluated that same mask-1586 twist-`+1` row directly at `σ = 12001/12000`,
bound all 3,922 coefficients, and matched all 184 exact moment bins. Its
direct log upper exceeds the frozen target-row endpoint by about
`4.44580659e-26`, so the strict row comparison is **FAIL**; the direct
interpolation debit also misses the frozen debit by about `1.50e-136`. The
separate [exact target aggregate replacement](../verification/sol-luna-20260923/numerical-audit/h6_target_aggregate_replacement.json)
is **PASS**: the larger endpoint leaves the fixed mixed-quadratic allowance
unchanged with about `9.19e-19` group-rounding slack, hence leaves the final
printed ceiling unchanged under its analytic assumptions. The row failures
remain failures and the factor identity, FE, global coefficient bound and H
remain unproved. This resolves the earlier cross-sigma substitution gap for
this one row, without rechecking the other 835 analytic factors.
A distinct guarded target-sigma replay using Arb generalized exponential
integrals then obtained a strict frozen-row **PASS** for this same H6 factor:
its log upper is `0.13334973905073891147460919318615529122`, below the
target by about `3.3570544381928877e-20`. It matched all 3,922 coefficient
entries and 184 bins; both AFE finite sums fit the target interpolation
enclosures, and an elementary all-`n` `d₂` tail was bounded conditionally.
This does not erase the SplitKernels method's recorded strict **FAIL**. The
new route shares Arb/FLINT, but derives different weights; an independent
formula review and independent source audit found no normalization or
interval-direction error. A new Lean rational leaf compiled and passed the
focused standard-axiom audit for the exact transcribed row comparison. The
analytic row identity, FE, Dirichlet series, contour growth, bad-factor list
and global coefficient bound are still assumptions. See the
[expint result report](../verification/sol-luna-20260923/numerical-audit/h6-target-sigma-expint-report.md),
[source audit](../verification/sol-luna-20260923/numerical-audit/h6-target-sigma-expint-source-audit.md),
and [Lean arithmetic check](../verification/sol-luna-20260923/numerical-audit/h6-target-expint-lean-arithmetic.md).
A separate [contour-growth source audit](../verification/sol-luna-20260923/numerical-audit/h6-contour-growth-source-audit.md)
locates the required theta reflection and strip-growth proof: the checked
Dirichlet-series/majorant source concerns twist `−1` at conductor `15015`,
while the numerical `+1` row at conductor `240240` still lacks its matching
actual factor bridge. Entireness and an FE by themselves do not justify the
Mellin contour shift.
The same reviewed expint method was then run on **all 32** mask-1586 H6
quadratic target rows under the guard. It reconstructed 164,712 coefficient
entries, checked each full vector hash and moment table, and evaluated 45,552
expint weights. All 32 frozen individual row comparisons and consistency
checks passed; the smallest row margin is about `2.0592384721174497e-20`.
The [batch receipt](../verification/sol-luna-20260923/numerical-audit/h6_all_quadratic_expint.json)
and [source review](../verification/sol-luna-20260923/numerical-audit/h6-all-quadratic-expint-source-review.md)
record the exact scope. The factor identities, FEs, contour bounds and global
coefficient bounds remain row-specific premises. The other analytic families
and the fixed-field H inequality remain open.
The [all-`n` coefficient-bound review](../verification/sol-luna-20260923/factor-inventory/artin-degree-two-coefficient-majorant.md)
found a useful exact distinction: Lean already proves the divisor-function
majorant for the source-defined mask-1586 twist-`-1` field quotient, including
ramified primes, but the numerical twist-`+1` row requires a separate
`B(√η)` extension and an all-prime local-factor match. Its finite vector hash
does not prove the global tail bound.
An exact Fraction substitution of **all 32** direct expint endpoints into
the target mixed-quadratic group passed, preserving the inherited sector's
outward rounding slack. The new group slack is about `2.557e-18`; the fixed
group allowance and final five-allowance upper remain unchanged. The
[aggregate result](../verification/sol-luna-20260923/numerical-audit/h6-target-batch-aggregate-report.md)
and [independent audit](../verification/sol-luna-20260923/numerical-audit/h6-target-batch-aggregate-independent-audit.md)
check only this conditional arithmetic, not the row premises or H.
A separate Mathlib-only Lean theorem now derives the global `d₂` majorant
from multiplicativity and all rational-prime-power coefficient bounds. Its
guarded compile and three focused axiom prints passed with only the standard
axioms; the [record](../verification/sol-luna-20260923/factor-inventory/multiplicative-prime-power-d2-bridge.md)
leaves those assumptions open for the actual plus row. A staged plus-field
Lean bridge and an [independent source review](../verification/sol-luna-20260923/factor-inventory/plus-field-bridge-independent-review.md)
identify the next field-to-factor step. Its one guarded compile exited 134
with a Lean interpreter memory exception before an artifact or valid axiom
audit; the [compile status](../verification/sol-luna-20260923/factor-inventory/plus-field-bridge-status.md)
records this exact failure.
The finite [p=17 residue calculation](../verification/sol-luna-20260923/factor-inventory/h6-plus-p17-residue-check.md)
explains the table's `(1−T)^2` entry but is not a Lean local-factor proof.
An exact guarded [PARI maximal-order check](../verification/sol-luna-20260923/factor-inventory/h6-plus-quartic-pari-status.md)
certified the plus quartic's field discriminant `8,408,400`, power-order
index `16`, and the relative Euler denominator quotients at all seven
listed rational primes. Each matches the H6 twist-`+1` table; an
[independent review](../verification/sol-luna-20260923/factor-inventory/plus-quartic-pari-independent-review.md)
checked the polynomial, quotient direction and finite factor values. This
finite check gives no all-prime row identity, functional equation, contour
growth, or global coefficient majorant.

An independent segmented traversal then replayed one H7 mixed-octic
mask-1824, twist-`+1` finite moment row. After a pilot exposed and fixed a
sector-mask versus twist-squareclass selector error, the guarded full run
passed all 544 bins through `N=360720360`, with 548,127 nonzero coefficients
counted and all 21 signed and absolute moments per bin matching the frozen
receipt. Its full run took 35.17 seconds and recorded source, input and
compiled-binary hashes; peak RSS was unavailable. This checks finite
coefficient accumulation for one row, not its AFE weights/tail, functional
equation, conductor proof, all-`n` coefficient bound, or H. See the
[full receipt](../verification/sol-luna-20260923/numerical-audit/h7_octic_segmented_direct.json),
[method note](../verification/sol-luna-20260923/numerical-audit/h7-octic-bounded-replay-feasibility.md),
and [independent review](../verification/sol-luna-20260923/numerical-audit/h7-octic-segmented-review.md).
The [numerical audit](../verification/sol-luna-20260923/numerical-audit/REPORT.md)
lists endpoints, hashes, required analytic row assumptions and limits. These
single-row checks do not establish the complete 836-row table or H. The
[selected-proof source review](../verification/sol-luna-20260923/independent-review.md)
and [external certificate bridge review](../verification/sol-luna-20260923/external-proof-review.md)
found no concrete mismatch within their scopes; they are AI source reviews,
not a fresh kernel replay.

## Research Lean work and next dependencies

The new research modules are outside the selected conditional proof closure.
Check each report for the exact theorem statement, source hash, guarded build
result and axiom status before relying on it. Pending builds must remain
labelled pending; a source-level argument is not a compiled proof.

- `ZetaLunaConductorSevenPrimitivePositiveRun20260923.lean`: combine actual
  coherent χ7 positivity and a positive seven-prime deletion factor to prove
  primitive χ7 positivity. A parser issue at the existential return was
  source-repaired; the next admitted `-M2560` compile exited 134 with a Lean
  interpreter memory exception before theorem diagnostics or an artifact.
  An admitted import-only probe with the exact four imports then exited 134
  with the same memory exception. This localizes the failure to that import
  closure under `-M2560`; the source is not checked. A smaller Euler-product
  import probe also exited 134 with the same exception. The χ7 final norm
  bound remains an unchecked source draft; the
  [χ7 report](../verification/sol-luna-20260923/chi7-norm.md) records the
  mathematical prefix/tail/deletion review and exact probe outcomes.
- `ZetaLunaGenusBroaderConductorFiveRun20260923.lean`: proposed actual χ5
  deleted-value bound `≤103/100`; numerical mask-8 value is about
  `1.0198070492`. Its conductor-five dependency artifact compiled, but the
  new bound's import-only probe hit the `-M2560` interpreter memory limit;
  the endpoint is uncompiled. A lighter direct periodic prefix/tail route
  avoiding the heavy Q5 import has a complete source draft. Its first
  guarded prefix check reached ordinary Lean proof errors, now under repair;
  no χ5 norm theorem has compiled. An independent source review found no
  mathematical counterexample to the proposed head/tail/deletion bounds;
  see the
  [χ5 report](../verification/sol-luna-20260923/genus-bounds.md).
- `DirichletCoprimeProductPointwise20260923.lean`: checked all-integer
  evaluation rule for product-level changes, including nonunits; the source
  compiled and its axiom audit reported only the three permitted axioms.
  It supplies one generic ingredient of the all-mask bridge.
- `GenusLunaPrimitiveAtomExpansion20260923.lean`: source-only draft using
  that lemma to express each actual primitive genus character as its
  two-primary value times five optional odd-prime values at every integer.
  It has not been compiled or audited, and it does not prove the subsequent
  Kronecker reciprocity formula.
- `GenusLunaPrimitiveAtomExpansionLight20260923.lean`: narrower two-import
  realization of the actual all-mask atom product at the intrinsic conductor.
  The guarded source compiled and its focused axiom audit returned only the
  three permitted axioms. This proves an all-integer primitive-character
  factorization, not explicit Legendre/Kronecker/Conrey values; see the
  [checked record](../verification/sol-luna-20260923/primitive-atom-expansion-light.md).
- `ZetaLunaRelativeBoundRun20260923.lean`: proposed norm `≥1` for each
  *aggregate genus-product local factor*, hence nonnegative total genus log
  and a relative-log upper bound by the actual completed imprimitive log.
  This does not assert that each individual character factor has norm `≥1`.
  An independent
  [source review](../verification/sol-luna-20260923/factor-inventory/review.md)
  found no counterexample. A further
  [local-factor review](../verification/sol-luna-20260923/factor-inventory/relative-genus-local-norm-review.md)
  checked the grouped genus denominator shape and distinguished it from the
  completed/genus relative quotient, whose local factor need not have norm
  `≥1`. Build and audit are pending.
- `ZetaSolGenusRowReceiptBridge20260923.lean`: exact rowwise interface from
  upper bounds on 128 *actual* coherent values to the genus allowance. The
  separately proved nonvanishing fact, row inequalities, and their summed
  strict bound are explicit premises to keep the import closure smaller.
  An earlier two-import compile exited 134 on Lean's interpreter memory
  limit; the source was split from the heavy nonvanishing import. After one
  admission deferral and one ordinary proof-script correction, the revised
  one-import source compiled under `-j1 -M2560`. All three public endpoints
  passed a separate audit with only `propext`, `Classical.choice`, and
  `Quot.sound`. The rowwise numerical premises remain open; see the
  [check queue](../verification/sol-luna-20260923/root-lean-checks.md).
- `ZetaSolRelativeAggregateBudget20260923.lean`: direct two-component
  completed-field budget interface. A genus bound at its printed allowance
  and an actual relative log bound at `-0.040875140862019542` suffice for
  the existing completed-field analytic estimate. Both numerical premises
  remain open. The guarded source compiled and all three focused axiom
  prints reported only the permitted standard axioms; see its
  [check record](../verification/sol-luna-20260923/relative-aggregate-budget.md).
- `ZetaLunaFactorInventoryRun20260923.lean`: reorganizes actual local/global
  genus and relative factor identities; build and audit are pending. It does
  not prove the Artin/Hecke row inventory or numerical bounds.
- `ZetaLunaRelativeInvariantFunctionsRun20260923.lean`: a small structural
  theorem identifies functions on `G ⧸ H` with functions on `G` constant on
  right `H`-cosets. Its guarded compile and focused standard-axiom audit
  passed; see the [receipt](../verification/sol-luna-20260923/factor-inventory/relative-invariant-functions-compile.md).
  It does not yet give an equivariant regular-representation equivalence,
  Frobenius local determinant, or 836-row inventory.
- `GenusLunaPortableRowTableRun20260923.lean` and its intrinsic-index budget
  bridge contain the exact 128 dyadic fixture endpoints and proposed sum
  certificate. Six guarded pure-table compiles reached ordinary Lean
  elaboration or proof errors, most recently a parenthesis/syntax issue in
  the eight-block final sum; the latest source repair is awaiting a check.
  No table artifact or audit
  exists yet. A separate Mathlib-only leaf checked the copied aggregate
  integer against the allowance, but not the 128-row sum. The actual
  coherent-row inequalities remain open even if this arithmetic layer passes.
- `GenusLunaOddAtomLegendreGeneric20260923.lean` proposes a generic prime
  quadratic character to Legendre-symbol identity and five common-level
  unit corollaries. Its guarded compile exited 134 at Lean's interpreter
  memory limit before an artifact or audit. The separate Mathlib-only base
  `GenusLunaOddAtomLegendreMathlib20260923.lean` now compiled and passed a
  focused standard-axiom audit; it proves the local cast quadratic character
  equals Mathlib's Legendre-symbol formula pointwise, including nonunits.
  See the [light check record](../verification/sol-luna-20260923/genus-all-characters/odd-atom-legendre-mathlib-scope.md).
  The new
  `GenusLunaPrimitiveDiscriminantCharacter20260923.lean` is a source-only
  all-mask unitized formula, with six local unit-case atom evaluations
  explicit as premises. The actual primitive all-mask to explicit
  Kronecker/Conrey bridge remains open.
- `H6TargetAggregateReplacementArithmetic20260923.lean` transcribes the
  target-sigma H6 direct and group rational endpoints into three exact
  arithmetic claims, retaining the strict row failure. Its guarded compile
  and focused axiom audit passed with only the standard three axioms. An
  [independent transcription review](../verification/sol-luna-20260923/numerical-audit/h6-target-lean-arithmetic-transcription-review.md)
  matched the exact rational inputs and receipt hashes; the
  [status note](../verification/sol-luna-20260923/numerical-audit/h6-target-lean-arithmetic.md)
  distinguishes that arithmetic from the external Arb/AFE assumptions.
- `H6TargetExpintRowArithmetic20260923.lean` proves the opposite exact row
  comparison for the distinct expint interval: its upper endpoint is below
  the frozen target row. Its guarded compile and focused axiom audit passed
  with only the standard three axioms. The
  [check record](../verification/sol-luna-20260923/numerical-audit/h6-target-expint-lean-arithmetic.md)
  and independent transcription review distinguish this rational proof from
  the conditional external expint calculation.
- `H6AllQuadraticExpintArithmetic20260923.lean` checks all 32 exact
  target-row rational endpoint comparisons separately and as a `Fin 32`
  aggregate. Its guarded compile and focused standard-axiom audit passed;
  the [check record](../verification/sol-luna-20260923/numerical-audit/h6-all-quadratic-lean-arithmetic.md)
  states the earlier ordinary import error and the external analytic scope.
- A Mathlib-only
  [two-eigenvalue coefficient lemma](../verification/sol-luna-20260923/factor-inventory/two-eigen-euler-coefficient-lemma.md)
  compiled and printed only the standard axioms. It proves the local
  `k+1` bound under eigenvalue norm hypotheses; the target twist-`+1`
  row-to-Euler-factor match and global all-`n` bound are still open. The
  [field-gap analysis](../verification/sol-luna-20260923/factor-inventory/h6-mask1586-plus-field-bridge-gap.md)
  locates the missing plus extension and all-prime identification.
- `ZetaLunaAnalyticFERun20260923.lean`: specializes the completed Dedekind
  zeta functional equation to the certificate point; build and audit are
  pending. It gives no numerical H estimate.
- `GenusLunaKroneckerBridgeRun20260923.lean`: source-level extraction of the
  existing all-mask actual-to-assembled character equality and the one χ13
  quadratic specialization. The generic Kronecker bridge is unfinished;
  build and audit are pending.

After those local checks, the main mathematical path is to identify the
actual relative factor with the 836 analytic rows, prove the row hypotheses
or replace them with another analytic bound, and finish the fixed-field H
inequality. The numerical genus result and one-factor proofs are useful
pieces but do not settle this path. The [assumption ledger](ASSUMPTIONS.md)
and [September 22 handoff](CONDITIONAL_HANDOFF_SOL_LUNA_20260922.md) give
earlier checked dependencies.

## Shared-host continuation policy

The [team work and resource ledger](../verification/sol-luna-20260923/TEAM_USAGE.md)
maps worker endpoints to checked, numerical and draft results. Per-worker
reasoning tokens and charges are unavailable; the goal-level usage snapshot
will be added at the final handoff.

The run has a 4 GiB cgroup maximum, 3 GiB high limit, no swap and a 150%
CPU quota. All costly Lean builds, exports, kernel checks and numerical runs
must use the master
`automation/lean-formalization/guarded_build.py` with the inherited
`LEAN_BUILD_LOCK_PATH=/tmp/lean-formalization-1000.build.lock` and
`LEAN_BUILD_*` thresholds, disk-backed TMPDIR and one expensive slot. Lean
checks use incremental pinned dependencies and `-j1 -M2560`. Exit 75 is a
resource deferral, not a theorem failure. Do not run an unrestricted full
build or monolithic verifier replay under this cap. Preserve all sealed
archives, receipts and unrelated working edits.

## Later H6 quartic checkpoint (12:50 UTC)

The H6 mask-1586 twist-`+1` row gained an independent exact finite check.
PARI maximal-order decompositions for `F=Q[x]/(x⁴−34x²+429)` and
`B=Q[x]/(x²+35)` match the pinned row at all 3,922 coefficients, using all
543 primes through 3922; both vectors hash to
`b9317cb66d83f606dbbeeecd2ad40f4e805afbfbda7bd04383b28b7e7f1e3489`.
All seven bad-prime denominator cross-products passed. The completed
[attempt-4 result](../verification/sol-luna-20260923/numerical-audit/h6_quartic_zeta_quotient_attempt4.json)
and [report](../verification/sol-luna-20260923/numerical-audit/h6-quartic-zeta-quotient-report.md)
pin the executed source and distinguish the later post-run GP version query:
the raw `gp -v` field is usage text. The provenance-corrected source at SHA
`1643a51379688ba6c1df0aee178f1759e16b8b4016e09c1394e648eabeee7905`
has not run; three guarded retries (attempts 5–7) returned exit 75 before
launch. The [independent receipt review](../verification/sol-luna-20260923/numerical-audit/h6_quartic_zeta_quotient-independent-review.md)
checks the finite logic and scope. The checker needs pinned sibling research
sources outside the extracted conditional package to regenerate its target
vector; the [all-32 plan](../verification/sol-luna-20260923/numerical-audit/h6-quartic-zeta-quotient-all32-plan.md)
records that portability limitation.

A [paper derivation](../verification/sol-luna-20260923/factor-inventory/h6-plus-all-prime-euler-and-analytic-data.md)
uses split/inert residue fields for every good prime and the seven exact
PARI factors to identify the code-defined plus-row Euler product with
`ζ_F/ζ_B` at all primes, subject to the pinned source and finite field-data
checks. It then derives the all-`n` `d₂` coefficient bound. Standard
quadratic Hecke theorems supply the completed factor, conductor `240240`,
gamma `[0,1]`, root number `+1`, entire continuation and strip growth on
paper. These arguments are **not** Lean proofs and do not identify this row
among the degree-16384 completed field's exact factors (inside the
degree-524288 retained field). The plus-field
Lean bridge and narrower degree core both exhausted the Lean interpreter
memory allocation (exit 134); the tiny corrected Mathlib polynomial
identity source remains uncompiled.

The [all-32 good-prime derivation](../verification/sol-luna-20260923/factor-inventory/h6-all32-good-prime-derivation.md)
matches the pinned twist rule for all 32 H6 quadratic rows outside the
common seven-prime set. The inherited H6 arithmetic JSON reports a PARI
`lfundiv` check of conductor, gamma, bad-seven factors and 10,000 exact
coefficients for each row (320,000 entries). A fresh
[source audit](../verification/sol-luna-20260923/numerical-audit/h6-all32-inherited-pari-audit.md)
confirms that stored receipt's code and six direct hashes; original raw GP
output, executable metadata and five transitive import pins are absent.
The later [guarded all-32 maximal-order replay](../verification/sol-luna-20260923/factor-inventory/h6-all32-quartic-zeta-quotient-status.md)
uses a distinct direct method with stronger run provenance, matching
164,712 coefficients and 224 exceptional cross-products. Its row-specific
cutoffs are shorter than the inherited 10,000-prefix claim.
The [all-32 relative Hecke corollary](../verification/sol-luna-20260923/factor-inventory/h6-all32-relative-hecke-corollary.md)
records exactly what the standard analytic theorems and local coefficient
bounds would provide for those 32 rows if the historical bad-prime and
field-data receipt is accepted. It is paper-level work outside the
selected package proof closure.
The [symbolic p=17 check](../verification/sol-luna-20260923/factor-inventory/h6-all32-p17-symbolic.md)
also proves the relative local denominator `(1−(D/17)T)²` for each twist
and compares it with all 32 pinned table entries.
The [p=7 local calculation](../verification/sol-luna-20260923/factor-inventory/h6-all32-p7-local.md)
handles the ramified quadratic base prime for all 32 twists:
`E_{D,7}(T)=1+(D/7)T`, again matching every pinned entry by exact
source-level arithmetic. The five remaining exceptional primes now have
source-level calculations: [2 and 5](../verification/sol-luna-20260923/factor-inventory/h6-all32-p2-p5-symbolic.md)
and [3, 11, 13](../verification/sol-luna-20260923/factor-inventory/h6-all32-p3-p11-p13-symbolic.md).
Together the seven notes derive the pinned local denominators for every
twist and compare all 224 entries. These are paper-level arguments and
finite table checks, not Lean theorems.

Candidate 17 was sealed under the guard at 13:11 UTC: SHA-256
`3e369cb1cdc367fbb396946b9b69c1898a99d69cbb534b9b0d5ebe8cc29f1672`,
7,226,450 bytes, 2,498 files, 261 referenced records and no missing
references. It includes the corrected one-row checker and completed
attempt-4 receipt, the plus-row paper derivation, and the generic all-32
good-prime and inherited-receipt notes. The all-32 Hecke corollary and
symbolic p=17 note above were checkout-side additions after source selection.
The guarded post-export pipeline passed: deterministic archive and metadata,
selected-proof-input identity against archives 07 and 14, all 17 extracted
finite scripts, and both extracted 128-mask genus/atom checks. Its direct
current-head policy smoke returned `toolchain.unsupported` at the Lean
`v4.35.0-rc2` floor. The [candidate 17 record](../verification/conditional-20260923/candidate17-packaging-preparation.md)
lists each receipt and its scope. Candidate 17 is the latest locally
package-checked archive. No new full verifier run occurred. The separate
all-32 maximal-order checker remains outside candidate 17's broad
research-script glob; its guarded second attempt passed after a first GP
syntax failure. The [checkout-side direct replay](../verification/sol-luna-20260923/factor-inventory/h6_all32_quartic_zeta_quotient.json)
matches 164,712 finite coefficients across 32 rows and all 224 bad-prime
cross-products. It is finite numerical evidence, not an all-prime identity or
analytic proof.
Continue with the master guarded helper; do not relax host/cgroup
thresholds. The post-export pipeline checks deterministic seal, proof-input
identity against archive 07, current-head metadata/toolchain policy,
17 extracted finite scripts and both extracted genus checks. Current public
policy still rejects Lean v4.32.0 before proof compilation.

## Later paper conductor and field-placement checkpoint (13:50 UTC)

The [all-32 conductor derivation](../verification/sol-luna-20260923/factor-inventory/h6-all32-conductor-paper-derivation.md)
uses the paper local field cases to derive relative discriminant norm
`429·4^e` with dyadic exponent `e=0,2,3`; the rational degree-two
conductor is `Q_D=35·429·4^e`, matching the 32 pinned row values. The
factor 35 is essential: the norm of the relative conductor ideal alone is
`|disc(K_D)|/35²`, while the rational quotient conductor is
`|disc(K_D)|/35`. This normalization was corrected in the plus-row and
all-32 analytic notes and the independent analytic audit. The derivation
checks the dyadic local order index on paper; it is not a Lean theorem.
A direct all-32 discriminant checker was staged but has no successful
result: an admitted GP API draft failed before comparison, and corrected
retries returned guard exit 75 before launch. Its
[status](../verification/sol-luna-20260923/factor-inventory/h6-all32-discriminant-status.md)
preserves the attempts. The historical `lfunparams` conductor receipt
remains separate, with its known provenance limits.

The [completed-field placement audit](../verification/sol-luna-20260923/factor-inventory/h6-all32-completed-field-placement.md)
corrects a naming ambiguity: `CanonicalRetained.Carrier` has degree 524288,
whereas `ArithmeticCompleted.CompletedField` has degree 16384 and embeds in
that retained field. The source tables suggest a specific squareclass map:
`η=17+2√−35` differs by a genus-field square from retained word 512,
which in turn has a completed-word XOR decomposition. All listed twists
`D` are genus-field squareclasses. This is a concrete route to place the
32 quartics in the completed field, but the Lean root maps and aggregate
relative-factor decomposition have not been built. A small new
`H6SquareclassCrossIdentity20260923.lean` isolates the cross-multiplied
algebraic identity; its [guarded check](../verification/sol-luna-20260923/factor-inventory/h6-squareclass-cross-identity-status.md)
returned exit 75 before Lean started, so it remains a draft.

The concise [final handoff](FINAL_HANDOFF_SOL_LUNA_20260923.md) should be
read first when resuming. This detailed record retains the earlier attempt
history and exact source boundaries.
