# Conditional planar unit-distance theorem

This locally prepared candidate proves an implication from one specified
numerical inequality to an ordinary planar unit-distance sequence theorem.
The inequality remains unproved. The proposed result is the implication
itself.

**September 28 migration:** the selected working sources now use Lean's module
system. The reversible header-repair layers under
`third-party/module-system-20260928/` record explicit Mathlib imports,
targeted `import all` declarations that restore private instances, and the
pinned `backward.proofsInPublic` option for legacy proof elaboration. These
header edits retain the existing proof bodies and add no axioms. Repairs 05
and 08 replace one simplifier-based commutativity step in each of
`ThetaFirstIdentity` and `DirectThetaFirstIdentity` with
an explicit application of `mul_comm`, preserving both theorem statements and
assumptions. Repair 12 supplies Mathlib's existing `krullTopology_t2` theorem
directly for the unchanged Hausdorff-instance statement. Repair 22 replaces the
tensor-induction proof of the unchanged adele-embedding composition theorem
with Mathlib's `Algebra.TensorProduct.map_id_comp`. Repair 38 is the fifth
proof-code repair: it supplies `krullTopology_t2` as a local, Prop-valued
Hausdorff instance in `ideleClassComponentQuotientEquivMaximalAbelianGalois`,
preserving its declaration type and underlying equivalence. All repaired modules
pass isolated compiler checks. Source gates
and exact source-recovery checks are recorded separately from compilation.
Complete compilation and the current full
verifier remain pending for this changed source. The mathematical theorem
and its hypothesis H are unchanged; earlier successes below retain their
original source-bound scope.

**Package status at the September 27, 2026 checkpoint (08:04 UTC):** candidate23's
deterministic export and archive-only metadata gate passed. Its archive SHA-256
is `a8b47796a275a598e2be85c9f6d4e28b560782047b4b7d6e8ea6c5c3f3d7132d`, and the gate used PalomarSubmission revision
`a59f25bd8a66bf6faf3a4f4260d412989c0185ea`. This does not include a full build
or verifier run. Candidate22's archive-only gate also passed; candidate21's
preserved archive gate failed metadata because its wrapper omitted the explicit
policy revision. Candidate20 retry2 stopped at 148,000/149,249 con-ron checks
when host available RAM reached 3.423931 GiB, below the 3.5 GiB threshold; it
exited 75 without a cgroup OOM or kernel verdict. No full-verifier or H proof
pass is claimed at this checkpoint. The mathematical statement and sole
hypothesis H are unchanged. See the [candidate23 archive gate
receipt](../verification/conditional-candidate23-20260927/candidate23-archive-check.json)
and [reproduction account](PALOMAR_REPRODUCE.md).

**Historical local preparation, 2026-09-23:** archive 17 pinned Lean
`v4.32.0`. The current public Palomar intake requires at least
`v4.35.0-rc2` and rejects that archive before compilation. The historical
full local verifier pass was on byte-identical selected proof inputs under
the older pinned implementation. Assess a later matched-toolchain source
build and current verifier run from their own exact-digest receipts. See
[PALOMAR_REPRODUCE.md](PALOMAR_REPRODUCE.md) for exact receipts and scope.

## Statement

For a finite set $U\subset\mathbb C$, let $u(U)$ be the number of unordered
pairs of distinct points at Euclidean distance one. Put

```text
a = 2083647/2000000 = 1.0418235,
d = 524288 = 2^19,  delta = 1/12000,
ell = (9/4) log 2 + (1/2) log 15015,
C = 42165819/1000000000 = 0.042165819.
```

The field $K$ is defined below. Assume

```text
log(Re zeta_K(1 + delta))/d
  + delta * ((ell - gamma - log(4*pi))/4
             - Re((zeta_K'/zeta_K)(2))/d) < C.                 (H)
```

Then there is a sequence of finite sets $U_j\subset\mathbb C$ such that

```text
|U_j| -> infinity,
u(U_j) / |U_j|^a -> infinity.
```

In particular, for every cardinality threshold $N$ and every real factor
$A>0$, some finite set has cardinality at least $N$ and at least
$A|U|^a$ unordered unit pairs. The statement does not assert a lower bound
at every sufficiently large cardinality.

The compared declaration is
`UnitDistanceZetaSubmission.target_of_canonical_zeta_bound`. Its independent
statement is [ChallengeZeta.lean](../ChallengeZeta.lean), and its proof is
[SolutionZeta.lean](../SolutionZeta.lean). There are no definition holes.
The one `sorry` in the Challenge is the deliberate theorem placeholder;
the Solution and its proof dependencies may use only `propext`, `Quot.sound`
and `Classical.choice`.

## The fixed field

Work in a fixed algebraic closure of the rationals. Choose square roots
$g_i$ of `[-1, 2, 3, 5, 7, 11, 13]`, in that order. A mask is an integer
whose bit $i$, starting at zero, selects the $i$-th factor. Write
$g(m)=\prod_{i: \mathrm{bit}_i(m)=1}g_i$. Define seventeen elements
$b_i=x_i+y_i g(m_i)$ from these literal tables:

| Table | Entries, indexed from zero |
| --- | --- |
| $m_i$ | `1,41,3,41,41,17,11,34,69,25,97,5,67,7,19,33,1` |
| $x_i$ | `4,6,1,1,7,1,1,19,4,1,5,1,1,1,3,3,-2` |
| $y_i$ | `7,1,4,1,1,1,10,2,1,7,1,2,2,8,2,1,3` |
| $w_j$ | `2,256,512,4096,9,65,132,2052,24576,37,32768,65536` |

For each of the twelve masks $w_j$, choose a square root $r_j$ of
the product of its selected $b_i$. Let
$K=\mathbb Q(g_0,\ldots,g_6,r_0,\ldots,r_{11})$.
These are algebraic generators, not assumptions about a field to be found.
`Classical.choose` fixes the square roots; it imposes no positivity convention.
`CanonicalRetainedEquiv.lean` aligns the genus-root signs and proves an actual
rational algebra isomorphism to the constructed arithmetic field. In
particular, `CanonicalRetained.degree` proves $[K:\mathbb Q]=524288$.
The choice of signs is accounted for in that isomorphism.

## Ordinary meanings and the boundary of the result

The Challenge uses Mathlib's complex numbers, Euclidean `dist`, finite sets,
real powers, filters, `NumberField.dedekindZeta`, and complex `logDeriv`.
It imports only canonical Mathlib modules. It contains all nineteen-radical
field data and the entire inequality, so reading its statement does not
require trusting project definitions.

`unitPairs` is the real number obtained by dividing the cardinality of
`{(x,y) in U x U | dist x y = 1}` by two. Distance one excludes the diagonal,
and the map to unordered pairs has fibers of size two. The internal theorem
`UnitDistance.unitPairs_eq_unordered_card` in
[Counting.lean](../UnitDistance/Counting.lean) proves the exact normalization.
`Target.lean` contains the literal sequence target used in the proof.

The zeta function is the ordinary ideal-norm Dirichlet series at the two
arguments in (H), both strictly greater than one. The project proves its
series identity, positivity and analytic properties on that half-plane.
Consequently the real logarithm in (H) is evaluated at a positive number,
and `logDeriv` there agrees with the ordinary quotient of derivative by
value. Lean's totalized logarithm and division do not introduce a zero-value
loophole. The sign in (H) follows from the proved prime-sum identity in
[PrimeDebitLogDerivative.lean](../UnitDistance/PrimeDebitLogDerivative.lean).

The hypothesis is a single explicit scalar assertion, but proving it is
substantial work: it involves the zeta function of a degree-$524288$ field.
No Lean-verified enclosure of its full left-hand side is claimed; the
computer-assisted evidence for (H) is described in the next section and is
not part of the Lean proof. The manuscript and its calculations motivate
(H); they are not an assumed oracle in the Lean proof, nor a proof of (H)
supplied by this package. No proof of (H), its negation, or its consistency
is claimed by this conditional submission. There is no additional GRH or
tower-existence hypothesis.

### Alignment imports in the Challenge

`ChallengeZeta.lean` imports `Mathlib.Analysis.CStarAlgebra.Classes` and
`Mathlib.AlgebraicTopology.SimplexCategory.Basic`, and removes the instance
`instCommCStarAlgebraComplex` locally (`attribute [-instance] ... in`) for
the single definition `orderedUnitPairs`. Neither import contributes
mathematical content to the statement. They exist solely so that the
Challenge, whose import list is far smaller than the Solution's, elaborates
the same instance terms as the Solution for Comparator's structural
comparison. This was checked on 2026-09-22: all instance paths involved are
definitionally the standard ones, and the removal has no semantic effect.
`set_option backward.isDefEq.respectTransparency false` is an
elaborator-only option; it changes no definition, theorem or axiom. From
`namespace` onward, the Challenge and Solution files differ only at the
`sorry`/`exact` line of the compared theorem.

## Numerical evidence for (H)

None of the material in this section is part of the Lean proof. It records
the conventional computer-assisted evidence that (H) holds, so that a
reader can judge how far the conditional theorem is from an unconditional
one, and it is stated with its scope.

Write $M$ for the fixed field $K$ (the manuscript's degree-$524288$
retained field, `CanonicalRetained.Carrier` in the Challenge), and write $N$
for the degree-$16384$ completed analytic subfield. These are distinct fields. Let
$\sigma = 12001/12000$. The manuscript's certificate bounds, for $M$
itself,

```text
log zeta_M(sigma) / 2^19       <= Y + B_D - S_4 - S_cen,
-(zeta_M'/zeta_M)(2) / 2^19    <= R.
```

The zeta value is positive and its logarithmic derivative is real at these
arguments. With the signs displayed above, the left side of (H) is at most

```text
Y + B_D - S_4 - S_cen + (sigma - 1) L,
L = (ell - gamma - log(4 pi))/4 + R.
```

The five certified allowances are:

| Allowance | Meaning | Certified bound |
| --- | --- | --- |
| $Y$ | analytic part: $\zeta_N$ with the exceptional Euler factors removed, bounded through the Hecke-factor calculation | $\le 0.000445355407103547$ |
| $B_D$ | restored exceptional Euler factors of $M$ | $\le 0.041727023150898786$ |
| $S_4$ | saving from the $P_4$ primes | $\ge 0.00003724741189544274807446$ |
| $S_{cen}$ | saving from the census condition | $\ge 0.00004201663320373563276702$ |
| $(\sigma-1)L$ | slope term at the logarithmic derivative | $\le 0.00006870442657779491222606$ |

Their exact sum is

```text
0.04216181893948094953138458 < 0.042165819.
```

The slack to this package's ceiling `0.042165819` is exactly
`0.00000400006051905046861542`. The slack to the manuscript's own threshold
`0.042161819` is about `6.05e-11`. This is slack in an upper-bound
certificate, not a measurement of the true value of the left side of (H),
and not an improvement in the exponent.

### What the evidence establishes as of September 23, 2026

The [September 21 external-proof account](../verification/external-zeta-20260921/README.md)
and [September 22 replay](../verification/external-zeta-20260922/README.md)
separate the manuscript argument from its numerical checks. The latter
recomputed the finite formula assembly with outward rounding, obtaining
`0.0421618189394842`. It checked the stored census and moment data by hash;
it did not regenerate every moment table or census in that run. The
certificate's positive slack does not itself obstruct a proof of H. An
estimate that loses more than that slack would need refinement or another
argument.

The following developments concern the external certificate or research
lemmas outside the selected conditional proof closure. Each result has a
narrower scope than a proof of H.

| Component | Established evidence | Remaining boundary |
| --- | --- | --- |
| Finite prime savings | The checked 1,000-prime support yields actual saving `2231824/10^11`. A new exact external replay validates 387,955 eligible primes through `163137359449`, all 6,716 bin receipts, and saving `152066974999277949267719/4000000000000000000000000000 > 3801674/10^11`. The hardened V2 replay binds assertion mode and source hashes. | The larger support has no Lean certificate; neither support supplies the analytic factor bound. See the [finite-support design](../verification/sol-luna-20260923/factor-inventory/finite-support-design.md) and [V2 receipt](../verification/sol-luna-20260923/factor-inventory/finite-support-replay-v2-summary.json). |
| Actual conductor-13 factor | The preceding September 22–23 run proved a coherent actual factor norm below one and connected it to the completed-field expression. | This is inherited work, not a new result of the eight-hour run. Its logarithmic saving is weaker than the manuscript row and cannot be subtracted as an additional certificate improvement. See the [actual norm](../verification/sol-luna-20260922/zeta-conductor13-final-norm.md), [completed-field connection](../verification/sol-luna-20260922/completed-actual-relative-chi13-saving.md), and [budget scope](../verification/sol-luna-20260922/genus13-budget-scope.md). |
| All 128 genus characters | The new replay reconstructs all 677,376 complete-period character values using a separate Kronecker implementation and recomputes primitive/deleted L-values. An additional finite atom check agrees on all residues. Lean has a checked actual atom expansion and coherent-product identities. | The numerical replay shares FLINT's Dirichlet-L backend with the inherited computation. The explicit all-mask Lean atom-to-Kronecker/Conrey identification and actual numerical row bounds remain open. See the [genus report](../verification/sol-luna-20260923/genus-all-characters/REPORT.md) and [bridge review](../verification/sol-luna-20260923/genus-all-characters/lean-bridge-review.md). |
| All 32 H6 quadratic AFE rows | A newly derived generalized-exponential-integral kernel reconstructs 164,712 coefficient entries and makes 45,552 expint evaluations. All frozen individual bounds pass; minimum margin is about `2.0592384721174497e-20`. Lean checks the exact rational endpoint comparisons. | The replay shares Arb/FLINT and inherited coefficient helpers. Actual factor identities, functional equations, contour-shift growth, deleted Euler factors and all-`n` coefficient bounds are analytic premises. See the [batch report](../verification/sol-luna-20260923/numerical-audit/h6-all-quadratic-expint-report.md), [source review](../verification/sol-luna-20260923/numerical-audit/h6-all-quadratic-expint-source-review.md), and [rational checks](../verification/sol-luna-20260923/numerical-audit/h6-all-quadratic-lean-arithmetic.md). |
| Independent actual quartic-field check | PARI maximal-order prime decompositions match all 164,712 coefficients and all 224 exceptional factor cross-products for the 32 twists. The earlier plus-row attempt 4 matches 3,922 coefficients and seven exceptional factors. | These are finite checks. The all-32 checker and 9 MB raw receipt were produced after archive 17 and are checkout-side. See the small [all-32 status report](../verification/sol-luna-20260923/factor-inventory/h6-all32-quartic-zeta-quotient-status.md) and the packaged [plus-row report](../verification/sol-luna-20260923/numerical-audit/h6-quartic-zeta-quotient-report.md). |
| H6 local and analytic argument | Source-level good-prime and seven-prime calculations derive the quotient Euler factors. The paper conductor calculation gives rational conductors `35·429·4^e`, `e=0,2,3`, matching `15015,240240,960960`. Standard relative Hecke theorems supply a paper route to continuation, functional equation and growth. | These are not Lean proofs. A fresh all-32 PARI discriminant checker has no successful receipt. The exact completed-field placement, field/order bridge and AFE application remain open. See the [conductor calculation](../verification/sol-luna-20260923/factor-inventory/h6-all32-conductor-paper-derivation.md), [placement record](../verification/sol-luna-20260923/factor-inventory/h6-all32-completed-field-placement.md), and [analytic review](../verification/sol-luna-20260923/factor-inventory/h6-all32-analytic-independent-audit.md). |
| H7 and octic work | Fresh individual H7 pure/mixed-quartic replays pass their finite comparisons. A separate segmented octic traversal matches all 544 moment bins and 548,127 nonzero coefficients through `N=360720360`. | The octic traversal shares prime helpers and proves no AFE endpoint or tail. The other factor families remain incomplete. See the [numerical report](../verification/sol-luna-20260923/numerical-audit/REPORT.md) and [octic receipt](../verification/sol-luna-20260923/numerical-audit/h7_octic_segmented_direct.json). |

The original SplitKernels replay of one H6 mixed-quadratic row failed its
strict frozen upper bound by about `4.45e-26` at `sigma=12001/12000`.
That failed comparison remains recorded. The separately derived expint
kernel passes that row, and exact Fraction substitution of all 32 expint
uppers retains the same rounded group allowance and five-family ceiling.
This checks arithmetic conditional on the row enclosures; it does not prove
their analytic premises or improve the exponent. The
[target-sigma report](../verification/sol-luna-20260923/numerical-audit/h6-target-sigma-direct-report.md)
and [aggregate audit](../verification/sol-luna-20260923/numerical-audit/h6-target-batch-aggregate-independent-audit.md)
also distinguish the separate `sigma=6001/6000` computation, whose bound
cannot be transferred across sigma without an argument.

The [assumption ledger](ASSUMPTIONS.md) records checked sufficient conditions
and remaining analytic obligations. The [September 23 detailed handoff](CONDITIONAL_HANDOFF_SOL_LUNA_20260923.md)
and [preceding run handoff](CONDITIONAL_HANDOFF_SOL_LUNA_20260922.md) retain
declaration-level checks, failures and chronology. These are dated research
records; their checkout-only source links and historical resource policies
do not enlarge the proof or impose a method for future work.

## Proof organization

| Step | Content and principal source |
| --- | --- |
| Identify the fixed field | `CanonicalRetainedEquiv.lean` and `NumberFieldNumericInvariance.lean` identify the explicit radicals, degree and zeta quantities under a rational algebra isomorphism. |
| Construct the family | `SigmaCutInfinite.lean` proves that the required pro-2 family is infinite (optimized Golod–Shafarevich local-block inequality); `SigmaCutUnconditional.lean` only instantiates the presentation. `SigmaCutFamily.lean` and the arithmetic/cohomological dependencies supply the local conditions and growth. |
| Bound the discriminant | `RetainedDyadicDifferentComplement.lean` supplies the retained different estimate; `RetainedDyadicDifferentReduction.lean` converts the different exponent to the logarithmic root-discriminant bound `log rd <= logRD`. |
| Transfer the scalar estimate | `RelativeResidueFixedBase.lean`, `ImaginaryQuadraticContinuation.lean`, the `TsfasmanVladut*.lean` modules and `SharperPairFixedBaseBridgeRun20260920.lean` transfer the fixed-field ceiling to the required relative-residue estimates along the family. The relative Hecke continuation is proved only for `K = F(i)` with `sqrt 7 in F` (`ImaginaryQuadraticContinuation.lean`); it is not a general relative continuation. |
| Count and project | `RelativeUnitsMass.lean`, `SIntegerWitnessGraph.lean` and the geometric dependencies supply actual mass identities, lattice counts, finite windows and projection into the Euclidean plane. |
| Certify the margin | The pair-functional certificates (`PairFunctionalSharperCertificateAstra.lean`, `PairFunctionalSharperThresholdAstra.lean`) prove the sufficient integral estimate `JPair >= 1.379633`. `SharperPairArithmeticRateCoreRun20260920.lean` combines it with the arithmetic costs. The strict inequality in (H) leaves a positive exponential margin. |
| Conclude both limits | `ArithmeticSequence.lean` and `Counting.lean` give the literal sequence theorem; `CanonicalSharperZetaResultRun20260920.lean` assembles the endpoint used by the Solution. |

The Lean route differs from the manuscript at three points.

1. The manuscript's analytic ceiling is replaced by the hypothesis (H) on
   the fixed degree-$524288$ field plus a formalized Tsfasman–Vlăduţ
   transfer.
2. The retained quotient is the field $M$ plus a finite cubic detector with
   centralizer index at least $4096$, not the manuscript's $Q = G/D_4 G$.
3. The pair-integral bound proved in Lean is `JPair >= 1.379633`, weaker
   than the manuscript's `1.379635324335`; this is compensated by relaxing
   the ceiling from the manuscript's `0.042161819` to `0.042165819`
   (a relaxation of `4e-6`). The exponent is unchanged.

The library ports, adaptation boundaries and licenses are recorded in
[SUBMISSION_PROVENANCE.md](SUBMISSION_PROVENANCE.md). The import closure,
source hashes and selected configuration are recorded in `SELECTION.json`
and `SOURCE_SNAPSHOT.json` in the exported package.

## Public record and related formalizations

Public claims for the unit-distance lower exponent, all of the form
"for arbitrarily large $n$", as of 2026-09-22:

| Source | Exponent | Status |
| --- | --- | --- |
| OpenAI internal model, May 20, 2026; human-verified digest by Alon, Bloom, Gowers, Litt, Sawin, Shankar, Tsimerman, Wang, Wood ([arXiv:2605.20695](https://arxiv.org/abs/2605.20695)) | inexplicit, $> 1$ | disproof of the Erdős unit-distance conjecture |
| Sawin ([arXiv:2605.20579](https://arxiv.org/abs/2605.20579)) | `1.014114` | explicit; public |
| Emmerich ([arXiv:2606.03419](https://arxiv.org/abs/2606.03419)) | `1.0152` | reoptimized certificate; public |
| Emmerich–Cordella (Zenodo [10.5281/zenodo.20551478](https://doi.org/10.5281/zenodo.20551478)) | `1.0311853` | public |
| MathOverflow question 511514, answer 511576 (Eric Naslund, May 26, 2026) | headline `1.03583`; the June 9, 2026 change-log records a bookkeeping issue and states the corrected best bound as $\delta > 0.0357$ | unverified forum claim |
| Tao's optimization-problems page (constants/84a, last edited 2026-05-30) | lists `1.03583` as "Current best. Unverified." | stale relative to the June 9 correction |
| This package | `1.0418235` | conditional on (H); the manuscript is unpublished |

The upper bound is $O(n^{4/3})$ (Spencer–Szemerédi–Trotter). Nothing above
`1.036` stands publicly as of 2026-09-22.

Lean formalizations of unit-distance results known to the preparer:

- `plby/Erdos90` (Boris Alexeev): unconditional $\exists\,\delta>0$, no
  explicit exponent; lean-eval accepted 2026-06-26.
- `Jayyhk/erdos-lean`, `problems/90`: a repackaging of the above.
- `logical-intelligence/erdos-unit-distance`: $\exists\,\delta>0$,
  conditional on two named hypotheses (a Golod–Shafarevich inequality and a
  Shafarevich relation-rank bound).
- `kim-em/erdos-unit-distance-comparator`: Alpöge's uniform-constant
  negation; the only unit-distance entry in the Palomar registry
  (`PALOMAR-2026-08-08-000001`).
- `n-yamaguchi-0729/SawinTotallyRealTowers`: only Sawin's totally real
  tower input.
- `google-deepmind/formal-conjectures`, `ErdosProblems/90.lean`:
  `sawin_explicit` with `1.014114`, still `sorry`.

To the preparer's knowledge, no public Lean formalization states an
explicit numerical unit-distance exponent. Novelty of the conditional
reduction has not been established.

## Research context

The Erdős unit-distance conjecture was disproved in May 2026: an OpenAI
internal model found a construction with an inexplicit exponent above one,
and Alon et al. published the human-verified digest. Sawin's
[explicit construction](https://arxiv.org/abs/2605.20579v1) then gave the
exponent `1.014114` using number fields with controlled discriminants and
small primes, and later public claims reach about `1.036`. The
[exposition by Alon et al.](https://arxiv.org/abs/2605.20695v1) explains the
arithmetic approach to power-law lower bounds. The present development
follows Eric Naslund's manuscript, which refines this mechanism and
advertises an unconditional `1.0418235`. This package formalizes only the
implication with (H). It therefore does not claim to improve an
unconditional published bound or to settle a new unconditional
unit-distance exponent.

The intended audience is researchers in discrete geometry and arithmetic
constructions using class field towers. What is kernel-checked is an
infinite pro-2 family with prescribed dyadic ramification, the discriminant
bound, the Tsfasman–Vlăduţ transfer, the relative mass identity, the
lattice and planar construction and both limits of the sequence theorem.
The only unproved input is one scalar Dedekind-zeta inequality for one
explicit field, and the numerical evidence for it is set out above. The
interest of the reduction is not established merely by the amount of Lean
code, and its novelty has not been established.

The manuscript is included in this package under `docs/manuscript/`; the
research repository it comes from was private as of 2026-09-22. Its AI
Methodology statement says the work was done with extensive AI use, with
agents developing the mathematics and writing the paper, and it is an
unrefereed preprint. It is disclosed as source provenance and is not used to
establish novelty, priority or research interest. The independently stated
conditional reduction and the public literature above supply the
mathematical content and context that a reviewer can assess.

## Historical package and verification status, September 23, 2026

As of this dated record, archive 17 was the latest sealed candidate, SHA-256
`3e369cb1cdc367fbb396946b9b69c1898a99d69cbb534b9b0d5ebe8cc29f1672`.
Its [post-export record](../verification/conditional-20260923/candidate17-packaging-preparation.md)
reports deterministic archive, metadata, selected-proof-input identity,
17 extracted finite-script and two extracted genus/atom checks. Those
receipts were generated after sealing and are not members of archive 17.
The [post-seal errata](../verification/conditional-20260923/candidate17-postseal-errata.md)
correct the supporting conductor normalization and completed/retained-field
names; H and the selected proof inputs are unchanged. Candidate 18's export
had not completed by September 23. The [final handoff](FINAL_HANDOFF_SOL_LUNA_20260923.md)
records that stopping point and the later checkout-side all-32 PARI result.

Only archive 07 received a complete local verifier pass, under the old
pinned implementation. Archive 17 has byte-identical selected proof inputs.
Current policy requires Lean `v4.35.0-rc2`; archive 17 pins `v4.32.0`, so
the current-policy check rejects that archive before proof compilation.
Assess any later migrated archive and current full verifier run by their
own source and archive-bound receipts. These are local records, not an
official Palomar report. No publication or submission is claimed. Exact
pins, receipts and commands are in
[PALOMAR_REPRODUCE.md](PALOMAR_REPRODUCE.md).

## Supplemental file selection

The following paths are explicit inputs to the source exporter's one-level
document-reference scan. They retain the dated supplementary scripts,
receipts and reviews used by this account; including a file does not attest
that its computation or draft proof succeeded. Reports identify unrun drafts,
failed attempts, conditional numerical inputs and checkout-only large data.
They are not the selected Lean proof closure.

```text
verification/sol-luna-20260923/genus-all-characters/{*.md,*.py,*.json}
verification/sol-luna-20260923/numerical-audit/{REPORT.md,*.py,*.cpp,*.json,*.log,h7-octic-*.md}
verification/sol-luna-20260923/factor-inventory/{finite-support-design.md,finite-support-independent-review.md,replay_finite_support.py,finite-support-replay-summary.json,finite-support-replay-v1-20260923/*.json,finite-support-replay-v2-summary.json,finite-support-replay-v2-20260923/*.json}
verification/sol-luna-20260923/{independent-review.md,external-proof-review.md}
verification/conditional-20260923/{current-policy-compatibility.md,current-policy-smoke-14.json,toolchain-migration-assessment.md,toolchain-migration-preparation.md,candidate15-packaging-preparation.md,package-documentation-audit.md}
verification/conditional-20260923/current-policy-smoke-15.json
verification/sol-luna-20260923/numerical-audit/{h6_mixed_quadratic_direct.py,h6_mixed_quadratic_direct.json,h6_aggregate_replacement.py,h6_aggregate_replacement.json,h6-mixed-quadratic-direct-review.md}
verification/sol-luna-20260923/numerical-audit/{h6_target_sigma_direct.py,h6_target_sigma_direct.json,h6_target_sigma_direct_attempt1.source,h6_target_aggregate_replacement.py,h6_target_aggregate_replacement.json,h6-target-sigma-direct-report.md,h6-target-sigma-independent-review.md}
verification/sol-luna-20260923/numerical-audit/{h6-target-lean-arithmetic.md,h6-target-lean-arithmetic-transcription-review.md}
verification/sol-luna-20260923/numerical-audit/{h6_target_sigma_expint.py,h6_target_sigma_expint.json,h6-target-sigma-expint-plan.md,h6-target-sigma-expint-report.md,h6-expint-formula-independent-review.md,h6-contour-growth-source-audit.md,h6-target-sigma-expint-source-audit.md,h6-target-expint-lean-arithmetic.md,h6-target-expint-transcription-review.md}
verification/sol-luna-20260923/numerical-audit/{h6_all_quadratic_expint.py,h6_all_quadratic_expint.json,h6-all-quadratic-expint-plan.md,h6-all-quadratic-expint-report.md,h6-all-quadratic-expint-source-review.md,h6-all-quadratic-expint-receipt-audit.md,h6-all-quadratic-lean-arithmetic.md,h6-all-quadratic-expint-lean-transcription-review.md}
verification/sol-luna-20260923/numerical-audit/{h6_target_batch_aggregate.py,h6_target_batch_aggregate.json,h6-target-batch-aggregate-plan.md,h6-target-batch-aggregate-report.md,h6-target-batch-aggregate-independent-audit.md,h6-plus-afe-analytic-gap.md}
verification/sol-luna-20260923/numerical-audit/{h6_quartic_zeta_quotient.py,h6_quartic_zeta_quotient_attempt4.json,h6_quartic_zeta_quotient_attempt4-provenance.json,h6_quartic_zeta_quotient_attempt4.source,h6-quartic-zeta-quotient-plan.md,h6-quartic-zeta-quotient-report.md,h6_quartic_zeta_quotient-independent-review.md}
verification/sol-luna-20260923/numerical-audit/{h6-quartic-zeta-quotient-all32-plan.md,h6-all32-inherited-pari-audit.md}
verification/sol-luna-20260923/factor-inventory/artin-degree-two-coefficient-majorant.md
verification/sol-luna-20260923/factor-inventory/{two-eigen-euler-coefficient-lemma.md,h6-mask1586-plus-field-bridge-gap.md,plus-field-bridge-independent-review.md,multiplicative-prime-power-d2-bridge.md,h6-plus-p17-residue-check.md}
verification/sol-luna-20260923/factor-inventory/{h6-plus-quartic-pari-status.md,h6-plus-quartic-local-factors.gp,h6-plus-quartic-pari-run-20260923.log,h6-plus-quartic-pari-receipt-20260923.json}
verification/sol-luna-20260923/factor-inventory/h6-plus-all-prime-euler-and-analytic-data.md
verification/sol-luna-20260923/factor-inventory/h6-all32-good-prime-derivation.md
verification/sol-luna-20260923/factor-inventory/{h6-all32-remaining-bad-local.md,h6-all32-p2-p5-symbolic.md,h6-all32-p3-p11-p13-symbolic.md,h6-all32-p7-local.md,h6-all32-p17-symbolic.md,h6-all32-conductor-paper-derivation.md,h6-all32-completed-field-placement.md,h6-all32-relative-hecke-corollary.md}
verification/conditional-20260923/candidate17-postseal-errata.md
verification/sol-luna-20260923/factor-inventory/{plus-field-bridge-status.md,plus-field-bridge-lean-run-20260923.log,plus-quartic-pari-independent-review.md}
verification/sol-luna-20260922/{submission-supplement.md,field_bridge_audit.*,geometry_margin_audit.*,order_four_log_check.*,exceptional_euler_log_check.*,central_bin_interval_check.*,quartic_field_trace_check.*,quartic-field-review.md,quartic_field_composites_check.*,quartic-composites-review.md,genus13_lvalue_interval*,genus13_common_level_interval*,genus13_short_upper_certificate*,hecke_all_rows_prefix*,hecke-all-rows-prefix-source-review.md,h7_all_new_coefficients*,h7_census_suffix_check.*,h7-census-suffix-review.md,afe-one-factor-review.md,debit_*,numerics*,euler-source.json,fresh-proof-review.md}
docs/ASSUMPTIONS.md
docs/FINAL_HANDOFF_SOL_LUNA_20260923.md
docs/CONDITIONAL_HANDOFF_SOL_LUNA_20260923.md
docs/CONDITIONAL_HANDOFF_SOL_LUNA_20260922.md
docs/CONDITIONAL_HANDOFF_20260921.md
verification/external-zeta-20260921/README.md
verification/external-zeta-20260922/README.md
verification/sol-luna-20260923/factor-inventory/finite-support-design.md
verification/sol-luna-20260923/factor-inventory/finite-support-replay-v2-summary.json
verification/sol-luna-20260922/zeta-conductor13-final-norm.md
verification/sol-luna-20260922/completed-actual-relative-chi13-saving.md
verification/sol-luna-20260922/genus13-budget-scope.md
verification/sol-luna-20260923/genus-all-characters/REPORT.md
verification/sol-luna-20260923/genus-all-characters/lean-bridge-review.md
verification/sol-luna-20260923/numerical-audit/h6-all-quadratic-expint-report.md
verification/sol-luna-20260923/numerical-audit/h6-all-quadratic-expint-source-review.md
verification/sol-luna-20260923/numerical-audit/h6-all-quadratic-lean-arithmetic.md
verification/sol-luna-20260923/factor-inventory/h6-all32-quartic-zeta-quotient-status.md
verification/sol-luna-20260923/numerical-audit/h6-quartic-zeta-quotient-report.md
verification/sol-luna-20260923/factor-inventory/h6-all32-conductor-paper-derivation.md
verification/sol-luna-20260923/factor-inventory/h6-all32-completed-field-placement.md
verification/sol-luna-20260923/factor-inventory/h6-all32-analytic-independent-audit.md
verification/sol-luna-20260923/numerical-audit/REPORT.md
verification/sol-luna-20260923/numerical-audit/h7_octic_segmented_direct.json
verification/sol-luna-20260923/numerical-audit/h6-target-sigma-direct-report.md
verification/sol-luna-20260923/numerical-audit/h6-target-batch-aggregate-independent-audit.md
verification/conditional-20260923/candidate17-packaging-preparation.md
verification/conditional-20260923/candidate17-postseal-errata.md
verification/cleanup-20260921/arithmetic/README.md
verification/sol-luna-20260923/relative-aggregate-budget.md
verification/sol-luna-20260923/primitive-atom-expansion-light.md
verification/conditional-20260923/current-policy-smoke-17-head1703.json
verification/conditional-20260923/current-policy-compatibility.md
verification/conditional-20260923/toolchain-migration-assessment.md
verification/conditional-20260923/toolchain-migration-preparation.md
```
