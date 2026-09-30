# Sol/Luna conditional-formalization continuation — September 22, 2026

This run started at 21:14 UTC and stops by 02:14:26 UTC on September 23.
The exact target is [GOAL.md](../GOAL.md). The selected Lean theorem is still
conditional: [ChallengeZeta.lean](../ChallengeZeta.lean) states one explicit
inequality (H) for the degree-524288 fixed field, and
[SolutionZeta.lean](../SolutionZeta.lean) derives finite planar sets with
unbounded cardinality and unordered unit-pair count divided by
\(|U|^{2083647/2000000}\) tending to infinity. The exponent is
\(1.0418235\). **(H) has not been proved in Lean**, so this is not an
unconditional bound.

## Resumable package checkpoint

The current locally prepared source candidate is
[candidate 14](../dist/conditional-20260922/conditional-source-14.tar.gz),
SHA-256
`4d4e657cbb557049b1d8281321941c1940053af40a2669d0435ed5388b500199`;
the extracted snapshot hash is
`43dd1bf4f9d3c97671f34b6989321f4727f2347a5fb1e455ede58aca1dda5175`.
Its deterministic [export](../verification/conditional-20260922/export-14.json)
and [reseal test](../verification/conditional-20260922/test-export-14.json)
passed. The [exact proof-input comparison](../verification/conditional-20260922/proof-input-identity-14.json)
found all 2,165 Lean files, Lake/build/config files, scripts and third-party
provenance byte-identical to archive 07. Archive 07, SHA-256
`f5bfc2e50e6432af0d6dfccf26801bf1de6d147f42cb6b037478e0b40c3ccd0a`,
had the [complete local pinned verifier pass](../verification/conditional-20260922/standard-07.json)
in 11,378 seconds. Candidate 14 itself did **not** receive a fresh complete
verifier run. The identity check transfers the proof-input scope of the
archive-07 receipt; it is not a new kernel replay.

All seventeen finite checkers included in candidate 14 passed from its extracted
standalone payload under the shared guard
([package smoke receipt](../verification/conditional-20260922/package-smoke-14-retry.json)).
The first [smoke attempt](../verification/conditional-20260922/package-smoke-14.json)
stopped after ten passing scripts because the optional AFE checker could not
import host `python-flint`; the successful retry set its existing local
`PYTHONPATH` and reran all seventeen scripts. This dependency is not shipped
with the source archive.
The companion [submission supplement](../verification/sol-luna-20260922/submission-supplement.md)
states what each script reads and does. A local
[pinned metadata check](../verification/conditional-20260922/metadata-14.json)
also passed; it did not run the official intake or full verifier. Candidates
09 through 13 remain intermediate sealed checkpoints. No source archive or sealed
receipt from earlier work was overwritten.

The strongest new checked sidecar result proves the **actual coherent χ₁₃
value** at the certificate point has norm at most
`4689291963776399684905241675231/4745938638374004765750000000000 < 1`,
and its log term is below the negative rational margin
`56646674597605080844758324769/4745938638374004765750000000000`.
These Lean modules are in the working tree outside candidate 14's selected
proof closure. The other 127 coherent genus terms and the actual relative
Euler product still lack numerical upper bounds, so (H) and the
unconditional target remain open.

## New checked Lean progress outside the selected proof closure

- [ZetaLunaRun20260922.lean](../UnitDistance/ZetaLunaRun20260922.lean)
  identifies the actual real and complex log-zeta score and its derivative
  debit, and proves a generic finite-factor upper-bound implication.
  A guarded pinned compile and four-endpoint axiom audit passed.
- [ZetaLunaImprimitiveLogRun20260922.lean](../UnitDistance/ZetaLunaImprimitiveLogRun20260922.lean)
  specializes the local-to-global product to the actual completed field:
  under genuine factor Euler products, a primewise local identity and
  nonzero special values, its imprimitive log equals the
  representation-degree-weighted sum of factor log moduli. A separate row
  grouping yields the exact five-family `hfactor` expression with
  normalization 16384. A guarded compile and six-endpoint axiom audit
  passed. These product, local, grouping and numerical premises remain
  explicit; [the theorem report](../verification/sol-luna-20260922/zeta-imprimitive-log.md)
  lists them.
- [ZetaLunaConductorThirteenEulerRun20260922.lean](../UnitDistance/ZetaLunaConductorThirteenEulerRun20260922.lean)
  proves the actual selected conductor-13 genus primitive character is
  pointwise quadratic mod 13, reindexes its genuine Dirichlet Euler product
  to rational height-one places, and proves its special value at
  \(12001/12000\) is nonzero. A guarded compile and five-endpoint
  standard-axiom audit passed. This is the primitive all-prime factor; the
  next modules delete the selected primes. Identifying its manuscript row
  and proving the complete Artin local identity and factor inventory remain
  open.
- [ZetaLunaConductorThirteenImprimitiveEulerRun20260922.lean](../UnitDistance/ZetaLunaConductorThirteenImprimitiveEulerRun20260922.lean)
  now deletes exactly the selected rational Euler factors, proves the
  resulting product converges to the primitive L-value times a finite
  correction, and proves this value nonzero at the certificate abscissa.
  Its guarded compile and three-endpoint standard-axiom audit passed.
  Identification with a specified completed-field genus slot and the full
  Artin local identity still remain open.
- [ZetaLunaConductorThirteenCommonLevelRun20260922.lean](../UnitDistance/ZetaLunaConductorThirteenCommonLevelRun20260922.lean)
  proves that the selected `S'` deletion correction equals the existing
  common-level genus correction and identifies the deleted Euler value with
  the actual common-level conductor-13 genus-character `LFunction` in
  `Re(s)>1`; it also proves that value nonzero at `12001/12000`. A guarded
  compile and three-endpoint standard-axiom audit passed. The map into a
  specified `genusLinearEulerValue` slot and completed-field Artin row is
  still open: the current 128-slot construction uses a separately chosen
  `genusSlotEquiv` at each prime. Its checked product identity gives the
  aggregate local genus factor, but no fixed χ13 assignment among those
  arbitrary slots.
- [ZetaLunaConductorThirteenSlotRun20260922.lean](../UnitDistance/ZetaLunaConductorThirteenSlotRun20260922.lean)
  uses the inherited Frobenius-indexed coherent genus coefficient, which is
  fixed across primes, and proves its conductor-13 Euler value equals both
  the common-level L-function and the selected-deletion value throughout
  `Re(s)>1`; it is nonzero at the certificate abscissa. A guarded compile
  and four-endpoint standard-axiom audit passed. The inherited library
  already proves the aggregate product of all 128 coherent genus values.
  This specialization still does not identify a literal prime-dependent
  `genusLinearEulerValue` slot or a completed-field Artin index; see the
  [exact theorem note](../verification/sol-luna-20260922/zeta-conductor13-slot.md).
- [ZetaLunaConductorThirteenPositiveRun20260922.lean](../UnitDistance/ZetaLunaConductorThirteenPositiveRun20260922.lean)
  proves the same coherent, selected-prime-deleted χ₁₃ Euler value at
  `12001/12000` is the complex cast of a strictly positive real number.
  It uses actual real Frobenius factors, absolute summability and a positive
  real product. Guarded compile and one-endpoint standard-axiom audit
  passed. The [theorem report](../verification/sol-luna-20260922/zeta-conductor13-positive.md)
  gives its scope. Positivity does not supply a numerical upper bound.
- [ZetaLunaCoherentGenusComponentRun20260922.lean](../UnitDistance/ZetaLunaCoherentGenusComponentRun20260922.lean)
  identifies the coherent 128-character genus Euler product with the
  inherited 128 linear-factor product for `Re(s)>1`; at the certificate
  point its log norm equals `genusLinearLogAtSigma`. This aggregate route
  avoids a fixed χ₁₃ assignment among prime-dependent slots. Guarded
  compile and two-endpoint standard-axiom audit passed. The
  [scope note](../verification/sol-luna-20260922/zeta-coherent-genus-component-bridge.md)
  identifies the still missing completed-field Artin inventory and
  five-family grouping.
- [ZetaLunaConductorThirteenLogSplitRun20260922.lean](../UnitDistance/ZetaLunaConductorThirteenLogSplitRun20260922.lean)
  splits `genusLinearLogAtSigma` into the selected coherent χ₁₃ log
  modulus and an explicit sum of the other 127 coherent log moduli, under
  their nonvanishing premise. A second theorem adds separate numerical
  upper bounds for those two terms; the bounds remain premises. Guarded
  compile and two-endpoint standard-axiom audit passed. The
  [exact statement](../verification/sol-luna-20260922/zeta-conductor13-log-split.md)
  does not assign χ₁₃ to a prime-dependent literal slot.
- [ZetaLunaConductorThirteenLogSplitNonzeroRun20260923.lean](../UnitDistance/ZetaLunaConductorThirteenLogSplitNonzeroRun20260923.lean)
  identifies every coherent genus value at the certificate point with its
  common-level Dirichlet L-function and uses its zero-free theorem to prove
  all 128 values nonzero. This discharges the other-127 premise above and
  yields the log split unconditionally. Guarded compile and two-endpoint
  standard-axiom audit passed; the
  [report](../verification/sol-luna-20260922/zeta-conductor13-log-split.md)
  gives exact names and provenance.
- [ZetaLunaCoherentGenusAllPositiveRun20260923.lean](../UnitDistance/ZetaLunaCoherentGenusAllPositiveRun20260923.lean)
  uses actual Frobenius signs and positive real Euler products to prove
  each of the 128 coherent genus values at `12001/12000` is strictly
  positive real. Guarded compile and two-endpoint standard-axiom audit
  passed; the [scope report](../verification/sol-luna-20260922/zeta-coherent-genus-all-positive.md)
  records the exact theorems. No numerical bound on these 128 values follows.
- [ZetaLunaCompletedGenusLocalFactorRun20260923.lean](../UnitDistance/ZetaLunaCompletedGenusLocalFactorRun20260923.lean)
  reindexes the actual prime fibers of
  `GenusField ≤ CompletedField` and factors the completed-field local
  Euler factor into the genus-field factor and an explicit relative
  correction. The imprimitive local identity identifies its genus part
  with the 128 coherent genus-character local factors. Both endpoints
  passed guarded compile and standard-axiom audit. The
  [scope note](../verification/sol-luna-20260922/zeta-actual-genus-local-factor.md)
  leaves the relative correction's further Artin decomposition open.
- [ZetaLunaCompletedGenusGlobalFactorRun20260923.lean](../UnitDistance/ZetaLunaCompletedGenusGlobalFactorRun20260923.lean)
  proves the explicit actual relative factors themselves have a convergent
  prime product for `Re(s)>1`, by dividing the actual completed-field
  imprimitive Euler product by the nonzero coherent genus product. It
  factors the completed-field imprimitive zeta value globally into the
  product of the 128 coherent genus values and that relative product.
  Guarded compile and two new standard-axiom audits passed. The remaining
  Artin/Hecke decomposition and numerical bound of the relative product
  are open; see the [scope note](../verification/sol-luna-20260922/zeta-actual-genus-global-factor.md).
- [ZetaLunaActualRelativeLogRun20260923.lean](../UnitDistance/ZetaLunaActualRelativeLogRun20260923.lean)
  takes real log norms of the actual global factorization at the
  certificate point. It proves the completed-field imprimitive log equals
  `genusLinearLogAtSigma` plus the log norm of the actual relative
  Euler-product value, and proves that relative value has the stated
  convergent product. Both endpoints passed guarded compile and
  standard-axiom audit. The
  [scope report](../verification/sol-luna-20260922/zeta-actual-relative-log-split.md)
  records exact statements and source hashes. The relative log still has
  no numerical bound or Artin/Hecke row identification.
- [ZetaLunaConductorThirteenShortBoundRun20260923.lean](../UnitDistance/ZetaLunaConductorThirteenShortBoundRun20260923.lean)
  proves the exact rational endpoint of the external 52-term χ₁₃
  certificate is below 1 and, assuming the actual coherent χ₁₃ norm is
  bounded by that endpoint, proves its log term strictly lowers the genus
  remainder. Its final corollary uses the checked nonvanishing theorem for
  all 128 characters, so this is its only premise. Guarded compile and
  three-endpoint standard-axiom audit passed. The
  [interface report](../verification/sol-luna-20260922/zeta-conductor13-short-bound-interface.md)
  retains the numerical norm bound as a premise in that theorem; the later
  final-norm theorem below discharges it for the actual χ₁₃ factor.
- [ZetaLunaConductorThirteenShortBudgetArithmeticRun20260923.lean](../UnitDistance/ZetaLunaConductorThirteenShortBudgetArithmeticRun20260923.lean)
  checks the rational 52-term upper plus `2/53` tail allowance,
  their product with `13093091/9296875`, and the strict `<1`
  comparison in Lean. Its sign-aware multiplication lemma does not
  require positivity of the primitive value. Guarded compile and four
  standard-axiom audits passed. The
  [report](../verification/sol-luna-20260922/zeta-conductor13-short-budget-arithmetic.md)
  separates this arithmetic from the actual L-series and correction bounds.
- [ZetaLunaConductorThirteenDeletionScalarBoundResearch.lean](../UnitDistance/ZetaLunaConductorThirteenDeletionScalarBoundResearch.lean)
  proves the explicit real selected-prime correction is positive and at
  most `13093091/9296875`. Guarded compile and two-endpoint
  standard-axiom audit passed. The
  [scope report](../verification/sol-luna-20260922/conductor13-deletion-scalar-bound.md)
  records the scalar step.
- [ZetaLunaConductorThirteenDeletionBoundResearch.lean](../UnitDistance/ZetaLunaConductorThirteenDeletionBoundResearch.lean)
  proves that the actual common-level χ₁₃ deletion factor is the explicit
  seven-prime complex product, hence the real scalar just bounded. Its
  actual factor upper and positivity theorems passed guarded compile and
  four-endpoint standard-axiom audit. The
  [exact theorem report](../verification/sol-luna-20260922/conductor13-deletion-actual-bound.md)
  records both source hashes. This verifies the finite correction,
  without yet bounding the primitive L-value.
- [EulerLunaRun20260922.lean](../UnitDistance/EulerLunaRun20260922.lean)
  recombines ten previously checked 100-prime blocks to prove an
  actual-field support defect lower bound \(2232161/10^{11}\), a gain of
  \(337/10^{11}\). Guarded compile and two-endpoint standard-axiom audit
  passed. The 45-prime order-four actual-field bound was already proved in
  the inherited Lean sources; this run did not first formalize it.
- [GenusLunaRun20260922ConductorThirteen.lean](../UnitDistance/GenusLunaRun20260922ConductorThirteen.lean)
  identifies the actual primitive conductor-13 genus character with the
  Legendre character and bounds its L-value by a finite completion integral.
  Guarded compile and axiom audit passed. No rational upper bound for that
  integral was proved.
- [GenusLunaRun20260922ConductorThirteenCancellation.lean](../UnitDistance/GenusLunaRun20260922ConductorThirteenCancellation.lean)
  proves the actual primitive conductor-13 character has complex partial
  sums of norm at most `2` for every endpoint, by checking its thirteen
  residues and period. A guarded compile and two-endpoint standard-axiom
  audit passed.
- [GenusLunaRun20260922DirichletBound.lean](../UnitDistance/GenusLunaRun20260922DirichletBound.lean)
  proves a generic finite summation-by-parts inequality: if the coefficients'
  partial sums have norm at most `B`, `s>1` is real and their L-series is
  summable, then `‖LSeries f s‖ ≤ B`. It applies the checked χ₁₃
  cancellation theorem to prove norm at most `2` for both its actual
  primitive L-series and Dirichlet-character L-function at the certificate
  point. Guarded compile and three-endpoint standard-axiom audit passed;
  the [report](../verification/sol-luna-20260922/genus-dirichlet-bound.md)
  records the nine earlier source-error attempts. The bound `2` is too coarse
  for the needed genus allowance.
- [GenusLunaRun20260923ShortFiniteUpper.lean](../UnitDistance/GenusLunaRun20260923ShortFiniteUpper.lean)
  proves the real-power upper and lower inequalities behind the short
  χ₁₃ certificate, then the signed inequality for coefficients `-1, 0, 1`.
  A guarded compile and four-endpoint standard-axiom audit passed; the
  [report](../verification/sol-luna-20260922/genus13-finite-upper-lean.md)
  records this analytic step. The later checked modules connect it to the
  actual finite character sum, shifted tail and correction product.
- [GenusLunaRun20260923ShortFiniteCertificate.lean](../UnitDistance/GenusLunaRun20260923ShortFiniteCertificate.lean)
  checks the exact rational 52-term upper
  `70334919167156019061867/105950239461401596800000` for the explicit
  mod-13 residue pattern using those signed real-power bounds. Guarded
  compile and two-endpoint standard-axiom audit passed. The
  [report](../verification/sol-luna-20260922/genus13-finite-upper-lean.md)
  records the exact finite bound.
- [GenusLunaRun20260923ShortActualBridge.lean](../UnitDistance/GenusLunaRun20260923ShortActualBridge.lean)
  identifies that explicit residue pattern with the actual primitive
  χ₁₃ coefficient for every natural `n`, then transfers the rational
  upper to the actual weighted 52-term complex polynomial's real part.
  Guarded compile and two-endpoint standard-axiom audit passed.
- [GenusLunaRun20260923ShortActualLSeriesPrefix.lean](../UnitDistance/GenusLunaRun20260923ShortActualLSeriesPrefix.lean)
  identifies that weighted polynomial with the exact `LSeries.term`
  prefix through 52 and transfers the rational real-part upper.
  Guarded compile and standard-axiom audit passed.
- [GenusLunaRun20260923ConductorThirteenPrefix52.lean](../UnitDistance/GenusLunaRun20260923ConductorThirteenPrefix52.lean)
  proves that the actual primitive χ₁₃ coefficient sum from 1 through 52
  vanishes exactly, using its mod-13 period and the checked identification
  with the genus character. Guarded compile and standard-axiom audit
  passed.
- [GenusLunaRun20260923ConductorThirteenTail.lean](../UnitDistance/GenusLunaRun20260923ConductorThirteenTail.lean)
  proves the actual primitive χ₁₃ L-series tail after 52 terms has norm
  at most `2 * 53^(-(12001/12000))`, using the checked zero-prefix and
  shifted Abel summation. Its generic version retains an exact
  zero-prefix premise; both endpoints passed guarded compile and
  standard-axiom audit.
- [GenusLunaRun20260923ConductorThirteenShortUpper.lean](../UnitDistance/GenusLunaRun20260923ConductorThirteenShortUpper.lean)
  combines that actual 52-term prefix and shifted tail to prove the actual
  primitive χ₁₃ L-series real part is strictly below
  `3939651194782072203878951/5615362691454284630400000`. Both
  endpoints passed guarded compile and standard-axiom audit. This is a
  single primitive factor bound, not the full genus allowance.
- [GenusLunaRun20260923ConductorSevenPrefix700.lean](../UnitDistance/GenusLunaRun20260923ConductorSevenPrefix700.lean)
  proves publication mask 17's actual primitive genus character is
  quadratic modulo 7 with conductor 7, and its actual coefficients sum
  to zero over the first 700 terms. The three endpoints passed guarded
  compile and standard-axiom audit.
- [GenusLunaRun20260923ConductorSevenFiniteHead.lean](../UnitDistance/GenusLunaRun20260923ConductorSevenFiniteHead.lean)
  proves the **explicit residue-table** χ₇ weighted 700-term sum is at
  most `119/100` at the certificate point. The guarded pinned compile,
  including 700-term rational arithmetic, and focused standard-axiom
  audit passed; the [exact scope report](../verification/sol-luna-20260922/genus7_finite_head_lean.md)
  records the source hashes.
- [GenusLunaRun20260923ConductorSevenActualFiniteHead.lean](../UnitDistance/GenusLunaRun20260923ConductorSevenActualFiniteHead.lean)
  proves every actual primitive χ₇ coefficient equals the explicit
  residue pattern, then transfers the `119/100` bound to the real part
  of the actual `LSeries.term` prefix through 700. Guarded compile and
  three-endpoint standard-axiom audit passed; the
  [χ₇ report](../verification/sol-luna-20260922/genus7_short_upper_certificate.md)
  records its hashes.
- [GenusLunaRun20260923ConductorSevenDeletionFactor.lean](../UnitDistance/GenusLunaRun20260923ConductorSevenDeletionFactor.lean)
  proves the **actual** χ₇ selected-prime deletion factor at the
  certificate point equals the explicit six-factor real product used
  by the rational checker. Guarded compile and a two-endpoint focused
  audit passed with only the standard axioms. The
  [χ₇ report](../verification/sol-luna-20260922/genus7_short_upper_certificate.md)
  records the theorem and source hashes. A separate guarded
  [exact-rational certificate](../verification/sol-luna-20260922/genus7_short_upper_certificate.md)
  bounds the primitive χ₇ value by `11889/10000` and the selected-prime
  correction by `8293/10000`, giving product upper
  `98595477/100000000 < 1`. The actual weighted-prefix transfer is
  now a Lean theorem; the actual tail is checked separately below.
  Primitive positivity and final integration remain open before a coherent
  χ₇ norm bound can be claimed. The checker also passed a guarded
  rerun after adding an explicit rejection of optimized Python execution.
- [ZetaLunaConductorSevenDeletionBoundRun20260923.lean](../UnitDistance/ZetaLunaConductorSevenDeletionBoundRun20260923.lean)
  proves the actual χ₇ six-factor deletion correction is positive and at
  most `83/100`, with a coarse exact rational envelope
  `91651637/110500000`. Guarded compile and four-endpoint focused
  standard-axiom audit passed; the [report](../verification/sol-luna-20260922/conductor7-deletion-scalar-bound.md)
  records hashes and scope. This bound alone does not control the
  primitive L-value.
- [GenusLunaRun20260923ConductorSevenTail.lean](../UnitDistance/GenusLunaRun20260923ConductorSevenTail.lean)
  proves the **actual** primitive χ₇ `LSeries` tail after 700 terms has
  norm at most `2 * 701^(-(12001/12000))`, using the checked zero prefix
  and a shifted Abel bound. Guarded artifact-producing compile and focused
  standard-axiom audit passed; the [report](../verification/sol-luna-20260922/conductor7-tail-lean.md)
  records the source hashes and an earlier missing-`.olean` audit attempt.
  A [primitive-positivity draft](../verification/sol-luna-20260922/zeta-conductor7-primitive-positive.md)
  and a [final norm-integration draft](../verification/sol-luna-20260922/genus7-norm-integration.md)
  remain **unverified**; no χ₇ coherent norm theorem is claimed.
- [ZetaLunaConductorThirteenPrimitivePositiveRun20260923.lean](../UnitDistance/ZetaLunaConductorThirteenPrimitivePositiveRun20260923.lean)
  proves the same primitive χ₁₃ L-function and L-series are positive real
  at the certificate point, by dividing the checked positive deleted
  coherent value by the positive actual selected-prime correction. Both
  endpoints passed guarded compile and standard-axiom audit; see the
  [source report](../verification/sol-luna-20260922/zeta-conductor13-primitive-positive.md).
- [ZetaLunaConductorThirteenFinalNormRun20260923.lean](../UnitDistance/ZetaLunaConductorThirteenFinalNormRun20260923.lean)
  combines the checked actual primitive χ₁₃ real-part bound, positive-real
  witness, exact selected-prime correction and rational product budget.
  It proves the actual coherent χ₁₃ norm is at most the certificate's
  exact rational endpoint below 1, then derives its strictly negative
  coherent-genus log contribution with no numerical premise. Both
  endpoints passed guarded compile and standard-axiom audit; the
  [exact report](../verification/sol-luna-20260922/zeta-conductor13-final-norm.md)
  records source hashes and scope. This is one of 128 coherent factors:
  no upper bound for the other 127 factors or the actual relative product
  follows.
- [ZetaLunaConductorThirteenShortLogSavingRun20260923.lean](../UnitDistance/ZetaLunaConductorThirteenShortLogSavingRun20260923.lean)
  turns that actual norm bound into the strict rational log saving
  `conductorThirteenLogModulus <
  -56646674597605080844758324769/4745938638374004765750000000000`.
  All three endpoints passed guarded compile and standard-axiom audit.
  The [quantitative report](../verification/sol-luna-20260922/zeta-conductor13-short-log-saving.md)
  and [independent chain review](../verification/sol-luna-20260922/genus13-short-lean-chain-review.md)
  record the exact proof and scope.
  The missing upper bound for the other 127 genus terms prevents this
  one-factor saving from lowering the current assembled H allowance.
- [ZetaLunaCompletedChi13LogSavingRun20260923.lean](../UnitDistance/ZetaLunaCompletedChi13LogSavingRun20260923.lean)
  carries the exact χ₁₃ saving through the actual completed-field
  imprimitive log split. With no new premise, its checked theorem bounds
  that log by the other-127 coherent remainder plus the actual relative
  product's log norm, minus the rational saving above. Guarded compile
  and focused standard-axiom audit passed; the
  [report](../verification/sol-luna-20260922/completed-actual-relative-chi13-saving.md)
  states the exact endpoint. Numerical bounds for both remaining terms
  are still needed.
- [ZetaLunaConductorThirteenManuscriptRowRun20260923.lean](../UnitDistance/ZetaLunaConductorThirteenManuscriptRowRun20260923.lean)
  proves the coherent χ₁₃ index maps to publication mask 64, whose
  expected fundamental discriminant is 13. The actual primitive
  character is quadratic mod 13, and its coherent value equals the
  selected-deletion value and the primitive mod-13 L-series times the
  actual deletion factor. Five endpoints passed guarded compile and
  standard-axiom audit. The
  [row-binding report](../verification/sol-luna-20260922/conductor13-manuscript-row64.md)
  checks the external inherited AFE row 64's `D=13` source fields.
  Its stored log enclosure near `−0.069118609` is stronger than
  our Lean short saving near `−0.012`. This mask alignment does not
  equate a prime-dependent literal `genusLinearCoefficient` slot to χ₁₃.
- [MixedLunaRun20260922.lean](../UnitDistance/MixedLunaRun20260922.lean)
  proves the actual nonprincipal ray-bit sign `-1` at the selected prime
  and a signed two-lattice auxiliary theta identity. Guarded compile and
  two-endpoint axiom audit passed. The actual Hecke theta identification
  and reflection remain open.

The follow-on grouped [Euler budget theorem](../UnitDistance/EulerLunaRun20260922Budget.lean)
is a draft: two guarded retries stopped at exit 75 on host memory pressure,
and a later admitted retry reached the 900-second command timeout (exit 124),
all without Lean diagnostics. There is no checked theorem or axiom result.
The proposed conductor-13 `≤1000` draft failed source elaboration; the
periodic partial-sum estimate subsequently compiled as noted above. The
mixed ideal-theta draft lacked a compiled prerequisite, and a lighter
rational-ray follow-on remains unverified after source elaboration errors.
Their exact status is in
[euler-grouped-lean-status.md](../verification/sol-luna-20260922/euler-grouped-lean-status.md),
[genus.md](../verification/sol-luna-20260922/genus.md), and
[mixed-ideal-theta.md](../verification/grok-review-20260922/mixed-ideal-theta.md).

## New external mathematical checks

Independent integer and rational scripts reconstructed the literal field
catalog and 45-prime order-four set, enclosed the order-four saving
\(S_4\) and seven exceptional Euler terms \(B_D\), matched all 1,229
manuscript derivative-floor rows through 10,000, and checked the stored
13,825-bin central-saving interval. The first 2,307 complete central bins
also match a separately regenerated prime census below \(10^7\).
An independent segmented sieve regenerated another 2,306 selected rows:
2,303 complete bins inside \([10^7,10^8)\), both boundary bins and one
complete bin around \(10^{10}\). All counts, reciprocal floors and class
splits matched the stored table. The remaining suffix through \(10^{12}\)
and infinite tail were not regenerated. The checker also passed from the
candidate-14 standalone extraction using its bundled-table fallback.
The derivative calculation has a second route using the Lean-proved coarse
Euler-constant lower bound, which still fits the selected relaxed H ceiling
when the other four manuscript allowances are assumed. The selected Lean
route had already proved its own actual-field prime-debit allowance; the
new script checks the manuscript's separate floor formula.

Four selected Hecke coefficient rows were regenerated: all 981 coefficients
in a mixed quadratic row by complete-vector hash, and 128 coefficients
each in one pure quartic, mixed quartic and mixed octic row. For the mixed
quadratic row, the separate quartic-field calculation derived
\(X^4+34X^2+429\) over \(\mathbb Q(\sqrt{-35})\) and matched direct
root-count traces to the row coefficient at every one of 159 unramified
primes through 981, plus all five eligible prime-square coefficients via
root counts over \(\mathbb F_{p^2}\). The [independent source review](../verification/sol-luna-20260922/quartic-field-review.md)
found no mathematical flaw in either finite trace argument. The checker pins
the coefficient-helper source hash; its guarded recheck passed after this
pin. A second checker used these traces and Euler multiplicativity to
reconstruct all 186 coefficients through 981 supported away from the six
ramified primes; their full-row hash matches the pinned row, with a separate
[source review](../verification/sol-luna-20260922/quartic-composites-review.md).

A further independent finite-prefix checker recomputed all 28,416 first-128
coefficient entries in the 222 new H7 quartic and octic analytic rows,
including 38 rows with quartic phases modulo 5 or 13. The row multiplicities
sum to 260 factors. Guarded source-bound fixture generation, finite-prefix
comparison, and compact simulated-package replay passed. Generation checks
3 arithmetic and 64 moment tables and four Euler receipts by SHA-256; ordinary
replay checks the compact fixture and arithmetic-helper hashes. The
[checker report](../verification/sol-luna-20260922/hecke_all_rows_prefix_review.md)
states the exact families and limitations. These coefficient checks do not
integrate moments, bound analytic tails, or identify every row with its
actual Hecke/Artin factor.

These checks support distinct finite bridges and do not regenerate
the full census suffix, all 836 analytic factor bounds, or the moment
integrations. The original manuscript analytic replay used stored moments;
it is external evidence, not a Lean proof of H.

An independent period-series calculation for the actual primitive quadratic
character modulo 13 gave an exact rational interval contained in
`[0.662607499048622, 0.662915167689497]` at `12001/12000`; the period
tail radius was bounded by `2/13001`. The
[checker and receipt](../verification/sol-luna-20260922/genus13_lvalue_interval.md)
do not prove a Lean numerical bound, identify a pinned analytic row, or
establish the genus aggregate.
An independent Arb Hurwitz-zeta evaluation at 256-bit precision landed inside
that rational interval; it is corroboration, not a replacement certificate.
Applying exact rational corrections at the selected primes further enclosed
the checked common-level conductor-13 L-value in
`[0.932999359249997,0.933432578984470]` and its log modulus in
`[-0.069350764898162,-0.068886542513859]`; see the
[correction report](../verification/sol-luna-20260922/genus13_common_level_interval.md).
The manuscript table gives an aggregate linear allowance, not a pinned
conductor-13 row allowance, so this check does not certify a factor-row
budget or the genus aggregate.

A separate [52-term rational certificate](../verification/sol-luna-20260922/genus13_short_upper_certificate.md)
uses four full χ₁₃ periods, elementary `exp`/`log` inequalities and a
`2/53` tail bound to put the selected-prime-deleted value strictly below
`1`. Its exact upper bound is
`4689291963776399684905241675231/4745938638374004765750000000000`,
leaving margin
`56646674597605080844758324769/4745938638374004765750000000000`.
The guarded script passed and is independent of the 13,000-term interval
routine. Candidate 14 ships this external checker, receipt and report.
The checked Lean research modules above now separately prove the same
actual coherent χ₁₃ upper outside candidate 14's selected proof closure.
A separate
[source-level mathematical review](../verification/sol-luna-20260922/genus13_short_upper_certificate-review.md)
checked its finite inequalities, shifted-tail bound, correction directions
and sign case, and found no substantive flaw. Its Lean-source hash binding
is conditional when those source files are absent from an extraction.
The independent [budget-scope assessment](../verification/sol-luna-20260922/genus13-budget-scope.md)
shows exactly how a χ₁₃ norm bound below 1 yields a negative term in the
coherent 128-character genus log, while leaving the full genus allowance and
the assembled H endpoint unchanged: the other 127 log contributions lack a
separate upper bound. The later checked mask-64 binding identifies the
publication character row, but the new Lean short saving is weaker than
that row's stored numerical enclosure and no fixed primewise literal
`genusLinearEulerValue` slot is identified.

A second [χ₇ exact-rational certificate](../verification/sol-luna-20260922/genus7_short_upper_certificate.md)
uses 700 terms and a `2/701` Abel tail to put the selected-prime-deleted
mask-17 value below `98595477/100000000`, with exact positive margin
`1404523/100000000`. It source-binds to the checked actual χ₇
character/conductor/prefix module. The checker passed under the guard;
its checked actual tail, finite-prefix upper, deletion-factor identity,
and coarse `83/100` correction bound have not been combined into a Lean
norm theorem. Primitive positivity is still open. Its
[independent source review](../verification/sol-luna-20260922/genus7-short-review.md)
found no rational-bound direction error; the checker's initial optimized-mode
execution caveat was fixed and the revised source passed a guarded rerun.
The other genus terms and (H) remain open.

For the same mixed quadratic row, a separate
[direct AFE checker](../verification/sol-luna-20260922/numerics_afe_one_factor.md)
used Arb exponential-integral weights and an elementary divisor-bound
tail. Its guarded full-source and compact-fixture runs passed, with computed
bad-factor-removed log upper approximately
`0.04824325652403731253668746`, below the pinned printed row allowance
`0.04824325652403731259195653`. An
[independent source review](../verification/sol-luna-20260922/afe-one-factor-review.md)
checked the formula and interval direction. This is one conditional factor
bound: row identification, conductor, functional equation, root-number
modulus, bad factors and the global coefficient bound are inputs. The other
factor evaluations are not regenerated by this run.

A second [direct pure-quartic AFE check](../verification/sol-luna-20260922/numerics_afe_pure_quartic_direct.md)
generated all 1,921,920 coefficients of one sector-1920, twist-minus-one
row from independently implemented local residue rules, matched the
pinned per-bin counts, absolute masses and zeroth moments, and evaluated
the four-Gamma Mellin kernel pointwise at its 26,785 nonzero coefficients.
The guarded corrected run passed: its bad-factor-removed log upper is
about `0.056343705003318770013297083706909639`, below the printed
row allowance by about `2.3301684e−25`. Two prior guarded runs failed
a raw `A_finite` overlap check because the stored A/B values are
polynomial-center approximations with a separate interpolation allowance;
the corrected checker uses that allowance only to check center consistency,
while its final upper uses the direct pointwise sums and its independent
tail. An [independent source review](../verification/sol-luna-20260922/numerics-afe-pure-quartic-direct-review.md)
checked the coefficient rules, AFE weights and tail directions. The
direct method reuses the pinned four-Gamma kernel and assumes the stated
functional equation, conductor, root number, coefficient majorant and
row identity. It is a second-factor cross-check, not a proof of (H).

## Remaining work and run controls

The essential missing mathematical step is still a verified upper bound for
the completed-field imprimitive log zeta (equivalently the fixed-field H
inequality after the proved corrections). To follow the five-family route,
connect all actual Artin/Hecke local factors and nonvanishing to the
completed-field product, identify the stored coefficient/moment data with
those factors, prove their directed numerical enclosures, and bring the
central-census suffix under an adequate verified bound. The new log bridge
reduces the formal interface at this point; it does not discharge those
premises. A complete unconditional result remains open.

Expensive Lean, export and numerical jobs were serialized through the master
`automation/lean-formalization/guarded_build.py` lock, with 10 GiB
admission, a 4 GiB low-memory stop and a 900-second per-job timeout.
Lean used the pinned toolchain, one thread and `-M6144`; the inherited
disk-backed TMPDIR was retained. Exit 75 is resource deferral, not a
mathematical failure. Six GPT-6 Luna workers were used with fresh initial
context and separate source ownership. Per-agent token or cost usage was
not exposed by the collaboration status interface; checked files and
receipts provide the evaluation record. Archived sources, earlier sealed
packages and unrelated working-tree edits were preserved.

Three brief exploratory numerical calculations occurred outside the guard:
an initial four-second census-prefix check before adopting the shared
helper, a reviewer's 0.4-second read-only AFE corroboration, and a small
exact-Fraction χ₇ feasibility calculation before its guarded certificate.
A later preliminary
one-second row-64 Lean axiom audit also ran directly by mistake; it was
rerun successfully under the guard, and only the guarded audit is counted.
The subsequent guarded replays are the counted verification receipts.
No unrelated process or resource cap was changed.

Remote publication, Palomar submission and registration remain for the
owner. Any later candidate should be exported afresh, compared to
verifier-passed archive 07 for proof-input identity, and given an honest
scope statement. The selected conditional theorem can be submitted as
such; its numerical hypothesis must remain prominently disclosed.
