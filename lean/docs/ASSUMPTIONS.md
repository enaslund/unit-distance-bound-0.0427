# Mathematical assumptions

Each Lean theorem assumes one explicit numerical inequality. None is proved
in Lean. Each is an explicit hypothesis of its theorem, not an added axiom or
a Boolean flag, and the fields, zeta functions, logarithmic derivatives and
constants have their ordinary mathematical meanings. The proofs otherwise use
only `propext`, `Quot.sound` and `Classical.choice`.

## H_W: the hypothesis of the 1.04315 theorem (version 2)

The theorem `UnitDistanceSqrt241Submission.target_of_wide_zeta_bound`, stated in
[ChallengeZeta241.lean](../ChallengeZeta241.lean) and proved in
[SolutionZeta241.lean](../SolutionZeta241.lean), gives finite planar sets with
both cardinality and the number of unordered unit pairs divided by
`|U|^(20863/20000)` tending to infinity. There is no assertion for every
sufficiently large cardinality.

Let `B = ℚ(√241)`, let `E` be the genus field of degree 512 described under
H241 below, and let `E_W = E(√β₁, √β₂, √β₃, √β₄)` for the four elements
`β_i ∈ E` of the Challenge (`CanonicalWide.wideRadicand`), written in terms of
`√241` and products `√a_i = rootA i`, `√b_i = rootB i` of the square roots of the
eight Kummer radicands. Each `B(√a_i, √b_i, √β_i)` is a dihedral extension of `B`
of degree 8, the field of the dihedral forms 24, 20, 17, 7 of
`papers/0.043171/certificates/dihedral/d4all27.json`; these four forms span the
space `W''` of the paper (Section 5), and `E_W` has degree 8192 over `ℚ`
(`Wide.finrank_field`). With `ℓ = (9/4) log 2 + (1/2) log 3615`, the hypothesis is

```text
log(Re ζ_{E_W}(1 + 1/4411))/8192
  + (1/4411) * ((ℓ − γ − log(4π))/4 − Re(logDeriv ζ_{E_W} 2)/8192)
  < 50969/1000000.
```

The evidence is outside Lean.
`papers/0.043171/certificates/dihedral/h_w_receipt.py` bounds the left side by
`0.0509171473`, below the threshold `0.050969` with slack `5.2·10⁻⁵`: the first
term is the certified value of `log ζ_{E_W}(4412/4411)/8192` from the
factorization of `ζ_{E_W}` into `ζ_E`, 448 Hecke L-functions of degree 4 and 128
of degree 8 (Sections 5 and 6 of the paper), and the logarithmic derivative at 2 is bounded above prime by
prime from lower bounds for the residue degrees in `E_W/B` up to norm `10⁶` and an
explicit tail. These are certified numerical computations, not proofs in Lean.

The planar theorem itself, the infinite 41-cap tower over `B`, its fields and
their local types, the field `E_W` with its degree, its embedding in the fixed
base `M` and its local data, the passage from H_W to the analytic ceiling, the
numerical margin and the planar construction are proved in Lean.

## H241: the hypothesis of the 1.0427 theorem (version 1)

Version 1 of the Palomar entry registered this theorem. Its endpoint modules were
removed from the current sources when the witness changed to the 41-cap tower
(version 2); it remains in the history of this repository and at the commits
cited by version 1. The genus field `E` defined here is also the base of `E_W`.


The theorem `UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound`,
stated in version 1 of `ChallengeZeta241.lean` and proved in version 1 of
`SolutionZeta241.lean`, gave finite planar sets with
both cardinality and the number of unordered unit pairs divided by
`|U|^(10427/10000)` tending to infinity. There is no assertion for every
sufficiently large cardinality.

Let `B = ℚ(√241)` and let `E` be the field generated over `ℚ` by `√241` and
square roots of the eight elements of `B` listed in the Challenge
(`radicandA`, `radicandB`): `−1`, `−71011068 + 4574225√241`,
`(−6101 − 393√241)/2`, `(6101 − 393√241)/2`, `31 − 2√241`, `31 + 2√241`,
`326 − 21√241` and `326 + 21√241`. They form a basis of the `{2,3,5}`-units of
`B` modulo squares, and `E`, of degree 512, is the genus field of the tower.
With `ℓ = (9/4) log 2 + (1/2) log 3615`, the hypothesis is

```text
log(Re ζ_E(1 + 1/300))/512
  + (1/300) * ((ℓ − γ − log(4π))/4 − Re(logDeriv ζ_E 2)/512)
  < 852/10000.
```

The evidence is outside Lean. `ζ_E` is `ζ_B` times the Hecke L-functions of
the 255 nontrivial quadratic characters of `Gal(E/B)`, and
`papers/0.04273/certificates/h241_receipt.py` bounds the left side by
`0.0848335193` from certified approximate functional equations for these
L-functions and an Euler product with explicit tail. An independent
recomputation with PARI's Hecke L-functions (all 256 characters, functional
equations checked) gave `0.0848334667`, leaving slack `3.665·10⁻⁴` below the
ceiling. See [sqrt241/SUBMISSION.md](sqrt241/SUBMISSION.md) and
[sqrt241/REVIEWS.md](sqrt241/REVIEWS.md).

## H: the hypothesis of the 1.0418235 theorem

This ledger was last revised for this theorem on September 27, 2026. The
research modules, records and run ledgers it cites that are not linked were removed
from the tree in the September 29, 2026 reorganization; they are at the tag
`pre-merge-2026-09-29`. The selected endpoint is
`UnitDistance.target_of_canonical_sharper_zeta_bound`, independently restated
in [ChallengeZeta.lean](../ChallengeZeta.lean) and proved in
[SolutionZeta.lean](../SolutionZeta.lean). It gives finite planar sets with
both cardinality and the number of unordered unit pairs divided by
`|U|^(2083647/2000000)` tending to infinity. The exponent is **1.0418235**;
there is no assertion for every sufficiently large cardinality.

### The hypothesis

Let `K = CanonicalRetained.Carrier` be the independently defined nineteen-radical
field, `d = 524288`, `δ = 1/12000`, and
`ell = (9/4) log 2 + (1/2) log 15015`. The hypothesis is

```text
log(Re ζ_K(1 + δ))/d
  + δ * ((ell − γ − log(4π))/4 − Re(logDeriv ζ_K(2))/d)
  < 42165819/1000000000.
```

**H is unproved in Lean.** It is an explicit hypothesis of the theorem,
not an added axiom or a Boolean flag. The field, zeta function, logarithmic
derivative and constants have their ordinary mathematical meanings. The
[conditional submission account](CONDITIONAL_SUBMISSION.md) gives the exact
radicals, normalization and positivity/analytic justification. Its selected
proof establishes the sufficient pair integral, discriminant estimate,
infinite arithmetic construction, local conditions, analytic transfer and
planar sequence internally, with only `propext`, `Quot.sound` and
`Classical.choice` as transitive axioms.

The ceiling is **0.042165819**, relaxed by `4e-6` from the earlier
`0.042161819` checkpoint to accommodate the checked pair bound. The exponent
is unchanged. The manuscript gives an external computer-assisted argument
for H. Its five-allowance upper certificate is
`0.04216181893948094953138458`, leaving
`0.00000400006051905046861542` below this ceiling. This is slack in an upper
bound, not an uncertainty interval or a measured value of H. A later replay
of the finite assembly obtains `0.0421618189394842`; stored moments and
census were hash-checked rather than regenerated by that replay. See the
[external-proof account](../verification/external-zeta-20260921/README.md)
and [September 22 replay](../verification/external-zeta-20260922/README.md).

### Checked sufficient conditions and research interfaces

The completed-field approach separates an analytic estimate in the
**degree-16384 completed field** from exceptional Euler corrections and
prime savings for the **degree-524288 retained field K**. These are distinct
fields. The following are useful sufficient conditions and intermediate
results; any valid argument proving the displayed H could replace this
approach. Research modules mentioned here are outside the selected
Challenge/Solution import closure.

| Component | Checked result | Unproved input or limit |
| --- | --- | --- |
| Actual prime support | The 1,000-prime support and its actual field-index consequences give saving at least `2231824/10^11` (earlier 100-prime value `1529823/10^11`). The common arithmetic audit covered 89 owned declarations. | Larger externally checked support has no Lean certificate. |
| Stronger completed-field budget | `target_of_support1000_and_improved_completed` and its 11-declaration audit pass. A completed-field log contribution, after the selected Euler terms, at most `42965707/10^11` suffices for the same planar target with the 1,000-prime support. | That analytic inequality remains a premise; SolutionZeta still uses exactly H. |
| Actual relative aggregate | A checked interface reduces the analytic budget to actual coherent genus log at most `7.337578130846530221` and actual completed/genus relative log norm at most `-0.040875140862019542`. | Both numerical inequalities remain open. The interface neither assumes nor establishes the quotient's identification with all 836 listed analytic rows. |
| Genus structure | Actual root number `+1` is proved for all 128 primitive genus characters, as are coherent-product/deletion identities and an all-integer product of lifted primitive atoms, including nonunits. | The explicit atom-to-Legendre/Kronecker/Conrey formulas and actual row inequalities are not supplied by these structural lemmas. |
| Individual genus bounds | The September 22 conductor-five theorem bounds one actual primitive value at `12001/12000` by `722247/1666250 + 10^-24`. The preceding September 22–23 run proves a conductor-13 coherent actual norm below one and its completed-field connection. | χ5/χ7 integration and the complete 128-row Lean numerical table remain unfinished. The χ13 saving is weaker than its manuscript row and is not an additional saving against the existing certificate. |
| Exact receipt arithmetic | Checked rational comparisons and aggregate leaves verify arithmetic on specified interval endpoints. A generic multiplicative prime-power bound implies `|a_n| ≤ d₂(n)`. | Actual analytic enclosures and row-specific prime-power bounds are separate premises. |

### September 24 completed-sector progress

Focused Lean 4.32 research checks outside the selected submission closure now
factor the **actual** completed/genus deleted zeta quotient into its 127
distinct quadratic character fields for real `s > 1`, using the certificate's
exact seven-prime deletion set. The corresponding exact logarithmic sum is
connected to the existing actual relative Euler expression at
`s = 12001/12000`. Every sector field has degree 256 over `ℚ` and degree two
over the actual genus field. The checked source is
`CompletedDeletedSectors20260924.lean`,
with its proof and audit scope recorded in the
sector progress record.
These `../research/` links locate checkout-side work; the selected candidate
archive contains this assumption account but does not include or build the
research modules.

The checked mask-60 squareclass bridge identifies the actual H6 genus
extension with one of those 127 sector fields. Consequently the actual
relative log equals twice the sum of the 32 literal H6 quartic/base deleted
logs plus the other 126 sector logs. The exact theorem is
`H6CompletedSectorBridge20260924.actualRelative_log_eq_h6_rows_add_remaining`;
its successful focused check and five standard-only audits are recorded with
source hash `83b0723edfb11e56a95cc065a3b4efed2691d65a41960a69ae1d64703c5c6a37`.
The H6 rows are thereby placed inside the actual aggregate, but no analytic
enclosure for that sum follows.

The finite 127-sector classifier exhaustively lists the obstruction forms
`q_m` and their largest totally singular subspaces. A separate focused Lean
check identifies each `q_m` with the **actual rational Galois square map**
on its degree-256 radical sector field: an explicit enumeration covers all
256 automorphisms and proves that a lifted automorphism squares to one
exactly when `q_m` vanishes on its genus vector. This is an arithmetic
interpretation of the finite classification, not a conductor or Artin-row
bound. The source is
`CompletedSectorSquareForms20260924.lean`,
SHA-256 `56134b0a3f4cc00048da8a458b43cf15b753107980666679b0dcbc3459986f74`,
with four standard-only axiom audits in its successful focused check.

Two further focused checks turn this form calculation into field structure.
`CompletedSectorOrderFour20260924.exists_order_four` proves that every actual
rational sector Galois group has an element of order four, so none of these
degree-256 sectors is a multiquadratic rational extension.
`CompletedSingularInducingFields20260924` constructs, for any binary subspace
`W` on which `q_m` vanishes, an actual intermediate base `B_W` inside the
genus field, proves `[F:B_W]=|W|` and `[E_m:B_W]=2|W|`, and proves the latter
extension group is elementary abelian. These are structural results; a Lean
finite certificate connecting the classifier's maximal choices of `W` to all
127 sectors and an analytic induction/row identity are still pending.

The numerical inequality H remains open. In particular, an exact map from
the remaining sectors to the low-degree H6/H7/mixed analytic rows, their
conductor and functional-equation data, and certified bounds for the resulting
relative sum have not been established in Lean. These focused checks do not
constitute a fresh full 4.35 build or a Palomar verifier pass.

The [September 21 arithmetic receipt](../verification/cleanup-20260921/arithmetic/README.md),
[actual-relative budget](../verification/sol-luna-20260923/relative-aggregate-budget.md),
[checked atom expansion](../verification/sol-luna-20260923/primitive-atom-expansion-light.md),
[χ13 norm](../verification/sol-luna-20260922/zeta-conductor13-final-norm.md),
[χ13 completed-field connection](../verification/sol-luna-20260922/completed-actual-relative-chi13-saving.md),
and [χ13 scope](../verification/sol-luna-20260922/genus13-budget-scope.md)
record their exact declarations, audits and limits.

### External numerical evidence and the remaining gap

The September 23 work supplies new finite evidence: all 128 genus characters
and 677,376 period values; all 32 H6 quadratic expint rows; an independent
PARI actual-field check of 164,712 coefficients and 224 exceptional factors;
387,955 eligible primes and 6,716 bins; and one complete H7 octic moment
row. The [numerical evidence table](CONDITIONAL_SUBMISSION.md#what-the-evidence-establishes-as-of-september-23-2026)
separates their algorithms, shared backends, conditional analytic premises
and archive boundaries. The [detailed handoff](CONDITIONAL_HANDOFF_SOL_LUNA_20260923.md)
retains the individual receipt paths and failures.

The expint checks pass all 32 H6 frozen row bounds under the stated analytic
premises. The earlier SplitKernels failure on one frozen row remains valid
as a method-specific result. Exact aggregate replacement preserves the
existing rounded five-family ceiling; it proves no new analytic enclosure
and changes no exponent.

Paper local/conductor arguments provide a route from actual H6 quartic
quotients to the required Euler products and relative Hecke analysis.
They correctly distinguish relative conductor norms from rational conductors
`35·429·4^e`. A fresh all-32 PARI discriminant check has no successful
receipt. Checked research modules now place the H6 extension and all 32
quartic twists in the completed field, identify the 64 H6 character fixed
fields, and prove the paired quartic quotient identities; see
the H6 progress record.
The checked local permutation-factor module reduces actual prime-fiber
denominators to cycle factors under explicit unramified Frobenius data and
assembles the H6 character polynomial conditionally. A further checked
module identifies the order of actual arithmetic Frobenius with residue
degree at unramified primes. The checked Frobenius-restriction and
quartic-restriction modules now identify trivial restriction with vanishing
of the paired character for all 64 actual quartic embeddings. Assuming
the actual prime is unramified in the common field, its literal quadratic
prime sign equals that character's sign on actual Frobenius. The latest
module has three clean standard-axiom audits in the
focused Lean 4.32 check;
the progress record gives its source hash and exact theorem names.
The actual unramified local-denominator assembly is now checked in
`H6UnramifiedLocalDenominator20260923.lean`, with all 64 literal quadratic
prime signs and no separate coefficient-identification premise. Its two
division corollaries explicitly assume the relevant denominator is
nonzero; all three audits are standard-only in the
focused check.
The later rational-prime and support modules prove the actual 64-to-32
grouping and unramifiedness outside `Σ={2,3,5,7,11,13}`. The checked
`H6DeletedEulerProduct20260923.h6_sigmaDeletedZeta_identity_real` now proves
`ζ_L^Σ/ζ_F^Σ = ∏D (ζ_KD^Σ/ζ_B^Σ)^2` for real `s>1`, with no unproved
factorization premise. All five printed audits in the
successful global check
use only `propext`, `Classical.choice`, and `Quot.sound`. The checked source
SHA-256 is
`8485e259ae23338c214266692bc0e7f7926f47c95351537ccb04087712f0de9d`;
the progress record gives the exact five theorem names and the earlier
failed-check diagnostics separately.

The certificate's deletion set also contains 17. The exact seven-prime
specialization is now checked in
`H6SelectedDeletedProduct20260923.h6_selectedImprimitiveValue_identity`,
with the existing real `rationalPrimeImprimitiveZetaValue` and actual
`selectedRationalPrimeSet`, for real `s>1`. Its five audits in the
successful check
are standard-only, with no warnings or errors; source SHA-256 is
`d7e32ea29ac1c817dcab6669b88f52eb44bb2ac4457f35f9710d1ffb42a1f188`.
The first two failed replay logs are preserved separately. This theorem
does not require the separate open ordinary ramified-correction identity.
It does not place the entire
completed/genus quotient into the H6 sector: the checked degree calculation
rules out that identification, and 126 other sectors remain. The full
aggregate decomposition and analytic bounds are still unfinished. These
H6 results and earlier finite matching do not prove the
all-prime identities, continuation, functional equation, growth, AFE tails,
remaining H7/mixed factors or derivative debit needed for H. The selected
conditional theorem has no extra hidden premise for any of these routes.

### Evidence and package boundary

At the September 27, 08:04 UTC package checkpoint, candidate23's deterministic
export and archive-only metadata gate passed for PalomarSubmission revision
`a59f25bd8a66bf6faf3a4f4260d412989c0185ea`; the archive SHA-256 is
`a8b47796a275a598e2be85c9f6d4e28b560782047b4b7d6e8ea6c5c3f3d7132d`. This is packaging and metadata evidence only: it includes no full build,
axiom check, independent checker, kernel replay, or H proof result. Candidate22's
archive-only gate also passed; candidate21's preserved gate failed metadata
because its wrapper omitted the explicit policy revision. Candidate20 retry2
stopped at 148,000/149,249 checks when host available RAM measured 3.423931 GiB
(<3.5 GiB), exit 75 with no cgroup OOM. This was an incomplete infrastructure
stop, not a proof verdict. H remains unproved. See [reproduction and
receipts](PALOMAR_REPRODUCE.md) and the live run
ledger.

The [final handoff](FINAL_HANDOFF_SOL_LUNA_20260923.md),
[September 23 detailed handoff](CONDITIONAL_HANDOFF_SOL_LUNA_20260923.md),
[preceding run handoff](CONDITIONAL_HANDOFF_SOL_LUNA_20260922.md), and
[September 21 handoff](CONDITIONAL_HANDOFF_20260921.md) preserve historical
checkpoints. In the research repository, `lean-formalization/STATUS.md` is
the current status; the research modules and their map
(`lean-formalization/research/README.md`) are at the tag `pre-merge-2026-09-29`. Those repository maps are separate from this exported
package. Dated plans and host limits are historical context, not restrictions
on which mathematical methods may be used next.
