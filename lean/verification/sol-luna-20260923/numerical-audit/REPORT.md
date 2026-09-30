# Independent AFE numerical audit (2026-09-23)

## Scope and result

Three conditional single-row AFE bounds were freshly replayed with outward Arb intervals, and each direct upper lies below its pinned printed row endpoint. For H6 mask 1586 twist +1, the pointwise `SplitKernels` row comparison remains **FAIL**; a distinct Arb expint-kernel replay and a 32-row expint batch at target sigma pass their row endpoints, and the exact target aggregate substitution separately **PASSES**. The H6-only aggregate replacement at sigma 6001/6000 also passes its cap. A segmented checker independently matches all 544 moment bins for one H7 octic row; it does not replay that row's AFE endpoint.

The pointwise AFE checks are **replays of the September 22 direct-check
scripts**, not new analytic kernels or interval backends. They recompute the
stated coefficient contractions without using the stored moment-bin
interpolation to obtain those endpoints, but reuse the pinned `SplitKernels`
or four-Gamma kernel and Arb implementation. Their row-specific assumptions
and comparison modes are described below.

An additional finite arithmetic audit independently reconstructs the first
3,922 coefficients of the H6 mask-1586 twist-`+1` row from PARI/GP
maximal-order prime decompositions of the proposed quartic/base-field zeta
quotient. All coefficients and seven explicit local factors match; this is
finite coefficient evidence, not an all-prime identity or a new AFE check.
See [`h6-quartic-zeta-quotient-report.md`](h6-quartic-zeta-quotient-report.md)
and its source-only [`all32 plan`](h6-quartic-zeta-quotient-all32-plan.md).

| Row | Independent upper | Printed upper | Approximate slack |
|---|---:|---:|---:|
| H6 quadratic, mask 1586, twist -1 | `0.048243256524037312536687462524286013` | `0.048243256524037312591956533323098958` | `5.52698e-20` |
| H7 pure quartic, sector 1920, twist -1 | `0.056343705003318770013297083706909639` | `0.056343705003318770013297316723754411` | `2.33017e-25` |
| H7 mixed quartic, mask 274, twist +1 | `-0.0198192193582759991782967947679641976` | `-0.0198192193582759949380506491625471806` | `4.24025e-18` |

The fresh machine-readable intervals are in [`quadratic_h6.log`](quadratic_h6.log), [`pure_quartic_afe.log`](pure_quartic_afe.log), and [`h7_mixed_quartic_direct.json`](h7_mixed_quartic_direct.json). The quadratic replay regenerated all 981 coefficients and matched the complete pinned coefficient-vector hash. The pure quartic replay generated all 1,921,920 coefficients, checked the first 128 against its pinned row, matched every pinned moment bin, and evaluated the pointwise kernel at all 26,785 nonzero coefficients. The mixed quartic replay reconstructed its full coefficient vector and checked the pinned prefix and all 306 bins before its pointwise kernel sum.

The quadratic check evaluates the degree-two exponential-integral weights directly with Arb and bounds both omitted tails from `|a_n| ≤ d₂(n) ≤ 2√n`. The quartic check evaluates each finite term through the pointwise four-Gamma Mellin kernel and bounds both omitted tails using the degree-four divisor majorant, `β=5/4`, and `ζ(β)^4`. It does not use the printed degree-40 moment-bin interpolation to obtain the AFE endpoint. The direct quartic replay does reuse the pinned four-Gamma kernel implementation, so it does not independently prove that implementation's residue-series enclosure.

The additional H6 mask-1586 twist-`+1` pointwise `SplitKernels` replay at
`sigma = 6001/6000` remains a strict row-comparison **FAIL**: its direct
upper exceeds the frozen endpoint by `4.4446443000903371223298219522882226312e-26`.
The H6-only aggregate replacement is a separate **PASS**, with
`8.9287764792885897e-24` slack, at that sigma only. At the target
`sigma = 12001/12000`, the same `SplitKernels` method also has a strict row
comparison **FAIL**; an independent expint-kernel replay passes the target
row endpoint, and an exact target aggregate substitution separately passes.
See the H6 row section and cross-sigma note below.

## Assumptions and limits

These are finite numerical cross-checks of stated rows, not a proof of the fixed-field hypothesis (H), a global factorization theorem, or all 836 non-linear factor allowances. Each AFE application remains conditional on the row being the intended factor, its conductor/gamma data and removed Euler factors being correct, the stated functional equation, and its global coefficient bound. The degree-two rows use `|a_n|≤d₂(n)`; quartic checks use the corresponding degree-four majorant and `ζ(β)^4` tail where stated. The H7 mixed-quartic row also uses its pinned root number `+1`. The octic segmented moment check verifies finite stored moment data only. Finite coefficient agreement does not prove the global coefficient bounds or factor identifications.

The pointwise AFE replays used `python-flint 0.9.0`, linked FLINT `3.6.0`, and outward Arb ball arithmetic. The independent coefficient recurrence checker and row fixtures are included in this directory; source tables and analytic kernels are pinned by SHA-256. The full 836-factor target-sigma replay is a separate September 22 receipt, not a new run in this audit; its relation to the local H6 cross-sigma failure is recorded in [`h6-row-cross_sigma-transfer.md`](h6-row-cross_sigma-transfer.md). The full prime census was not regenerated by these local checks.

## Reproduction

This launcher reproduces the first two table rows only. The H7 mixed-quartic
and H6 twist-`+1` row checks, aggregate substitution, and segmented octic
moment replay have their own scripts and receipts below.

From the repository root, run:

```sh
python3 automation/lean-formalization/guarded_build.py --timeout-seconds 900 -- python3 lean-formalization/verification/sol-luna-20260923/numerical-audit/replay.py
```

The successful guarded run admitted at 17.6 GiB host memory available and 1.60 GiB cgroup headroom. It ran serially: quadratic 0.386 seconds, pure quartic 41.758 seconds, total numeric replay 42.144 seconds. A preceding attempt was deferred (exit 75) before starting because the shared lock was busy / cgroup headroom was below the admission threshold; it produced no numeric result. The successful run completed with exit 0. See [`usage.json`](usage.json).

## H7 mixed-quartic row replay

A third row was replayed pointwise: H7 sector mask 274, twist +1, degree 4, gamma [0,0,1,1], conductor 577152576, root number +1, sigma 12001/12000, and cutoff N=192193. The checker reconstructed every coefficient, matched the arithmetic/moment first-128 prefixes, checked all 306 exact moment bins and the total 2,255 nonzero coefficients, then performed pointwise Taylor-kernel summation rather than the stored bin contraction.

| Quantity | Direct replay | Frozen row |
|---|---:|---:|
| Primary finite sum A | 1.4973027059302169069426 | source center interval, checked after interpolation debit |
| Dual finite sum B | 0.0809799315704986563595 | source center interval, checked after interpolation debit |
| One-side interpolation debit | 7.66961936581169040739628746177900203e-25 | 7.6696193658116904073962874617790020e-25 |
| One-side tail, beta 5/4 | 2.62531192310572662201584102691958938e-11 | 2.6253119231057266220158410269195894e-11 |
| Bad-factor multiplier | 0.621166239140794364485531788864224213 | interval overlap passed |
| Final log upper for L_S | -0.0198192193582759991782967947679641976 | printed upper -0.0198192193582759949380506491625471806 |

The direct log upper is below the printed upper by 4.2402461456054170e-18. Both direct finite sums are contained in their frozen center intervals expanded by the frozen interpolation allowance. The direct interpolation remainder is no larger than the frozen allowance, the tail intervals overlap, and the direct bad-factor product overlaps the frozen multiplier interval. The complete machine-readable enclosure is h7_mixed_quartic_direct.json.

This is a pointwise coefficient-contraction cross-check, but it reuses the pinned nonpositive-afe.py quartic SplitKernels, its Taylor remainder proof, and the python-flint/Arb interval backend. It is conditional on the mixed-quartic row's conductor/gamma/root number and functional equation, the global finite-image bound |a_n|≤d₄(n), and the completeness of the seven bad-prime factors. It does not prove H, the factor identification, or the all-n coefficient bound.

## H6 mixed-quadratic row: failed strict endpoint and aggregate replacement

The additional mask 1586, twist +1 degree-two row was replayed pointwise at
sigma 6001/6000 (Q=240240, N=3922, 562 nonzero coefficients, 184 exact
moment bins). All 3,922 coefficients were reconstructed; their complete
signed-vector hash matched
`245989a787ca8bfa916c030bff304a9337365c62e5d7bd4ed1d7fad2aa1ff489`.
The pointwise A and B intervals lie within the frozen center intervals after
the frozen interpolation debit, the tail intervals overlap, and the bad
factor multiplier intervals overlap. The row comparison itself is a **FAIL**
and remains so in [`h6_mixed_quadratic_direct.json`](h6_mixed_quadratic_direct.json):

| Endpoint | Exact outward upper (decimal display) |
|---|---:|
| Direct pointwise log upper | `0.133316063778537035184834794656877152` |
| Frozen row allowance | `0.13331606377853703518483475021043415` |
| Direct minus frozen | `4.4446443000903371223298219522882226312e-26` |

The failure is the endpoint comparison only: the direct interval bound is
slightly looser than the frozen moment-contraction allowance. It does not
indicate inconsistent A/B values or tail/factor data, and the pointwise upper
still bounds the row under the conditional assumptions. The replay reuses
the pinned quadratic SplitKernels/Taylor remainder and Arb backend; its global
coefficient bound `|a_n|≤d₂(n)`, functional equation, row identification,
root number, conductor/gamma data, and completeness of removed factors remain
assumptions.

A separate exact-rational calculation replaces just this one individual
degree-two factor in the published H6 low-degree sum. Its factor multiplicity
is 1, and its Artin weight is 2 in field degree 8192, so the normalized
increment is `(direct−frozen)/4096 = 1.0851182373267425e-29`. The recomputed
H6 normalized upper is strictly below the published cap
`-0.00004864998064564819068`, with exact remaining slack
`8.9287764792885897e-24`. Thus the aggregate replacement check is **PASS**
even though the individual frozen-row comparison stays **FAIL**. The exact
fractions, standard-library `Fraction` method, multiplicity, source hashes,
and both statuses are in
[`h6_aggregate_replacement.json`](h6_aggregate_replacement.json); reproduce
with `python3 lean-formalization/verification/sol-luna-20260923/numerical-audit/h6_aggregate_replacement.py`.

This pass concerns only the twelve-sector H6 low-degree aggregate at sigma
6001/6000. The consolidated five-family analytic receipt is at sigma
12001/12000, so this row cannot be substituted into that receipt directly;
no five-family result is claimed. Neither calculation proves H or discharges
the global analytic assumptions.

The source-only analysis of this sigma gap and the subsequent target-sigma
replay are in [`h6-row-cross_sigma-transfer.md`](h6-row-cross_sigma-transfer.md).
The off-sigma `6001/6000` **FAIL** cannot itself be transferred to or change
the target receipt, which uses a separately evaluated `12001/12000` endpoint.
The direct target-sigma replay also has a strict row-comparison **FAIL**;
separately, replacing that endpoint in the full target mixed-quadratic
group passes its exact aggregate allowance, as detailed below.

The follow-up pointwise replay at the actual target sigma has strict row
comparison **FAIL** by `4.4458065915680757e-26`; the exact-rational replacement
in the full target mixed-quadratic allowance nevertheless **PASSES**, retaining
`9.191335284030761e-19` group-rounding slack and leaving the displayed
`1.0418235` ceiling unchanged. The first interpolation-consistency failure,
full target-receipt hash binding, exact aggregate arithmetic, and guard
resource record are documented in
[`h6-target-sigma-direct-report.md`](h6-target-sigma-direct-report.md), with
the direct receipt in
[`h6_target_sigma_direct.json`](h6_target_sigma_direct.json) and replacement
receipt in
[`h6_target_aggregate_replacement.json`](h6_target_aggregate_replacement.json).

The independent expint-kernel replay at the target sigma **PASSES** the frozen
row endpoint. It derives weights directly from the `[0,1]` gamma factor and
uses elementary `d₂` exponential tails, without `SplitKernels`. It checked
all 3,922 coefficients, their complete signed-vector hash and all 184 moment
bins; both finite sums pass center consistency checks, the signed lower bound
is positive, and the bad-factor interval overlaps the target. Its direct log
upper is `0.13334973905073891147460919318615529122`, below the target endpoint
`0.13334973905073891150817973756808417` by the exact positive margin recorded
in [`h6-target-sigma-expint-report.md`](h6-target-sigma-expint-report.md),
with formulas and provenance in
[`h6-target-sigma-expint-plan.md`](h6-target-sigma-expint-plan.md) and the
receipt [`h6_target_sigma_expint.json`](h6_target_sigma_expint.json), SHA-256
`56aa4b9fddbe580d852119f79329635c06630d2833315857b581fe1aa0bb4e2f`. This is
a separate method-specific **PASS**; it does not relabel the
`SplitKernels`-method **FAIL**. The expint formula review identifies the
Dirichlet-series identity and contour-growth assumptions needed in addition
to the functional equation; see
[`h6-expint-formula-independent-review.md`](h6-expint-formula-independent-review.md).

The expint run used the guarded slot, admitted with 15.1 GiB host memory and
1.81 GiB cgroup headroom, and completed in 0.359655 seconds. Peak RSS was not
reported. The formula, assumptions, source pins, output, and guarded command
are recorded in [`h6-target-sigma-expint-plan.md`](h6-target-sigma-expint-plan.md).
The full 32-row target-sigma expint batch **PASSES** all endpoint comparisons.
It checked 164,712 coefficients, 22,776 nonzero terms, and 45,552 primary/dual
expint evaluations with no consistency failures. Exact row margins range
from `2.0592384721174497e-20` (twist +55) to `1.2961086925710612e-19`
(twist -10). See the
[`batch result`](h6-all-quadratic-expint-report.md),
[`pinned receipt`](h6_all_quadratic_expint.json) (SHA-256
`54e9fe4921c92366da8644e27bd8d2217a04b678046dfa3c31701519b4c917ce`), and
[`plan/provenance`](h6-all-quadratic-expint-plan.md). The guarded run completed
in 6.480669 seconds, with admission at 15.9 GiB host / 1.00 GiB cgroup
headroom; peak RSS was unavailable. The expint method remains conditional on
the coefficient bound, the Dirichlet-series identity, contour-growth
conditions, functional equations, and complete bad factors.
The exact-rational substitution of all 32 direct endpoints **PASSES** the
mixed-quadratic group allowance and inherited target assembly, retaining the
existing final ceiling. The sum of row improvements is about `1.6378733e-18`;
updated mixed-quadratic group slack is about `2.5570069e-18`. See the
[`exact aggregate report`](h6-target-batch-aggregate-report.md), receipt
[`h6_target_batch_aggregate.json`](h6_target_batch_aggregate.json) (SHA-256
`e65fa928f5a4c2d0568aff3aa9cf37fd6034838f353884601d55810b6b0e6609`), and
[`method/provenance plan`](h6-target-batch-aggregate-plan.md). This
Fraction-only check consumes the conditional direct expint upper endpoints;
it proves no new analytic premises.
The exact rational aggregate arithmetic also has a Lean transcription and
audit in [`h6-target-lean-arithmetic.md`](h6-target-lean-arithmetic.md); that
checks the arithmetic substitution, not the external functional equation,
coefficient bound, or AFE tail hypotheses.

## H7 mixed-octic segmented full-bin replay

The source-only plan for the already completed full five-family 836-factor
AFE replay at `sigma = 12001/12000`, including exact source/archive hashes,
runtime, and the deferred nonzero-phase octic branch assessment, is in
[`afe-836-replay-plan.md`](afe-836-replay-plan.md). It concludes that a
same-input rerun adds no material evidence beyond the September 22 replay.

An independent segmented checker was run for the mask-1824 twist +1
row (degree 8, gamma `[0,0,0,0,1,1,1,1]`, root +1, conductor
208190684989647360000, cutoff 360720360). It scans coefficient factors in
blocks and immediately aggregates the exact degree-20 bin moments. It uses a
byte per possible prime label, not a dense coefficient vector. The selected
row is bound to the arithmetic fixture by conductor, gamma/root metadata,
all seven bad Euler factors, and the first 128 coefficients; it is the
quartic-phase-zero row, separate from its large-conductor twist -1 partner.

The pilot first compared the first 256 frozen bins, contiguous through
N=39746, with 263 nonzero terms. This checked beyond the first 128
coefficients and matched all 21 signed and absolute moments in every bin.
Full mode then compared all 544 frozen bins through N=360720360. The full
result is **PASS**: all 548,127 nonzero coefficients were accumulated, every
bin boundary, midpoint, mass, count, signed moment, and absolute moment
matched exactly, and the first 128 coefficients matched. There were no
mismatches. The full machine-readable receipt is
[`h7_octic_segmented_direct.json`](h7_octic_segmented_direct.json), SHA-256
`efaeeff42730d13cfb4e25ed94d551ba511f4f0604d059d6bca5b59af8883d28`.

The full run was admitted by the 1800-second guard with 13.9 GiB host memory
available and 1.44 GiB cgroup headroom. Runtime including compilation was
35.166353 seconds. Peak RSS was not available from guard/tool output. The
compiled executable hash is `cd5bda9679a0837791e7e7e5868db2d3c451cfe011ce8d7ce2fd964b8f616203`;
the exact compiler command, source hashes, input hashes, bin-layout hash, and
raw-output hash are in the receipt. The lock was released on successful exit.
The binary lived in a temporary build directory that was removed after the
run, so the recorded executable digest cannot now be independently rehashed.
The read-only review in
[`h7-octic-segmented-review.md`](h7-octic-segmented-review.md) recomputed all
source hashes, confirmed row binding and receipt counts, and found no
practical false-PASS path; it also notes that it could not regenerate the
metadata hash because its environment lacked the `flint` module.

The first pilot attempt stopped before scanning at an erroneous assertion
that conflated sector mask 1824 with the twist's squareclass. For twist +1,
that squareclass is 0. The failed attempt's diagnostic receipt is preserved
as [`h7_octic_segmented_pilot_attempt1.json`](h7_octic_segmented_pilot_attempt1.json);
the corrected pilot summary is
[`h7_octic_segmented_pilot_summary.json`](h7_octic_segmented_pilot_summary.json).
The original successful pilot JSON was overwritten by the later full receipt;
the summary retains the captured pilot metrics and its at-run receipt hash,
and explicitly records that the original JSON bytes are unavailable.

The numerical checker reused the pinned arithmetic helper conventions and
prime-label formulas but used a separate segmented coefficient and moment
traversal from the frozen recursive sparse producer. The moment replay does
not recompute the AFE sums, interpolation or tail debits, bad-factor AFE
multiplier, or log endpoint. It also does not prove the row's conductor,
factor identity, functional equation, global `|a_n|≤d₈(n)` bound, or H. See
[`h7-octic-bounded-replay-feasibility.md`](h7-octic-bounded-replay-feasibility.md)
and the two `h7_octic_segmented_*` source files.
