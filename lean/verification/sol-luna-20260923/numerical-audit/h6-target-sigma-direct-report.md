# H6 mask 1586, twist `+1`: direct target-sigma replay

## Objective and source binding

The prior H6 pointwise row check used `sigma = 6001/6000`, so it could not
independently check the same row at the five-family target
`sigma = 12001/12000`. This replay reconstructs the same H6 mask-1586,
twist-`+1`, degree-two row (conductor 240240, gamma `[0,1]`, root number
`+1`, multiplicity 1, cutoff 3922) and evaluates it directly at the target
sigma. It uses the same exact quadratic coefficient recurrence and the
pinned quadratic `SplitKernels` and Arb/FLINT backend as the previous direct
check; it is not a new analytic kernel or interval backend.

The target comparison is the mask-1586/twist-`+1` `H6-low` row in
`publication/nonabelian-dyadic-lower-bound/research/h7-inherited-euler-12000.json`.
The checker verifies that the target receipt's SHA-256 occurs both in the
consolidated receipt's `printed_analytic_table_check.source_sha256` map and
in `analytic_replay.replay_input_sha256`, and that the consolidated receipt
sets `all_analytic_factors_reevaluated = true`. The row source arithmetic and
moment hashes are the same as the earlier H6 replay.

## Preserved first attempt

The first guarded attempt used the source snapshot reconstructed by reverting
the subsequent diagnostics-only edits from the executed script. The retained
reconstruction is
[`h6_target_sigma_direct_attempt1.source`](h6_target_sigma_direct_attempt1.source),
SHA-256
`ff5b66f7e20cd9c42496e4a5101b49cddddbb9b548ce48c9d71217cf40967553`.
The guarded command admitted with 15.7 GiB host memory available and 1.27
GiB cgroup headroom. It stopped with exit 1 at the check
`direct interpolation remainder exceeds target-sigma allowance`, before
serializing a JSON receipt. This is a **failed consistency check**, not a
recorded strict comparison of the direct `log L_S` upper with the target row
endpoint; this first attempt does not establish either a target row PASS or
target row FAIL. Its diagnostic limitation is preserved here.

The revised checker at
[`h6_target_sigma_direct.py`](h6_target_sigma_direct.py) records the direct
endpoint and all target-row consistency flags before returning its strict
comparison status. It pins the earlier off-sigma H6 **FAIL** and same-sigma
H6 aggregate-substitution **PASS** and does not modify either receipt. A
syntax check passed, and a lightweight JSON check confirmed that the
consolidated receipt binds the target endpoint at both source-map locations.
The target receipt binding was checked in both the consolidated table's
`source_sha256` map and the analytic replay's `replay_input_sha256` map; both
equal the target receipt digest, and the consolidated flag
`all_analytic_factors_reevaluated` is true.

## Guarded target-sigma result

The revised run used the master guard with a 900-second timeout and was
admitted with 15.9 GiB host memory available and 1.63 GiB cgroup headroom.
It completed the pointwise computation in 0.415137 s, wrote
[`h6_target_sigma_direct.json`](h6_target_sigma_direct.json), then exited 1
for its preserved strict-comparison **FAIL**. The complete receipt SHA-256 is
`d35c52ea39918684b39c456c1e1fd6f3cdad3b61e177f0eeea06c5457e7eff58`; the
checker source SHA-256 is
`3be6c008e4edcb6471445c27a7d283c3360b5f07e23d808e7c30fc3ab1f5375b`.

All 3,922 coefficients were reconstructed, the signed-vector hash matched,
and all 184 exact bins agreed. At the actual target sigma, the direct outward
upper is
`0.133349739050738911508179782026150081`; the target row endpoint is
`0.13334973905073891150817973756808417`. The direct endpoint exceeds the
target endpoint by exactly
`3503473977378734678796183364994491634330168811173005498416628575442218183323135852792921985/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632`,
approximately `4.4458065915680757e-26`. The target row comparison therefore
remains **FAIL**.

The direct primary and dual finite sums lie within the target center intervals
after its interpolation debit. The pointwise direct interpolation upper is
larger than the target's stored interpolation upper by the exact difference
`7/46517678354918840995156723704832290198633047083988355858015372747560914439257467092876227245680868195888801382801035387746214504231337984`,
about `1.5048042480950279e-136` (one tiny final-rounding unit). The directly
recomputed tail and bad-factor product overlap the target intervals. This
component check remains recorded false; the direct full endpoint and strict
comparison are not relabeled as a row PASS.

## Exact full-table substitution

The direct pointwise endpoint is a valid upper under the same stated analytic
assumptions, so it can be substituted as an alternative row upper while
retaining the row-level **FAIL** against the tighter frozen endpoint. The
standard-library `Fraction` calculation in
[`h6_target_aggregate_replacement.py`](h6_target_aggregate_replacement.py)
has receipt
[`h6_target_aggregate_replacement.json`](h6_target_aggregate_replacement.json),
SHA-256
`35ec8d17c01f716663e9e7c7b64862413efd65cbae6807851b3d06536e360f27`.
It increases the target mixed-quadratic exact input upper by the same
`4.4458065915680757e-26`, from
`2021855623839300674327469484631254025352927934824871541534433570606904982134797463157587608030041969833662486552665055/5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448`
to
`2021855623839300674327469708853588577591947377780606901181898167737708897207149361821816436332005702514357065299672095/5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448`.
The changed exact group upper remains below its fixed rational allowance
`0.400886873183882259`; the remaining group-rounding slack is
`17683449697974575126351051383683032659161464622954148755634856646204946922408235702633815328667305113119685268153/19239260838083241802870625048898248928261591440656956380834127638791856333738872368854622194768025215237611323392000000000000000000`
(`9.191335284030761e-19`). The normalized exact AFE contribution increases
by `2/16384` times the row increment, or `5.4270099994727486e-30`.

Because the mixed-quadratic rational allowance remains valid, the displayed
table allowance and final rational ceiling are unchanged:
`0.04216181893948094953138458 < 0.042161819`, with slack
`3025952523430771/50000000000000000000000000` (about
`6.051905046861542e-11`). Thus the `1.0418235` target remains certified under
the existing global assumptions. This **aggregate substitution PASS** does
not erase the individual target-row **FAIL**, and neither proves H.

The exact replacement script ran with Python's standard-library
`fractions.Fraction` in 0.084190 s; its source SHA-256 is
`b7302cfee6457776d1d8142dc3367f4b12805e0838d2d90b0bcb301c9695becb`.

When allocated, run from the repository root:

```sh
python3 automation/lean-formalization/guarded_build.py --timeout-seconds 900 -- \
  env PYTHONPATH=/tmp/unit-distance-flint python3 \
  lean-formalization/verification/sol-luna-20260923/numerical-audit/h6_target_sigma_direct.py
```

## Assumptions and limits

The direct AFE upper remains conditional on this row's identification,
conductor/gamma/root number, functional equation, completeness of the
removed bad Euler factors, global `|a_n| <= d_2(n)` coefficient bound and
Rankin tail, and the validity of the pinned Taylor-kernel remainder proof
and outward Arb implementation. Reconstructing the complete finite
coefficient vector and matching its hash and all moment bins does not prove
the all-`n` coefficient bound or H. Even a strict target-row check is one
factor, not a replacement for the full target-sigma five-family certificate.
