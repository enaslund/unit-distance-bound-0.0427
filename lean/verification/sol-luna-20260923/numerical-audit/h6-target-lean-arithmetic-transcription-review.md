# H6 target aggregate Lean arithmetic transcription review

Read-only comparison of
`UnitDistance/H6TargetAggregateReplacementArithmetic20260923.lean` with the
target aggregate receipt `h6_target_aggregate_replacement.json`. No Lean or
numerical job was run, and the Lean source was not edited.

The receipt SHA-256 matches the Lean module's pinned digest:
`35ec8d17c01f716663e9e7c7b64862413efd65cbae6807851b3d06536e360f27`.
The Lean source SHA-256 reviewed here is
`b7393c6351dca618d7e5d707e54e83eeda8cd3c545c964c25b42c1e989c85c1e`.

## Rational transcription

All four private rational constants in the Lean module exactly match their
receipt fields:

| Lean constant | Receipt field | Check |
| --- | --- | --- |
| `directRowUpper` | `strict_row_comparison.direct_upper` | Exact equality |
| `frozenRowUpper` | `strict_row_comparison.frozen_target_upper` | Exact equality |
| `oldGroupUpper` | `mixed_quadratic_exact_aggregate.old_exact_input_upper` | Exact equality |
| `groupAllowance` | `mixed_quadratic_exact_aggregate.rational_group_allowance` | Exact equality |

The compared literals are:

```text
directRowUpper = 5254247244364801449641946514444622364599007319314955464370047545343763278192391042275983942521594522681262381545149 / 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816
frozenRowUpper = 10508494488729602899283889525415267350463335842446545934248460760518715383379283667923392442825005722226671970168313 / 78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632
oldGroupUpper = 2021855623839300674327469484631254025352927934824871541534433570606904982134797463157587608030041969833662486552665055 / 5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448
groupAllowance = 400886873183882259 / 1000000000000000000
```

The exact widened group sum is

`oldGroupUpper + (directRowUpper - frozenRowUpper)`

and equals the receipt's `new_exact_input_upper` exactly. It is strictly below
`groupAllowance`; the computed difference equals the receipt's
`new_exact_rounding_slack`. This matches the Lean proposition
`widened_group_below_allowance`. The strict row proposition also has the
receipt's recorded outcome: **FAIL**, since
`frozenRowUpper < directRowUpper`.

The receipt's exact widened group sum is
`2021855623839300674327469708853588577591947377780606901181898167737708897207149361821816436332005702514357065299672095/5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448`; the allowance-minus-sum slack is positive and exactly matches `new_exact_rounding_slack`.

The Lean final rational upper,
`2108090946974047476569229/50000000000000000000000000`, exactly matches
`full_table_effect.final_rational_upper_after` (and `before`) in the receipt.
The additional target ceiling literal `42161819/1000000000` matches the
receipt's `target_ceiling`; the exact strict inequality is consistent with
its recorded ceiling slack. The receipt status is **PASS exact target
mixed-quadratic aggregate replacement; strict row comparison remains FAIL**.

## Receipt provenance

The aggregate script hash matches its receipt field:
`b7302cfee6457776d1d8142dc3367f4b12805e0838d2d90b0bcb301c9695becb`.
Every listed receipt input hash was checked against the current file:

- Target direct row receipt:
  `d35c52ea39918684b39c456c1e1fd6f3cdad3b61e177f0eeea06c5457e7eff58`
- Target inherited Euler receipt:
  `b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f`
- Consolidated analytic replay:
  `34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e`
- Earlier off-sigma direct row receipt:
  `5ad1872e87f6c9a823fc3d0ad9491b29807a8cfa9ff61b70335130f1a4caabcf`
- Earlier H6 aggregate replacement receipt:
  `1df80e3c2ade0134178f35a6d7742f26930ba6d91bdd1b4e6c7ea52451175bf1`

This review establishes rational transcription and source-hash agreement
only. The arithmetic module explicitly assumes its direct row upper is a
valid analytic bound; it does not prove that external numerical or analytic
premise, and this review did not compile Lean.
