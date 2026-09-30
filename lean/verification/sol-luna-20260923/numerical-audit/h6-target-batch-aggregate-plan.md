# Exact aggregation of the 32 H6 quadratic expint rows

## Objective and proposed comparison

[`h6_target_batch_aggregate.py`](h6_target_batch_aggregate.py) is a
source-ready, standard-library `Fraction` checker. It consumes the pinned
32-row expint receipt and small target/consolidated JSON tables. It does no
Arb evaluation and proves no analytic premise. The exact check has now run
once under the allocated shared guarded slot.

The H6 inherited sector has 32 mask-1586 degree-two rows. Each source row,
direct expint row, and inherited target row is matched by twist, conductor,
cutoff, and multiplicity. All target inherited multiplicities are 1, and the
sum of row multiplicities must equal the sector's `individual_factors` count.
The checker verifies every direct endpoint and margin against its exact
dyadic target endpoint, then forms the rational totals

`R = sum multiplicity * frozen row upper`,
`D = sum multiplicity * direct expint upper`,
`delta = D - R`.

The inherited sector's `log_L_S_sum` upper is checked to be at least `R`.
The mixed-quadratic group input in the full exact table contains that sector
upper plus the other mixed-quadratic sector uppers. To retain its original
outward sector-sum rounding slack, the conservative replacement is

`G_new = G_old + delta`,

not `G_old - sector_upper + D`. Because the batch receipt establishes every
row margin is positive, `delta < 0`; the new exact group upper is lower than
the already passing old group upper. The checker still calculates and
compares exact fractions against the group allowance, rather than relying
only on the sign argument.

The pinned table assembler groups all inherited degree-two sector sums into
`mixed_quadratic`; the pinned inherited evaluator sums each row endpoint with
its `factor_multiplicity`. Those source hashes and the consolidated receipt's
target-source bindings are checked. For the target H assembly, the degree-two
group has weight `2/16384`. If the existing mixed-quadratic allowance remains
valid, the published rounded group allowance, dimension-weighted table
bound, five-rational-allowance assembly, and final ceiling are unchanged.
The checker verifies that exact existing rational assembly and ceiling; it
does not propose a new sharper published value.

## Scope distinction

This Fraction checker can establish only that the 32 already computed direct
upper endpoints fit the target table's mixed-quadratic group allowance and
that the inherited rational target assembly remains valid. The expint receipt
is conditional on each factor's identity, conductor/gamma/root number,
functional equation, Dirichlet-series identity, contour-growth conditions,
complete bad Euler factors, and global `|a_n|<=d_2(n)` tail bound. It also
assumes sound Arb/python-flint outward intervals. The finite rational
aggregation does not prove any of those analytic statements or `H`.

It pins the method-specific single-row expint **PASS**, the full 32-row
expint **PASS**, the previous pointwise `SplitKernels` strict **FAIL**, and
the prior one-row target aggregate **PASS**. It preserves those independent
statuses and receipts.

## Pinned inputs

| Input | SHA-256 |
|---|---|
| H6 arithmetic | `b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771` |
| H6 inherited evaluation | `b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f` |
| Consolidated analytic replay | `34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e` |
| Exact table assembler | `768707a65d5b6bf2f1dc27ebf12e2cbc4a7ffbd87ecd5effb3acc2987387d662` |
| Inherited H6/H7 evaluator | `cb52db15386d204a92bf4b4f689742bb8e34e377df043170ed2a7c742e8ff0aa` |
| H6 all-quadratic expint checker | `060af68df4b7e1eb6dfba87e88ca13fa26cbccca16966c2c256b4fc8cd2116c3` |
| H6 all-quadratic expint receipt | `54e9fe4921c92366da8644e27bd8d2217a04b678046dfa3c31701519b4c917ce` |
| H6 single-row expint receipt | `56aa4b9fddbe580d852119f79329635c06630d2833315857b581fe1aa0bb4e2f` |
| Preserved SplitKernels row FAIL | `d35c52ea39918684b39c456c1e1fd6f3cdad3b61e177f0eeea06c5457e7eff58` |
| Preserved single-row aggregate PASS | `35ec8d17c01f716663e9e7c7b64862413efd65cbae6807851b3d06536e360f27` |

The checker passed `py_compile` and a read-only hash check of its pinned
inputs. Checker SHA-256:
`9de12672586525793d728032579a4fb3b8f9329a939cb9a5e86e0d0204714d71`.
The exact result is **PASS**. The sum of the 32 endpoint improvements is
`33042173493187893057900326884279802675077326081844816299084309047951299307003449420392482976918034241/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792`
(about `1.637873330160229e-18`). The checker adds its negative to the frozen
mixed-quadratic group input while retaining the inherited sector's outward
summation slack. The updated exact group upper remains below the allowance
`400886873183882259/1000000000000000000`; its exact remaining slack is
`196779691088030316751652087065885787076111131282221990375374954548870899369516153378449313484110681637934063338237/76957043352332967211482500195592995713046365762627825523336510555167425334955489475418488779072100860950445293568000000000000000000`
(about `2.557006903021371e-18`).

The degree-weighted input decreases by `2/16384` times the exact group
change, about `-1.9993570924807484e-22`. The existing rounded mixed-quadratic
allowance, dimension-weighted table bound, and five-rational-allowance target
assembly remain unchanged. The final exact rational upper remains
`2108090946974047476569229/50000000000000000000000000`
(`0.04216181893948094953138458`), below `42161819/1000000000`, with slack
`3025952523430771/50000000000000000000000000`.
The `42161819/1000000000` value is the tighter inherited manuscript ceiling;
the package H threshold is `42165819/1000000000`, leaving slack
`0.00000400006051905046861542`.

The result receipt is
[`h6_target_batch_aggregate.json`](h6_target_batch_aggregate.json), SHA-256
`e65fa928f5a4c2d0568aff3aa9cf37fd6034838f353884601d55810b6b0e6609`.
It dynamically verifies the target receipt hash in both consolidated
source maps and checks `all_analytic_factors_reevaluated = true`.

The executed command was:

```sh
python3 automation/lean-formalization/guarded_build.py --timeout-seconds 900 -- \
  python3 lean-formalization/verification/sol-luna-20260923/numerical-audit/h6_target_batch_aggregate.py
```

Guard admission was 16.4 GiB host memory / 1.41 GiB cgroup headroom; this
fraction-only checker completed in `0.11784284096211195` seconds with exit 0.
Peak RSS was unavailable.
