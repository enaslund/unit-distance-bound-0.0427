# Independent direct AFE check: pure-quartic H7 row

## Result and scope

I independently recomputed the conditional AFE upper bound for the pure-quartic
sector `1920`, twist `-1`, at \(s=12001/12000\). The selected row has degree 4,
conductor `57715257600`, gamma signature `[1,1,1,1]`, and root number 1. Its
printed row allowance is the `log_L_S_upper` for twist `-1` in the pinned
`h7-pure-euler-12000.json` source.

The checker produced

```text
direct log_L_S upper: [0.056343705003318770013297083706909639 +/- 6.90e-38]
printed row allowance: [0.056343705003318770013297316723754411 +/- 1.34e-37]
```

The exact slack, using the printed interval's upper endpoint minus the direct
upper endpoint, is

```text
390530637392689426124036281431883219284896255408670391756005606291478407195545686917233565005188120939621774886984488321397021521 /
1675975991242824637446753124775730765934920727574049172215445180465220503759193372100234287270862928461253982273310756356719235351493321243304206125760512
```

This is approximately `2.330168447717979e-25`. Thus this one independent
conditional row check is below its pinned printed allowance.

## Independent computation

The checker generated all `1,921,920` coefficients from the defining residue
character and local Euler recurrences implemented in
`numerics_hecke_coeff_check.py`, extended to the full AFE cutoff. It checked
the first 128 coefficients against the compact source row. It also checked the
coefficient count, absolute mass, and zeroth moment in every one of the 713
pinned exact-moment bins. These checks matched; there were `26,785` nonzero
coefficients.

It then evaluated the four-Gamma Mellin kernel pointwise by the pinned
residue-series implementation at each nonzero coefficient. This does not use
the source AFE's degree-40 moment/bin Taylor summation. At 512-bit Arb
precision, the direct finite sums were

```text
A = [2.5126741323482692441436646271132668 +/- 4.18e-35]
B = [0.030087461344280462932060292257572466 +/- 4.66e-37]
```

This is an independent pointwise use of the AFE, but it reuses the existing
pinned four-Gamma kernel implementation; it is not a second proof of that
kernel's residue-series enclosure.

The source's `A_finite` and `B_finite` entries are polynomial-center sums, not
enclosures of the exact dense sums. Therefore the direct values were checked
against those centers expanded by the separately printed one-side
interpolation error. Both were inside that allowance. The interpolation error
was used only for this source-consistency check; it was not added to the direct
bound.

For the omitted terms I used \(\beta=5/4\), the degree-four divisor majorant
\(|a_n|\le d_4(n)\), and hence
\(\sum_{n>N}|a_n|n^{-\beta}\le\zeta(\beta)^4\). The positive Mellin-kernel
tail bound on each side was

```text
1.3183188411585997346730580619162774e-9.
```

The bad-prime logarithmic correction independently overlaps the pinned
`BAD7_log_removal` interval. Combining the pointwise direct sums, the two tail
bounds, and that correction gives the displayed log upper.

## Guarded receipt and provenance

The successful command was run through `automation/lean-formalization/guarded_build.py`
with `--wait-seconds 30 --timeout-seconds 900`, inherited disk `TMPDIR`, and
`PYTHONPATH=/tmp/unit-distance-flint`. The guard admitted the job at `14.8 GiB`
available. The checker reported Python-flint `0.9.0` and FLINT `3.6.0`.

Two earlier guarded diagnostic attempts are preserved. Both exited 1 at a raw
`A_finite` interval-overlap assertion. That assertion was inappropriate because
the source interval records only the Taylor-polynomial center; the direct sum
differed from its center by about `1.9e-33`, within the independently printed
`2.962531430287528e-25` one-side interpolation error. The corrected check
explicitly uses that error only to compare centers. It does not relax the
direct bound or final allowance comparison.

The successful guarded JSON output is
[`numerics_afe_pure_quartic_direct_corrected_guarded.log`](numerics_afe_pure_quartic_direct_corrected_guarded.log)
(SHA-256 `676fcf078f6febfa4521371626c1c287747578efdaa4c40c78cfb5417b132926`).
The failed diagnostic logs are
[`numerics_afe_pure_quartic_direct_guarded.log`](numerics_afe_pure_quartic_direct_guarded.log)
(SHA-256 `7657f3699f95e43887e9369dbbae0bf98527af8b37951150080254bda2f6f8e4`) and
[`numerics_afe_pure_quartic_direct_retry_guarded.log`](numerics_afe_pure_quartic_direct_retry_guarded.log)
(SHA-256 `c070fc49198095f7ec1a9b1e00d085cdf1be48e329d60987fd20579ffc7dc540`).

Checker source SHA-256:

```text
numerics_afe_pure_quartic_direct.py
8b51cd4e9584b7e48c715cf3cb279ee30da2ad16f955ee60d10fa40dd269ef34
```

The computation binds these inputs:

| Input | SHA-256 |
|---|---|
| `h7-analytic-kernel.py` | `2b47df974b40453a1440df740bb011648c28a3297d4fc598eaa70d0121a34150` |
| `h7-pure-quartic-afe.py` | `0dc7bbafd9fe81660cb74b4f1a5ca0fefed6a622dd31c7f2241f7feae0919342` |
| `numerics_hecke_coeff_check.py` | `3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329` |
| `numerics_hecke_coeff_fixture.json` | `db0e2050cf3e9a3d1f0b79f4481b55609b52fb071a2ade4c93acfc21e864a1ae` |
| `h7-pure-arithmetic.json` | `e1d892ba20f90bf6ea15e52f710ead0b8806a6db50d95792a76ebe2552183948` |
| `h7-pure-moments.json` | `c999ec7882f758e72f683fc3572406ed0d325ff674958e23a0349f322ecd84bf` |
| `h7-pure-euler-12000.json` | `441ecbc24ae113807de6de5b2e911c356c98c6df6947bdac7e94233cb49a2d3e` |

## Conditional assumptions and limitations

The AFE conclusion assumes the pinned row's conductor, gamma signature, and
unit root number belong to the asserted entire completed degree-four
L-function and functional equation. It assumes the finite-image degree-four
local data give \(|a_n|\le d_4(n)\) at every prime, and that the pinned
bad-prime denominators are the complete local factors removed in the printed
quantity. The computation does not prove these analytic or representation
identifications, establish the global hypothesis \(H\), or verify a complete
Euler product. It checks one pure-quartic row against its numerical allowance.
