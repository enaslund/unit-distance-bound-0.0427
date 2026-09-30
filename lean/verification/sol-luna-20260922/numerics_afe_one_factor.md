# Independent direct-kernel AFE check for one factor

`numerics_afe_one_factor.py` checks the H6 sector `mask=1586`, twist `-1`
quadratic factor at `sigma=12001/12000`. It evaluates a single factor only;
it does not replay the 836-factor table.

The manuscript's quadratic AFE kernel satisfies

```text
I_b(x) = integral_1^infinity u^(b-1) exp(-x*u) du = E_(1-b)(x).
```

The checker evaluates these weights directly with Arb's generalized
exponential integral: `I_sigma(t*n)=E_(1-sigma)(t*n)` and
`I_(1-sigma)(t*n)=E_sigma(t*n)`, where `t=2*pi/sqrt(15015)`. This differs
from the manuscript's Taylor-grid kernel computation. It reconstructs the
finite coefficient row using the pinned independent rank-two residue/Euler
checker, verifies the complete 981-entry coefficient-vector hash, and checks
that both direct finite-sum intervals overlap the printed AFE `A_finite` and
`B_finite` intervals.

For the omitted tail, put `delta=sigma-1=1/12000` and `m=N+1=982`. For
`x>=t*m>delta`, the integral definitions give

```text
I_sigma(x) <= exp(-x)/(x-delta)
I_(1-sigma)(x) <= exp(-x)/x.
```

Using the row's coefficient bound `|a_n|<=d_2(n)<=2*sqrt(n)` and a geometric
sum bounds the two omitted AFE terms by

```text
tail_A <= prefactor * 2*exp(-t*m) /
          (t*sqrt(m)*(1-delta/(t*m))*(1-exp(-t)))
tail_B <= prefactor * 2*exp(-t*m) /
          (t*sqrt(m)*(1-exp(-t)))
prefactor = t^sigma/Gamma(sigma).
```

Arb evaluates the finite sums, tail expressions, seven bad-prime factors, and
logarithm with outward intervals at 256-bit precision. The coefficient-bound
premise and the supplied functional equation, conductor, row identity, and
bad factors remain conditional inputs. The AFE identity assumes the completed
degree-two L-function has archimedean factor `Gamma_R(s) Gamma_R(s+1)` and a
functional equation with root number of modulus one. The manuscript labels
this row's root number `+1`; the phase-free triangle bound uses only its
modulus. The global bound `|a_n|<=d_2(n)` is also an external unitary-local-
factor premise. The checker verifies the finite 981-entry sequence, not that
infinite coefficient bound or the field identification.

## Guarded result

```text
guarded-build: admitted with 19.7 GiB available; exit 0; both modes passed
sigma=12001/12000; mask=1586; twist=-1; degree=2; conductor=15015; N=981
python=/usr/bin/python3 3.13.5; python-flint=0.9.0; linked FLINT=3.6.0
source modes=full research tables verified; compact hash-pinned fixture
complete coefficient vector SHA256=baec4879c9e60ab3f2e657ff9f4d9cac64a39eebc3aa123495844f19e3ef654c
direct A finite interval overlaps printed A interval: yes
direct B finite interval overlaps printed B interval: yes
tail_A_upper=1.7292588510283369619614091510322739e-22
tail_B_upper=1.7292559891572087453988819977733517e-22
L_upper=0.58826389943779272863457054737706122
bad_multiplier_upper=1.7839372855929801848133896557979754
computed log L^S upper=0.048243256524037312536687462524286013
  exact upper endpoint: 89378999432481043611149362575072813015969718630390823852292967222212704702751 * 2^-260
printed log L^S upper=0.048243256524037312591956533323098958
  exact upper endpoint: 15207048739954932604118704376168157803668370720358482512541816838400848427083546290461778463141797612626490565502465 * 2^-387
comparison=independent upper is below printed upper
```

The computed and printed endpoints are stored exactly as dyadic rationals in
the script output; the displayed decimals are rounded. The
computed upper is lower than the printed upper by approximately
`5.5269e-20`. This is a one-factor numerical certificate under the stated
AFE and coefficient-bound hypotheses. It is not an independent proof of the
factor's field identification or the functional equation, and it does not
establish the global zeta hypothesis.

## Pinned inputs

The compact input fixture is 4,627 bytes, SHA-256
`3d05b2be40b3392bf48022b57d352ebeb6c0f48dc288944fba77becc108b7505`. It binds
the selected allowance to these sources:

```text
h7-inherited-euler-12000.json       b6e87580af03ec9260c9277bfa64d786937d6d087ce9d99a0e4244e4345f625f
h6-low-degree-arithmetic.json       b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771
h6-low-degree-moments-1586.json     a7e65537a05389f11115a8cf64c186ead6b1dc4973a8c5f862f31a34fdeb40f1
h6-low-degree-euler.py              9fdee8fe5bd9fcbc90c9b28ccbdd0ec5066d49b8b52757ee3f20cc89af707f38
nonpositive-afe.py                 8d6b82b12f7de4a3d53feccde8aaffe0d0fbdf4b623c1447af6ea68ed399cba7
next-dyadic-h5-single.py            f9a97f5c41485914e9700a5efcebb9df0ffdbc834a56a666b994d397ab3a3ba6
numerics_hecke_coeff_check.py       3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329
numerics_hecke_family_fixture.json  5fd9c83deb0fcdef56d314657ae8e1c7408c5508e652834e32cdabc3de234200
```

The checker verifies each available full-source hash and compares copied row
and sector fields with those tables. In a standalone package, publication
tables and scripts are optional: their pinned hashes remain embedded in the
fixture, while the compact row and the independent coefficient helper/fixture
suffice for the calculation.

## Runtime

This checker requires `python-flint==0.9.0`; the guarded run used
`/usr/bin/python3` version `3.13.5` and observed linked FLINT `3.6.0`. The
local guarded command was:

```sh
PYTHONPATH=/tmp/unit-distance-flint python3 automation/lean-formalization/guarded_build.py \
  --wait-seconds 300 --timeout-seconds 900 -- \
  python3 lean-formalization/verification/sol-luna-20260922/numerics_afe_one_factor.py
```

`/tmp/unit-distance-flint` is an environment-local dependency path and is not
shipped in the archive. For replay, install `python-flint==0.9.0` in the
chosen Python environment, then run the checker with that environment's
`python3` and the checked-in fixture files. The package contains no binaries
or vendored library.
