# H6 quartic zeta quotient: finite coefficient replay plan

## Status

Attempt 4 completed the exact finite comparison with zero mismatches; its
executed checker SHA-256 is
`7139eb656580755af33ece151acb072bdc76ef3d8af60e47b6118cfd22f39a5f` and its
immutable receipt is `h6_quartic_zeta_quotient_attempt4.json`. The current
source SHA-256 is
`1643a51379688ba6c1df0aee178f1759e16b8b4016e09c1394e648eabeee7905`; it only
corrects tool-version provenance and records the imported python-flint
installation tree. Its later guarded reruns (attempts 5 through 7) were deferred
by the master guard with exit 75 before checker launch. Candidate16 captured
an earlier untested draft whose global coefficient assembly was incorrect.
Attempts 1--3 are also preserved: GP syntax error, table representation
mismatch, and missing import path respectively. None produced a coefficient
comparison. Logs and receipts use the matching `h6_quartic_zeta_quotient_attemptN.*`
names. Only attempt 4 completed the comparison.

The successful attempt-4 guarded command was:

```sh
python3 automation/lean-formalization/guarded_build.py --timeout-seconds 900 -- \
  env PYTHONPATH=/tmp/unit-distance-flint python3 \
  lean-formalization/verification/sol-luna-20260923/numerical-audit/h6_quartic_zeta_quotient.py
```

The checker launches one quiet GP process over the 543 rational primes at most
3922, constructs two `nfinit` structures, checks each with `nfcertify`, and
reads `idealprimedec` e/f data in the resulting maximal orders. The Python
side forms exact integer local series and the multiplicative Dirichlet
coefficient vector. The pre-run source estimate was seconds and under 1 GiB;
the observed attempt-4 admission and timing are recorded in the
[result report](h6-quartic-zeta-quotient-report.md). GP is given a 400 MB
PARI stack. No Lean build or Arb calculation is part of the run.

## Fields and local-factor comparison

Set `beta^2 = -35` and `alpha = 17 + 2 beta`. Then
`Norm_{Q(beta)/Q}(alpha) = 429`. If `u^2=alpha`, elimination of `beta` gives
`u^4 - 34 u^2 + 429 = 0`; the proposed fields are

* `B = Q(beta)`, defined by `x^2 + 35`,
* `K = Q(u)`, defined by `x^4 - 34 x^2 + 429`.

Subject to the polynomial irreducibility and field identification, `K/B` is
quadratic. The independent route uses, at every rational prime `p <= 3922`,
the maximal-order prime ideals from `idealprimedec`. If their residue degrees
in a field `F` are `f_i`, its local zeta denominator is
`D_F(T)=prod_i (1-T^f_i)`. Thus the local factor of `zeta_K/zeta_B` is
`D_B(T)/D_K(T)`. The checker computes those formal series and their exact
Dirichlet product through `n=3922`.

The pinned H6 coefficient source
`publication/six-dimensional-lower-bound/research/next-dyadic-h5-single.py`
uses the following good-prime rule. For `p` outside its explicit set
`S={2,3,5,7,11,13,17}`, let
`a=(-35/p)` and `b=(429/p)`. If `a=1`, choose `r^2=-35 mod p`; the two
reductions of `alpha` are `17+2r` and `17-2r`. Their quadratic signs have
product `b`. When `b=1`, the signs coincide at `epsilon`, giving denominator
`1-2 epsilon T+T^2`; this is precisely the source's `legendre(17+2*r,p)`
test and the assertion that its conjugate has the same sign. In all other
cases the induced degree-two local denominator is `1+a*b*T^2`, which the
source encodes as trace zero and determinant coefficient `a*b`. If `a=-1`,
`B` is inert and the relative quadratic character on its degree-two residue
field is the sign of the residue norm `Norm(alpha)=429`; the induced local
factor gives the same `1+a*b*T^2` rule. This explains the source's
quadratic-residue branches in terms of the proposed field splitting rule.

At the seven explicit finite exceptions the checker compares the table's
exact polynomial `E_p(T)` with PARI data by the identity
`D_K(T)=E_p(T) D_B(T)`, including the prime 17 (which is separately listed
by the table even though it is unramified in the displayed field models).
This is a symbolic comparison of the two local-factor formulas at those
primes, plus finite PARI decompositions. It does not establish the branch
rule at every prime by computation; the argument above is the source-level
derivation. In particular, finite coefficient equality alone cannot prove
the all-prime identity of L-functions.

## Target and pinned sources

The target is the H6 low-degree sector mask `1586`, twist `+1`: `N=3922`,
conductor `240240`, gamma vector `[0,1]`, root number `+1`, and multiplicity
`1`. The expected coefficient vector is reconstructed by the pinned
quadratic-Hecke recurrence; the independent PARI vector comes from
maximal-order zeta factors. The intended assertion is exact equality of all
3922 integer entries and a common SHA-256 after deterministic JSON
serialization.

Pinned input/tool sources checked by the script:

| Input | SHA-256 |
|---|---|
| H6 sector/row inventory `h6-low-degree-arithmetic.json` | `b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771` |
| H6 inventory generator `h6-low-degree-arithmetic.py` | `09cf2aae4e0f67bf3dee34289fd767635b0499801e81d787950f48b53599c14f` |
| H6 evaluator/source-binding driver `h6-low-degree-euler.py` | `9fdee8fe5bd9fcbc90c9b28ccbdd0ec5066d49b8b52757ee3f20cc89af707f38` |
| H6 arithmetic explanation `h6-low-degree.md` | `09f325e66fb399f463576aaa1314d321611dd92e89c38158851eb84836306b46` |
| Target recurrence `next-dyadic-h5-single.py` | `f9a97f5c41485914e9700a5efcebb9df0ffdbc834a56a666b994d397ab3a3ba6` |
| Sector extension input `next-dyadic-arithmetic-extensions.json` | `729cbff5f8477db075a43cec9a7e3aa20ed077a5d244592d472ac55b4bb97de6` |
| Recurrence dependency `five_descent.py` | `3671cea7925585b7f8a0f83310777b9dbb09c64d039544e7c3333c0d630faf0a` |
| Recurrence dependency `five_single.py` | `fab1dab721b92f3d2713d666e6ad9a394b6f5ff90834609d6190e432e2e0053f` |
| Recurrence dependency `five_space_data.py` | `b11235fa492a91fe2b487e35bcbb46ad87bb09ab1f22ceaf2dc5e7d3b892d4ec` |
| Recurrence dependency `four_space_odd_local.py` | `e3a8488c434b3e0c6978ce06f1ca1fcef76587e1b6a3ab55d21a1622ab67254b` |
| Recurrence dependency `hecke_coefficients.py` | `897f51fa566be6312288f5e48552cd44655051a3967cd2123b4e05f6cb95defe` |

The current checker passes `py_compile`; source pins were reverified for the
successful attempt-4 run. That receipt records all source pins, generated GP
source hash, guard admission, runtime, both vector hashes, and all seven local
cross-products. The checker used `gp -v` and stored usage text in its raw
`tool.version` field; the post-run provenance supplement gives the documented
`gp --version-short` result and executable hash. The current source fixes this
metadata issue and records the import-only python-flint tree hash. Guarded
replays of the corrected source were deferred three times with exit 75, and their
logs/receipts are preserved as attempts 5 through 7.

## Scope limits

This is an independent finite arithmetic cross-check. It does not by itself
prove that the displayed quartic polynomial defines the claimed relative
extension at every prime, although its maximal-order finite decomposition
checks are evidence for the first 3922 coefficients. It does not prove the
conductor, gamma factor, root number, global functional equation,
Dirichlet-series identity in a half-plane, contour shift or growth
conditions, coefficient bound used for the AFE tail, or any global bound
for `H`.
