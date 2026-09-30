# Read-only audit of the inherited H6 mask-1586 PARI receipt

## Finding

The stored arithmetic table claims an independent PARI check for all 32
degree-two mask-1586 twists at prefix 10,000: 320,000 coefficient comparisons
in total. The code supports that scope. I inspected the generator and
comparison source but did not execute them. This is an audit of a historical
JSON-embedded receipt, not a fresh guarded replay.

The stored table SHA-256 is
`b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`.
Its mask-1586 `independent_pari` object reports 32 evaluation rows, 32
individual factors, prefix 10,000, 320,000 checked coefficients, generated
GP-source SHA-256
`98c5ff9a0dd4da1e041da8e72edd9ca0497a539ba310d630a1973489a262e470`, and
GP-stdout SHA-256
`eaaff9aa4a85c16d73c79de21563eaa05d2bd2823b96c5e8d1cec927e39dd614`.
Each row also stores the Python expected-vector hash; for twist `+1` that
hash is
`a2500a2f5840f55abf314723421807d0275eb82caa9b7f37144d524149ceb304`.
The row hashes are not hashes of each individual PARI vector. The code
compares PARI coefficients to Python coefficients before writing the status,
and the stored GP-stdout hash commits to the combined printed output, but the
stdout itself is not present in this JSON.

## What the stored script checks

The generator
[`h6-low-degree-arithmetic.py`](../../../../publication/nonabelian-dyadic-lower-bound/research/h6-low-degree-arithmetic.py)
selects the rank-two sector with mask 1586, sets
`A=-35`, `x=17`, `y=2`, `N_B=429`, builds the 32 rows, and calls
`single.gp_check([recipe],10000)`. The exact comparison code is in
[`next-dyadic-h5-single.py`](../../../../publication/six-dimensional-lower-bound/research/next-dyadic-h5-single.py).
For each twist `D`, it forms the base polynomial `X^2+35` and quartic
`X^4 - 34 D X^2 + 429 D^2`, constructs
`L = lfundiv(lfuncreate(F), lfuncreate(B))`, and asks PARI for:

* `lfunparams(L)`, checked against the row conductor, root number `+1`, and
  gamma vector `[0,1]`;
* all seven local denominators at `2,3,5,7,11,13,17`, checked coefficient by
  coefficient against the row table;
* `lfunan(L,10000)`, checked entry-by-entry against the Python recurrence.

For this real row family, `complex_pair` is false; the source additionally
requires every expected coefficient to be real. On success, it stores the
per-row expected recurrence hash and aggregate generated-GP-script/stdout
hashes. The expected-vector hashes and 32 twist entries are present in the
JSON.

## Stored source binding and limits

All six paths in the arithmetic JSON's top-level `source_sha256` map match
the current files. They bind the H6 generator, generated modulus-five
helper, H5 rank-four and single-row helpers, H6 scan input, and the
conductor-thirteen helper. The H6 source generator itself hashes its
generated GP program and captured GP stdout. The original Python recurrence
source `next-dyadic-h5-single.py` is pinned at
`f9a97f5c41485914e9700a5efcebb9df0ffdbc834a56a666b994d397ab3a3ba6`.

The top-level map does not list all transitive imports of that recurrence
module (`five_descent.py`, `five_single.py`, `five_space_data.py`,
`four_space_odd_local.py`, and `hecke_coefficients.py`). Their current hashes
are shown below for audit context, but they are not part of the stored
H6-table binding.

| Unbound transitive import | Current SHA-256 |
|---|---|
| `five_descent.py` | `3671cea7925585b7f8a0f83310777b9dbb09c64d039544e7c3333c0d630faf0a` |
| `five_single.py` | `fab1dab721b92f3d2713d666e6ad9a394b6f5ff90834609d6190e432e2e0053f` |
| `five_space_data.py` | `b11235fa492a91fe2b487e35bcbb46ad87bb09ab1f22ceaf2dc5e7d3b892d4ec` |
| `four_space_odd_local.py` | `e3a8488c434b3e0c6978ce06f1ca1fcef76587e1b6a3ab55d21a1622ab67254b` |
| `hecke_coefficients.py` | `897f51fa566be6312288f5e48552cd44655051a3967cd2123b4e05f6cb95defe` |

The JSON also does not record a PARI/GP executable hash,
version, guarded command, or a standalone raw GP output file. Thus the
embedded status and its hashes are historical evidence whose asserted
comparison logic can be reviewed, not a freshly reproduced execution record.

The current fresh check in
[`h6-quartic-zeta-quotient-report.md`](h6-quartic-zeta-quotient-report.md)
used a different arithmetic route: it obtained prime-ideal e/f profiles
from `idealprimedec` after explicit `nfcertify`, then formed the relative
zeta local factors directly. That fresh method checked only twist `+1`,
through `n=3922`. It is independent method evidence for one row; it does not
refresh the inherited 32-row, 10,000-prefix receipt. Conversely, the
inherited `lfunan` route has broader row/prefix coverage but does not record
an explicit `nfcertify` or direct `idealprimedec` table.

Neither finite route alone proves the all-prime relative zeta/Hecke identity,
the functional equation or contour-growth premises, an AFE tail bound, or
the global target `H`.
