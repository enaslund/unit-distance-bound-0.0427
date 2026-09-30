# Independent review: plus-field bridge for H6 twist `+1`

## Scope

I inspected the staged Lean source
`UnitDistance/HeckeManuscriptMixedQuadratic1586PlusFieldBridge20260923.lean`
and the imported definitions it specializes. I did not compile it or inspect
any numerical run. The review asks what the theorem establishes about the
actual field `B(√η)` and the H6 arithmetic row with twist `+1`.

## What the source proves, if it compiles

The imported arithmetic source defines `B = Extension (-35 : ℚ)` and
`η = ⟨17,2⟩ : B`, with rational norm `429` and a proof that 429 is not a
rational square (arithmetic source lines 27–62). The new `eta_nonsquare`
argument applies the field norm to a hypothetical square equation and
correctly transfers that obstruction to `η` (new source lines 24–32).
Consequently `PlusFactorField := Extension η` is the literal relative
quadratic algebra `B(√η)`, and `plusFactorField_relative_degree` specializes
the existing relative-degree theorem (lines 34–40).

`plusFactor_local_euler` then instantiates the generic identity for a
quadratic extension at every height-one prime `𝔭` of `𝓞 B` (lines 42–52):

\[
 \prod_{\mathfrak P\mid\mathfrak p}(1-(N\mathfrak P)^{-s})
 =(1-(N\mathfrak p)^{-s})(1-\epsilon_+(\mathfrak p)(N\mathfrak p)^{-s}),
\]

where `ε₊` is the split/inert/ramified value
`quadraticPrimeSignAll` from the generic module. This identity has the right
local cases for a relative quadratic extension: signs `+1`, `−1`, and `0`
give respectively two degree-one factors, one degree-two factor, and one
ramified degree-one factor. It is a local denominator identity over `B`.

## Relation to the numerical twist `+1`

The pinned H6 arithmetic data in
`publication/nonabelian-dyadic-lower-bound/research/h6-low-degree-arithmetic.json`
has a twist `+1` row with conductor `240240`,
gamma `[0,1]`, and root number `+1`. The new bridge does not mention this
row's coefficient sequence, conductor, gamma factor, or root number; it
contains no rational-prime Euler factor or coefficient theorem. Its own
module comment at lines 7–10 expressly leaves the H6 row identification and
all-`n` majorant open. Thus `B(√η)` is a mathematically plausible intended
field for that numeric twist, but this source does not establish the match.

It is especially important not to transfer the existing `FactorField`
results automatically. The imported manuscript source defines `beta = -eta`
as its `D=-1` field and records conductor `15015` (arithmetic source lines
38–43 and 125–134). The new
source instead uses `eta`, while the same imported file proves `−1` is
nonsquare in `B`. Since `eta/beta = -1`, the two radicands
are in distinct squareclasses over `B`; these are different quadratic
extensions over `B` (the nonsquareness of `−1` is proved at arithmetic source
lines 85–103). Any use of the old beta-field ray character, prime
values, conductor, or Euler identities therefore needs a new bridge.

The next missing identity is a **rational-prime local factor comparison**.
For every rational prime `ℓ`, group the relative factors over all
`𝔭 | ℓ` in `B`, including the ramified/bad cases, and prove that the result
equals the arithmetic twist-`+1` local polynomial from the H6 table. At
unramified primes this requires identifying the two induced Frobenius
eigenvalues (and hence trace and determinant) with that row's local
coefficients; it is not enough to identify only the split/inert sign at one
base prime. The listed local data at 17 must also be matched even though 17
does not divide the row conductor. After that, a multiplicative/all-prime
power-coefficient argument is still needed to prove the global
`|a_n| ≤ d₂(n)` bound used by the numerical tail.

## Lean risks and assessment

The proof steps are short and the generic theorem application appears to
match `quadratic_primeFiber_factor_product`'s explicit parameters. The norm
obstruction mirrors the imported `beta_nonsquare` proof, so I see no obvious
local proof error by inspection. It remains uncompiled; the `#print axioms`
commands at lines 54–56 request an audit but are not themselves compile or
axiom-audit results.

One API risk for follow-on files is that `plusEtaNonsquareFact` is declared
`private` (line 34). This supplies the field/number-field instances inside
this file, but downstream source cannot rely on that instance being exported
when it asks Lean to synthesize operations or `NumberField PlusFactorField`.
Expose a reusable instance or locally reconstruct it from `eta_nonsquare` in
the consumer. This does not invalidate the local theorem's mathematical
content.

Conclusion: this is a plausible, appropriately scoped first endpoint for the
actual plus-radicand extension and its relative local factor identity. It
does not yet prove that the field quotient is the H6 numerical twist-`+1`
factor, nor does it transfer the numerical AFE or tail assumptions into Lean.
No build was run; worker resource counters are unavailable, not zero.
