# Kronecker bridge attempt

## Status

I did not complete the requested all-mask identification

```text
genusPrimitiveCharacter m n = χ_D(n),
D = expectedGenusFundamentalDiscriminant m,
```

for a standard Kronecker character `χ_D`. I found no sign or conductor
counterexample. The remaining proof obligation is multiplicative: identify
the pointwise product of the local primitive characters in `assembledDatum`
with the signed-discriminant Kronecker symbol, including the 2-primary factor
and values at nonunits.

## What is proved in the source tree

`GenusDirichletRootNumbersActualRun20260920b.lean:1047–1055` already proves
for every mask and every integer that the actual primitive character equals
`(assembledDatum m).χ`. The conductor-13 specialization proves for every
integer that this character equals `primeQuadraticCharacter 13`, and the
manuscript mask theorem identifies its expected discriminant as 13
(`ZetaLunaConductorThirteenManuscriptRowRun20260923.lean:38–53`). This
specialization includes the seven selected primes because its hypothesis is
just `n : ℤ`.

I added
`UnitDistance/GenusLunaKroneckerBridgeRun20260923.lean` to expose these two
pointwise results together. It states no unproved assumptions, axioms, or
`sorry`s. It does not claim the general Kronecker identification.

## Why the general proof did not close

The existing construction proves exact primitive conductors from the
2-primary and five odd-prime pieces (`GenusDirichletConductorsRun20260920.lean`
and `GenusDirichletRootNumbersActualRun20260920b.lean:870–1000`). Those
conductor equalities alone do not determine a quadratic character. The
pointwise assembled-character theorem reduces the requested result to
showing that the assembled local values multiply to the Kronecker value for
the signed product radicand. That final symbol-factorization theorem is not
present in the inspected source. Proving only equality on primes outside the
common modulus would also fail to bridge the selected-prime correction
factors used by the Arb receipt.

A direct proof route is to factor the fundamental discriminant as
`D = D₂ · ∏q q`, where the odd `q` range over the selected subset of
`{3,5,7,11,13}` and `D₂ ∈ {1, -1, -4, 4, 8, -8}` is the corresponding
2-primary factor. The desired Kronecker value then factors as
`(D₂/n) · ∏q (q/n)`. The assembled local odd characters instead evaluate
`(n/q)`. For `q = 3,7,11`, the local `χ₄` factor combines with `(n/q)` to
convert it to `(q/n)`; `GenusDirichletReciprocityRun20260920.lean:39–85`
proves these sign conversions away from the selected primes. The generic
proof must extend the identities to all integers and track zeros when `n`
is divisible by a selected odd prime or by 2 when `D₂` is even. In particular,
the factor `(−1/n)` for `D₂ = -1` is not itself a Dirichlet character modulo
one; its product with the odd factors is what gives the primitive character.
No such all-integer factorization theorem was completed here.

There is a useful support caveat. Mathlib's
`DirichletCharacter.primitiveCharacter_apply_of_isCoprime` (pinned
`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:328–330`) compares the
primitive reduction with the original character only when the input is
coprime to the original character's level. For the common-level genus
character this means coprime to 2,042,040, which excludes 17. It cannot by
itself handle `n = 17`, where `gcd(n, |D|) = 1`, the primitive Kronecker value
is nonzero, and the imprimitive common-level value is zero. The assembled
primitive local product is needed to keep that value.

The exact missing bridge can be stated without assuming a Mathlib
`kroneckerSym` API: after defining `explicitKroneckerFactorization m n` from
the above signed factorization using `jacobiSym` on the odd part and the
separate valuation-at-2 correction, the theorem needed is

```text
theorem assembledDatum_apply_eq_explicitKroneckerFactorization
    (m : GenusCharacterIndex) (n : ℤ) :
    (assembledDatum m).χ n = explicitKroneckerFactorization m n
```

with `explicitKroneckerFactorization m n = (D₂/n) · ∏q (q/n)` in standard
Kronecker notation. `jacobiSym` alone on arbitrary `n` is insufficient:
Mathlib defines it using prime factors with multiplicity and documents that
it agrees with the ordinary Jacobi symbol only for odd denominators. Its
Legendre symbol at 2 does not supply the Kronecker supplementary factor, so
the 2-adic correction must be handled separately (pinned
`Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:10–14, 68–88`).
Together with `genusPrimitiveCharacter_apply_eq_assembled`, this would identify every
primitive Lean row at every integer, including the selected primes.

## Build status and scope

No Lean build was started. The parent reserved the next Lean slot for chi7
retries, then a short-row bridge and chi5; I was asked to wait for a signal
before compiling this file. It is therefore source-reviewed but not
compile-verified. No FLINT or Arb run was performed by this task. The D=13
pointwise theorem is an existing one-row result, not evidence that all 128
Python rows are already identified with the Lean primitive characters.
