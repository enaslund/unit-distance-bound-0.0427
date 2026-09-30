# Read-only bridge review: direct replay of 128 genus factors

## Finding

The script's mask convention, signed radicands, discriminants, and seven
selected primes match the corresponding Lean definitions. I found no mask
or sign mismatch. The remaining gap is an exact character-value
identification: the script verifies its FLINT Conrey character against the
Kronecker symbol for its own discriminant, but the inspected Lean chain does
not identify that character with `genusPrimitiveCharacter m` (or the
assembled Lean primitive character) for every mask. Thus this is a strong
independent numerical re-evaluation of the intended 128 factors, but it is
not yet a theorem-level replay of the 128 Lean primitive factors.

## Index and discriminant match

`genus_full_direct.py:26–30, 64–85, 133–145` uses the ordered list
`(-1,2,3,5,7,11,13)`, bit `j` as weight `2^j`, and
`D=d` when `d ≡ 1 mod 4`, otherwise `D=4d`; it then uses `|D|` as the
conductor. This matches
`GenusDirichletRowDataRun20260920.lean:25–81`: `GenusMaskIndex` is
definitionally the same `Fin 7 → ZMod 2` type as the actual
`GenusCharacterIndex`, the row radicands have the same order, and
`genusMaskValue` plus `explicitGenusMaskEquivFin` fix the same little-endian
mask convention. The explicit Lean checks at masks 0, 126, and 127 give
`1`, `120120`, and `-120120` (`:83–93`), agreeing with the script's
formula. The table's conductor sum `677376` and full-mask conductor bound
are also kernel-checked in Lean (`:100–109`).

The script pins these four Lean source files by SHA256 and compares each
archived row's mask, `D`, and Conrey label (`genus_full_direct.py:31–46,
133–145`). This prevents a quiet data-row reorder for the sources at those
hashes.

## What the Lean character chain establishes

`GenusDirichletCharacterBridge.lean:34–63` defines the seven common-level
generators in the same order: `χ₄`, `χ₈`, `χ₄χ₃`, `χ₅`, `χ₄χ₇`, `χ₄χ₁₁`,
`χ₁₃`. `GenusDirichletConductorsRun20260920.lean:49–76` repeats those
definitions, and `GenusDirichletConductorsActualRun20260920.lean:26–59`
proves they and their products agree with the arithmetic `genusDirichletCharacter`.
`GenusDirichletReciprocityRun20260920.lean:39–85` proves the three
nontrivial reciprocal identities which turn `χ₄χ₃`, `χ₄χ₇`, and `χ₄χ₁₁`
into the expected Legendre symbols away from the selected primes.

The factor theorem
`GenusDirichletFactorsRun20260920.lean:137–204` identifies the 128 actual
coherent genus Euler products with the common-level Dirichlet `L`-series.
The actual-conductor result is
`GenusDirichletConductorsActualRun20260920.lean:53–87`, and
`GenusDirichletPrimitiveActualRun20260920.lean:30–61` transports the
primitive character to the expected conductor type and states the primitive
times deletion-factor expression. `GenusDirichletPrimitiveRun20260920.lean:110–184`
defines that primitive character and its correction

\[
\prod_{p\mid 2042040}(1-\chi_m^*(p)p^{-s}),
\]

with the prime-factor set proved to be exactly `{2,3,5,7,11,13,17}`.

That chain establishes the conductor and the deletion formula, but a
conductor alone does not determine a quadratic character. The nearest
pointwise theorem I found,
`GenusDirichletRootNumbersActualRun20260920b.lean:1047–1055`, identifies
the primitive character with `assembledDatum m).χ`; that datum is assembled
from the five odd prime quadratic characters and the 2-primary character.
It does not identify its values with the script's signed-discriminant
Kronecker character or Conrey label. The source itself describes a
conductor identification, not a rowwise character identification
(`GenusDirichletRowDataRun20260920.lean:7–13, 124–129`).

## Exact missing bridge

The useful missing theorem is a pointwise equality, for each mask `m` and
integer `n`, between the actual primitive character and the Kronecker
character of the discriminant already defined in `RowData`, for example

```text
genusPrimitiveCharacter m n = χ_D(n),
  where D = expectedGenusFundamentalDiscriminant m
  and χ_D is the explicit Kronecker/primitive quadratic character of D
```

or the equivalent equality with the explicit primitive quadratic
`DirichletCharacter` of conductor
`expectedGenusPrimitiveConductor m`. It should include nonunits and the
selected primes, since the script checks a whole period and evaluates the
seven deletion factors there. Proving equality only for primes outside the
common modulus would identify the coherent unramified Euler factors but
would leave the primitive values at selected primes unbridged.

The seven-prime set itself does match: `2042040.primeFactors` is proved to
be `{2,3,5,7,11,13,17}` in
`GenusDirichletPrimitiveRun20260920.lean:132–171`, and the script uses the
same tuple (`genus_full_direct.py:25–27`). Its correction has the expected
`1 - χ(p)p^{-σ}` form. For primes dividing the primitive conductor, the
Kronecker value is zero and the correction factor is one; at 17, which is
in the common level but not in a genus radicand, the value is generally
nonzero and the correction remains necessary. The Lean deletion product
has this same structure, but the pointwise character-value bridge above is
needed to conclude the script evaluates exactly those Lean factors.

## Scope

This review inspected source only. I did not run the FLINT script or modify
it. The script's own docstring states that it does not prove the
Lean-to-Conrey identity (`genus_full_direct.py:1–12`); my source trace
confirms that this is the precise missing theorem rather than a detected
mask/sign error. No claim is made here about correctness of FLINT's Arb
evaluation or the inherited AFE certificate.
