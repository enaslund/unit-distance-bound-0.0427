# Paper-level factorization of the 128 primitive characters

## Statement

Write the seven mask bits as

```text
a = m 0   (-1)       b = m 1   (2)
c = m 2   (3)        d = m 3   (5)
e = m 4   (7)         f = m 5   (11)
g = m 6   (13).
```

Each displayed bit is read as its value in `{0,1}`. Put

```text
O = 3^c 5^d 7^e 11^f 13^g,
u = c + e + f (mod 2),
r = a + u (mod 2),
δ = (-1)^a 2^b O.
```

Here `u` is the parity of the selected odd primes that are `3 mod 4`, and
`r` is exactly `chi4MaskParity m` from the Lean development. The row's
fundamental discriminant is

```text
D = δ       if δ ≡ 1 (mod 4),
D = 4 δ     otherwise.
```

This is the formula implemented by `expectedGenusFundamentalDiscriminant`
from the ordered signed radicands in
`GenusDirichletRowDataRun20260920.lean:30–40, 66–76`.

The four cases are therefore:

| `b` | `r` | `D` | `twoDatum` character |
|---:|---:|---|---|
| 0 | 0 | `(-1)^a O` (odd, `1 mod 4`) | trivial character mod 1 |
| 0 | 1 | `4(-1)^a O` | `χ₄`, the primitive character of `-4` |
| 1 | 0 | `8(-1)^a O` | `χ₈`, the primitive character of `8` |
| 1 | 1 | `8(-1)^a O` | `χ₈'`, the primitive character of `-8` |

In the last two rows, `r` need not equal `a`: the `χ₄` factors attached to
the selected primes `3,7,11` account for the difference.

Define the odd local product and the 2-primary factor by

```text
A_m(n) = ∏_{q ∈ {3,5,7,11,13}} (n/q)^{bit(q)},
T_m     = 1, χ₄, χ₈, χ₈' according to the table.
```

Here `(n/q)` is the ordinary Legendre symbol, including its zero value when
`q ∣ n`. For positive `n`, the paper-level identity is

```text
(assembledDatum m).χ n = T_m(n) A_m(n) = (D/n).
```

The right side is the Kronecker symbol, with its usual extension to integer
character arguments (so its value at a negative argument includes the
character's parity). At `n = 0`, use the conventional value `(1/0)=1` and
`(D/0)=0` for `D ≠ 1`.

## Why the assembled character has these atoms

The following parts of the factorization are already represented in Lean.

* `GenusDirichletRootNumbersActualRun20260920b.lean:28–91` defines the
  optional primitive odd atoms at moduli `3,5,7,11,13`; each selected atom is
  `primeQuadraticCharacter q`. `GenusDirichletCharacterBridge.lean:33–36`
  defines that character as the cast of `quadraticChar (ZMod q)`. Unfolding
  this definition identifies its value at `n : ℤ` with `legendreSym q n`,
  i.e. `(n/q)`, including zero when `q ∣ n`.
* `GenusDirichletRootNumbersActualRun20260920b.lean:150–151` defines
  `optionalDatum`: an unset bit contributes the level-one trivial datum, and
  a set bit contributes its corresponding odd atom. The nested products
  `oddDatum35`, `oddDatum357`, `oddDatum35711`, and `oddDatum` assemble these
  factors (`:438–644`).
* The parity `r` is Lean's `chi4MaskParity` in
  `GenusDirichletConductorsRun20260920.lean:308–316`. The case definition of
  `twoDatum` is `GenusDirichletRootNumbersActualRun20260920b.lean:648–651`;
  its atoms are `datumOne`, `datumFour`, `datumEight`, and `datumEightPrime`
  (`:18–25, 93–139`). They use the characters `χ₄`, `χ₈`, and `χ₈'`.
  `Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean:72–82, 150–189`
  gives their residue-class values and the relation `χ₈' = χ₄ χ₈`. In
  particular, on odd arguments these are respectively `(-1/n)`, `(2/n)`,
  and `(-2/n)`; `χ₄`, `χ₈`, and `χ₈'` vanish on even arguments.
* `assembledDatum` is `oddDatum` composed with `twoDatum` in
  `GenusDirichletRootNumbersActualRun20260920b.lean:870–878`. Its primitive
  modulus is the expected conductor
  (`assembledModulus_eq_expected`, `:958–962`). The existing pointwise theorem
  `datumAt_primitiveCharacter_apply` (`:1027–1034`) and its actual-family
  wrapper `genusPrimitiveCharacter_apply_eq_assembled` (`:1047–1055`) already
  prove, for every mask and integer, that the Lean primitive character is
  `(assembledDatum m).χ`.

The composition structures combine characters by coprime products. Expanding
`coprimeProduct` from `GenusDirichletDatumCompositionRun20260920b.lean:22–27`
shows why the local formula preserves support at every integer: on units of
the product modulus, level changes preserve each local value; on nonunits,
some local factor and the product character both vanish. A generic pointwise
lemma spelling out this expansion is a formalization step; there is no
existing theorem in the inspected files that directly states
`(assembledDatum m).χ n = T_m(n) A_m(n)`.

## Symbol calculation

Let `t` be the integer parity representative `u ∈ {0,1}`. On odd `n` coprime
to `O`, quadratic reciprocity gives

```text
∏q (n/q) = (O/n) χ₄(n)^t.
```

Indeed, the supplementary sign in reciprocity is present precisely for the
selected `q = 3,7,11`; each contributes `χ₄(n)`, while `q = 5,13` contributes
no sign. The three existing lemmas
`chiFour_mul_reciprocal_three`, `chiFour_mul_reciprocal_seven`, and
`chiFour_mul_reciprocal_eleven` in
`GenusDirichletReciprocityRun20260920.lean:39–85` prove the corresponding
prime-input identities. Extending those identities multiplicatively from
primes to arbitrary odd `n` is not yet a Lean theorem in the inspected
source.

For odd `n`, the table gives

```text
T_m(n) = (2/n)^b χ₄(n)^r.
```

Since `r ≡ a+t (mod 2)`, multiplication by `A_m(n)` yields

```text
T_m(n) A_m(n)
  = (2/n)^b χ₄(n)^(r+t)
      (O/n)
  = (2/n)^b (-1/n)^a (O/n).
```

If `b=0,r=0`, then `D=(-1)^a O` and this is `(D/n)`. If `b=0,r=1`, then
`D=4(-1)^a O`; for odd `n`, `(4/n)=1`, so it is again `(D/n)`. If `b=1`,
then `D=8(-1)^a O`; for odd `n`, `(8/n)=(2/n)`, giving the same identity.

If `n` is even and `D` is even (the cases `b=1` or `b=0,r=1`), the
Kronecker symbol is zero and the selected `χ₈`/`χ₈'` or `χ₄` atom is zero.
If `n` is even and `D` is odd, then `b=0,r=0` and `D=(-1)^a O ≡ 1
(mod 4)`. Quadratic reciprocity for this fundamental discriminant gives
`(D/n) = (n/O)`, including the 2-adic contribution to the Jacobi symbol in
the numerator. Multiplicativity of the ordinary Jacobi symbol in its first
argument identifies `(n/O)` with `A_m(n)`. If an odd selected `q` divides
`n`, both sides instead vanish by the local `q` factor. These cases give the
identity for all positive `n`.

For negative `n`, multiplicativity of the characters reduces to the positive
case: `T_m(-1)=(-1)^r` and `A_m(-1)=(-1)^t`, so the assembled value at `-1`
is `(-1)^{r+t}=(-1)^a`, the parity of the discriminant character. At `n=0`,
if any odd bit is selected then `A_m(0)=0`; otherwise the only masks have
`D ∈ {1,-4,8,-8}`, and the table gives value 1 for `D=1` and 0 for the
other three discriminants.

## Formalization boundary and the auxiliary prime 17

The preceding identity is a paper-level deduction, not an existing Lean
theorem. The exact missing bridge is the pointwise assembly formula
`(assembledDatum m).χ n = T_m(n) A_m(n)` together with the all-integer
quadratic-reciprocity/supplementary-law argument above. The existing prime
reciprocity lemmas cover the selected-prime-excluded prime inputs, not the
whole statement.

The identity does cover the deletion factors at all seven selected primes.
At `2,3,5,7,11,13`, the character is zero exactly when that prime divides
`|D|`; otherwise its value is the Kronecker sign. At `17`, no factor of `D`
can be 17, so the value is always `±1`. This distinction is necessary:
`17` divides the common level `2042040`, but not any expected primitive
conductor. Lean proves the common-level prime set is
`{2,3,5,7,11,13,17}` in
`GenusDirichletPrimitiveRun20260920.lean:132–136`; the primitive deletion
factor in that file uses the primitive character value at each of those
primes (`:159–171`). The common-level character's value zero at 17 cannot
replace the primitive value used by the numerical correction.

No Lean file was edited by this note and no build was run.

## Worker usage

No per-worker CPU or peak-RAM measurement was available for this
source-level task; those values are unavailable, not zero. No Lean build or
numerical computation was run.
