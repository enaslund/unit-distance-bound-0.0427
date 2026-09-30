# H6 mask-1586: symbolic local signs at 2 and 5

This addendum sharpens the bad-prime analysis in
[`h6-all32-remaining-bad-local.md`](h6-all32-remaining-bad-local.md). It gives
closed local rules for the exact row denominators at `2` and `5`, and checks
them against all 32 pinned twists. The local argument is paper-level
quadratic local-field arithmetic; the comparison is a separate small exact
read of the pinned JSON. Neither is a Lean proof.

Throughout, `B=Q(√−35)`, `η=17+2√−35`, and
`K_D=B(√(Dη))`. Write `E_{D,p}=D_{K_D,p}/D_{B,p}` with the denominator
convention in the parent note.

## The dyadic factor

The completion `L=B⊗Q₂` is the unramified quadratic extension of `Q₂`, since
the fundamental discriminant `−35` is odd and `−35 ≡ 5 (mod 8)`. Put
`ω=(1+√−35)/2`; its polynomial is `X²−X+9`, which is irreducible modulo 2,
so `O_L=Z₂[ω]` and `O_L/2O_L ≅ F₄`. In this ring

`η=15+4ω`.

If `2|D`, squarefreeness gives `v_L(Dη)=1`; adjoining its square root is
ramified. The unique prime of `B` over 2 has rational residue degree two,
and a ramified relative quadratic extension has the same residue degree.
Thus `D_{K_D,2}=D_{B,2}=1−T²` and `E_{D,2}=1`.

Now let `D` be odd. In `L×/(L×)²`, its class is `1` when
`D≡1 (mod 4)` and `−1` when `D≡3 (mod 4)`. Indeed, `5` is a square in `L`
because `−35/5=−7 ≡1 (mod 8)` is a square in `Q₂`. Every odd rational
integer congruent to 1 modulo 4 is congruent to 1 or 5 modulo 8, hence is a
square in `L`; for `D≡3 (mod 4)`, `−D≡1 (mod 4)` and the same argument shows
that `D` has the class of `−1`.

For `D≡1 (mod 4)`, `Dη` has the class of `η`. Since `η≡3 (mod 4O_L)`, it
cannot be a square: its reduction modulo 2 is 1, so any square root would
reduce to 1 in `F₄`, and a unit of the form `1+2y` squares to 1 modulo 4.
It also cannot define the unramified quadratic extension. An unramified
quadratic extension in residue characteristic two has a generator
`θ` with `θ²−θ−a=0` and irreducible reduction; then
`(2θ−1)²=1+4a`, so its square-class radicand has a representative
congruent to 1 modulo 4. Multiplication by a square does not change this
congruence for a unit reducing to 1 modulo 2. Thus `L(√η)/L` is ramified,
and `E_{D,2}=1`.

For `D≡3 (mod 4)`, `Dη≡1 (mod 4O_L)`, so write `Dη=1+4a`, where
`a=(15D−1)/4 + Dω`. Modulo 2, the coefficient `(15D−1)/4` lies in the
prime field `F₂` and has absolute trace zero from `F₄`; `ω mod 2` has trace
one because it satisfies `X²+X+1`. Therefore `Tr_{F₄/F₂}(a)=1`. The element
`θ=(1+√(Dη))/2` satisfies `θ²−θ−a=0`; modulo 2 this becomes the
irreducible Artin–Schreier polynomial `Y²+Y+ā` over `F₄`. Thus this is the
unramified quadratic extension of `L`, not a split one. Its residue degree
over `L` is two, so the top-field prime has rational residue degree four
and

`E_{D,2}=(1−T⁴)/(1−T²)=1+T²`.

Consequently the exact dyadic rule is

`E_{D,2}(T) = 1+T²` if `D` is odd and `D≡3 (mod 4)`;
`E_{D,2}(T) = 1` otherwise.

This conclusion classifies the local extension, not just the denominator:
the `E=1` cases are ramified (both even `D` and odd `D≡1 mod 4`) in this
family. The denominator comparison alone would not distinguish a split
extension from a ramified one in general.

The eight twists predicted to have `1+T²` are
`{−65,−13,−5,−1,3,11,15,55}`. This exactly matches the pinned JSON.

## The factor at 5

Let `P` be the unique prime of `B` above 5 and set `π=√−35`. The prime is
ramified, `π` is a uniformizer, and `π²=−35=−5·7`, so
`5=−π²/7`. The residue field is `F₅`, with `π≡0` and
`η=17+2π≡2 (mod P)`. Thus `η` is a unit at `P`.

If `5∤D`, the local square class of `Dη` is the unit whose residue is
`2D mod 5`. Define
`λ_D=(2D/5)`, the ordinary Legendre symbol. If `5|D`, write `D=5d`; since
the twists are squarefree, `d` is a 5-adic unit. Removing the square
`π²` from

`Dη=5dη=π²(−dη/7)`

leaves a unit with residue `−d≡4d` in `F₅`, since `η≡2` and `7≡2`. As
`−1` is a square modulo 5, define `λ_D=(d/5)` in this case. In both cases
`λ_D=+1` means the relative
quadratic extension at `P` splits; `λ_D=−1` means it is the unramified
quadratic extension. (The radicand has even valuation in both cases, and at
odd residue characteristic a unit has exactly these two quadratic
possibilities.) Therefore

`E_{D,5}(T)=1−λ_D T`. Equivalently, when `5∤D`,
`λ_D=(2D/5)=−(D/5)`, since 2 is a nonsquare modulo 5.

In particular, the pinned `1−T` twists are exactly
`{−130,−55,−30,−22,−13,−5,−3,−2,2,3,5,13,22,30,55,130}`;
all other listed twists have `1+T`. This is exactly the row table's
classification.

## Exact comparison and scope

A read-only script compared these two formulas against each of the 32
`bad_euler_denominators` entries in the pinned arithmetic JSON
(SHA-256 `b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`).
It reported `PASS 64 exact p=2/p=5 row comparisons across 32 twists`.
This is a direct arithmetic transcription check, independent of the PARI
decomposition. The all-32 certified maximal-order PARI receipt separately
checks each quotient denominator against the actual field decompositions.

The square-class arguments explain the local signs symbolically for this
two-prime subset. The complementary
[split-prime note](h6-all32-p3-p11-p13-symbolic.md) now performs the
corresponding residue-unit calculation at `3,11,13`; the separate
[p=7](h6-all32-p7-local.md) and [p=17](h6-all32-p17-symbolic.md) notes
cover the other two listed primes. None of these local arguments alone gives an all-prime completed
factor identity or Lean proof.
