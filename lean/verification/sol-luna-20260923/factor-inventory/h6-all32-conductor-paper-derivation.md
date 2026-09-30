# H6 mask-1586: paper derivation of all 32 relative conductors

This derives the relative discriminant norms and rational conductor values
for the 32 quadratic extensions
`K_D/B`, with `B=Q(√−35)` and `K_D=B(√(Dη))`,
`η=17+2√−35`. It uses the symbolic local cases in
[`h6-all32-good-prime-derivation.md`](h6-all32-good-prime-derivation.md) and
[`h6-all32-p2-p5-symbolic.md`](h6-all32-p2-p5-symbolic.md), together with
the elementary local arguments below. This is a paper-level derivation, not
a Lean proof. PARI comparison is recorded separately as corroborating finite
evidence.

## Relative discriminant away from 2

The base field has fundamental discriminant `disc(B)=−35`, so 5 and 7 are
ramified in `B`, and 2 is unramified inert. The twist set is
`±1, ±2, ±3, ±5, ±6, ±10, ±11, ±13, ±15, ±22, ±26, ±30, ±55, ±65, ±110,
±130`; its prime divisors lie in `{2,3,5,11,13}`. Also
`N_{B/Q}(η)=429=3·11·13`.

At each `p∈{3,11,13}`, the prime splits in `B` since `−35` is a nonzero
square modulo `p`. The ideal `(η)` has valuation one at exactly one of the
two primes over `p`, because its norm has `p`-valuation one. If `p∤D`,
`Dη` therefore has odd valuation at that prime and valuation zero at the
other. If `p|D`, the rational prime `p` has valuation one at both split
primes, so the valuations of `Dη` are two at the `η`-prime and one at the
other. In either case exactly one of the two local quadratic extensions is
ramified, and it has odd valuation radicand. Since `p` is odd, this is
tamely ramified quadratic extension; its relative discriminant exponent is
`e−1=1`. The prime of `B` has norm `p`, so each such rational prime
contributes exactly `p` to
`N_{B/Q}(𝔡_{K_D/B})`. Together these give the factor `3·11·13=429`.

At `p=5`, the unique prime `P` of `B` is ramified over `Q`. The norm 429
shows `η` is a unit there. If `5|D`, then `v_P(D)=2`; otherwise it is zero.
After removing this even valuation, `Dη` is a unit. At odd residue
characteristic, adjoining the square root of a unit gives either a split
algebra or the unramified quadratic extension, according as its residue is
a square or nonsquare. Thus there is no relative discriminant contribution
at 5.

At `p=7`, `D` and `η` are units at the unique prime of `B`: no listed twist
is divisible by 7, and `7∤429`. Again the relative extension is split or
unramified, so 7 contributes no relative discriminant. This includes the
row's deleted prime 7; deletion does not mean ramification.

For every other odd prime, the base is unramified and `Dη` is a unit at all
primes above it. A quadratic extension obtained by adjoining the square root
of a unit in odd residue characteristic is split or unramified. Hence there
are no further odd-prime relative discriminant factors. In particular 17
is unramified in this family despite its inclusion in the deleted-prime
list.

## Exact relative discriminant exponent at 2

Let `L=B⊗Q₂`. It is the unramified quadratic extension of `Q₂`; its
valuation is normalized by `v_L(2)=1`, and its residue field is
`F₄`. Set
`ω=(1+√−35)/2`, so `O_L=Z₂[ω]`, `ω²−ω+9=0`, and
`η=15+4ω`. The polynomial `X²−Dη` has discriminant `4Dη`, of valuation
`2+v_L(Dη)`.

If `D` is odd with `D≡3 (mod 4)`, the earlier Artin–Schreier residue
calculation proves `L(√(Dη))/L` is unramified. Thus the relative
discriminant exponent is zero.

If `D` is odd with `D≡1 (mod 4)`, then `u=Dη` is a unit and
`u≡3 (mod 4O_L)`. The preceding square-class argument shows `u` is
nonsquare, but its class cannot be unramified: any unramified quadratic
extension in residue characteristic two has a square-class radicand
congruent to 1 modulo 4. Therefore this is ramified and its relative
discriminant exponent is 2, provided the order `A=O_L[√u]` is maximal.

If `D` is even, squarefreeness gives `v_L(u)=1`. The extension is
ramified. Its candidate relative discriminant exponent is 3, again
provided `A=O_L[√u]` is maximal.

### Maximality at 2 in the two ramified cases

Here is the index check for `A`. In either case, a proper overorder of `A`
would contain an element of the form
`z=(a+b√u)/2` with `a,b∈O_L` not both divisible by 2: a nonzero finite
`O_L`-module quotient between two rank-two orders has an element killed by
the uniformizer 2. Integrality of `z` requires
`Tr(z)=a∈O_L` and
`N(z)=(a²−b²u)/4∈O_L`.

For odd `D≡1 (mod 4)`, `u` is a unit, `u≡1 (mod 2)`, and
`u≡3 (mod 4)`. If `b` is even, norm integrality forces `a` even, contrary
to the choice of `a,b`. If `b` is a unit, reduction modulo 2 of
`a²≡b²u` gives `(a/b)²=1` in `F₄`; the unique root is 1, so `a/b≡1`
modulo 2 and `(a/b)²≡1 (mod 4)`. Norm integrality then requires
`u≡(a/b)²≡1 (mod 4)`, a contradiction. There is no overorder of index
2, so `A` is maximal and the discriminant exponent is exactly
`v_L(4u)=2`.

For even `D`, `v_L(u)=1`. If `b` is even, then `b²u` is divisible by 4,
and norm integrality forces `a` even. If `b` is a unit, reduction modulo 2
again forces `a` even, but then `v_L(a²)≥2` while `v_L(b²u)=1`, so
`a²−b²u` is not divisible by 4. Both cases contradict the choice of
`a,b`. Thus `A` is maximal and its discriminant exponent is
`v_L(4u)=3`.

This verifies the **relative** local maximality at 2. It does not assert
that the quartic power order `Z[α_D]` is maximal; its index is generally
nontrivial and is computed below.

## Norm, rational conductor, and exact table comparison

Let `e₂(D)` be the relative discriminant exponent at the unique prime of
`B` above 2. The preceding cases give

| twist class | `e₂(D)` | `N_{B/Q}(𝔡_{K_D/B})` | rational `Q_D=35·N_{B/Q}(𝔡_{K_D/B})` |
|---|---:|---:|---:|
| `D` odd, `D≡3 mod 4` | 0 | `429` | `15015=35·429` |
| `D` odd, `D≡1 mod 4` | 2 | `429·4²=429·16` | `240240=35·429·16` |
| `D` even | 3 | `429·4³=429·64` | `960960=35·429·64` |

Since each `K_D` contains the imaginary quadratic field `B`, it has
signature `(0,2)` and positive absolute discriminant. The formula therefore
predicts `disc(K_D)=35·Q_D`, namely `525525`, `8408400`, or `33633600` in
the three rows of the table. These are the exact values for a future fresh
maximal-order discriminant comparison.

The prime over 2 has norm 4, which explains the powers `4^{e₂}` in the
ideal norm; the rational conductor is **not** just the exponent or the
rational prime power `2^{e₂}`. For the quadratic relative Hecke character
`χ_{K_D/B}`, the conductor-discriminant theorem says
`𝔣(χ_{K_D/B})=𝔡_{K_D/B}`. Its **relative ideal** conductor has norm
`N_{B/Q}(𝔣)=N_{B/Q}(𝔡)`. The rational degree-two completed quotient has
conductor
`Q_D=|disc(B)|·N_{B/Q}(𝔣)=35·N_{B/Q}(𝔡)`.
Indeed `|disc(K_D)|=|disc(B)|²·N_{B/Q}(𝔡)`, so equivalently
`Q_D=|disc(K_D)|/|disc(B)|`.

For comparison with the pinned mask-1586 table:

| table `Q` | twist values in that class | count |
|---:|---|---:|
| 15015 | `−65,−13,−5,−1,3,11,15,55` | 8 |
| 240240 | `−55,−15,−11,−3,1,5,13,65` | 8 |
| 960960 | `±2,±6,±10,±22,±26,±30,±110,±130` | 16 |

These are exactly the three conductor classes in
[`h6-low-degree-arithmetic.json`](../../../../publication/nonabelian-dyadic-lower-bound/research/h6-low-degree-arithmetic.json),
SHA-256 `b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`.
The historical all-32 `lfunparams` receipt reports matching row conductors
but lacks raw GP output and fresh run provenance. The new direct all-32
PARI replay certifies quartic maximal orders and finite Euler factors but
does not output discriminants or independently check conductors. A separate
fresh discriminant checker remains deferred by the shared resource guard.
For the quartic polynomial
power-order comparison at 2, the quartic polynomial discriminant has
valuation 12 for odd `D` and 18 for even `D` (since
`disc(P_D)=16·429·560²·D⁶`). Combining with
`|disc(K_D)|=35²N(𝔡)` gives

| twist class | `v₂(disc(P_D))` | `v₂(disc(K_D))` | `v₂([O_{K_D}:Z[α_D]])` |
|---|---:|---:|---:|
| odd, `D≡3 mod 4` | 12 | 0 | 6 |
| odd, `D≡1 mod 4` | 12 | 4 | 4 |
| even | 18 | 6 | 6 |

This computes the quartic power-order index at 2 from the field
discriminant formula; it does not confuse that nontrivial index with the
relative maximality of `O_L[√(Dη)]`. At `D=1`, the resulting index 2-part
is 16, matching the earlier plus-field PARI discriminant/index receipt. At
`D=−1`, the paper formula predicts 64; the fresh all-32 replay did not
record this index.

## Scope

The local argument plus the conductor-discriminant theorem determines the
32 rational conductors on paper. The fresh PARI all-32 maximal-order
certification supports the field/order and finite local-factor data, but
is not an independent recorded discriminant/conductor comparison and is
not an input to the displayed relative discriminant calculation. This note does not prove
in Lean the field presentations, relative integral-basis results, or
conductor-discriminant theorem. Nor does it by itself identify the rows as
factors of the completed target field or establish their functional
equations, analytic growth, or AFE bounds.
