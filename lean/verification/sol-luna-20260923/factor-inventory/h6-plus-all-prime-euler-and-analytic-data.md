# H6 mask 1586, twist `+1`: local factors and standard analytic package

This is a paper-level derivation for the proposed plus field
`B = Q(√−35)`, `η = 17 + 2√−35`, `F = B(√η)`, with
`P(X) = X⁴ − 34X² + 429`. It is separate from the finite numerical AFE
replay and from a Lean proof. The main conclusion is conditional only at the
global identification point: once the row is identified with
`ζ_F(s)/ζ_B(s)`, its all-prime Euler denominators are the ones below.

## Good-prime Euler denominator

For a number field `K`, write
`D_{K,p}(T) = ∏_{𝔭|p}(1 − T^{f(𝔭/p)})`. Thus the local factor of
`ζ_K(s)` is `1/D_{K,p}(p⁻ˢ)`. The local factor of `ζ_F/ζ_B` is therefore
`1/E_p(T)`, where `E_p = D_{F,p}/D_{B,p}`.

Set `S = {2,3,5,7,11,13,17}`. The polynomial discriminant is

`disc(P) = 16·429·(34² − 4·429)² = 2,152,550,400`,

whose prime support is `{2,3,5,7,11,13}`. Also `disc(B) = −35`.
Since the field discriminant divides the discriminant of the power order,
every `p ∉ S` is unramified in both fields, and `p` divides neither 35 nor
429. Consequently
`a = (−35/p)` and `b = (429/p)` are each `±1`.

The identities `N_{B/Q}(η)=429` and
`ηη̄ = 429` are exact. They also show `η` is not a square in `B`: if
`η = u²`, then `429=N(u)²` would be a square in `Q`, which it is not.
Thus `F/B` is a nontrivial quadratic extension. If `α²=η`, then
`α⁴−34α²+429=0` and `√−35=(α²−17)/2`, so `P` presents this quartic
field. The staged Lean plus-field bridge has not been compiled; the PARI
receipt cited below independently checks this presentation and its field
data.

There are two residue-field cases.

1. **`a=1` (p splits in B).** Choose `r∈F_p` with `r²=−35`. The two
   residue fields of `B` are `F_p`, and the two residues of `η` are
   `u₊=17+2r` and `u₋=17−2r`. They are nonzero and
   `u₊u₋=429`, so their Legendre symbols `ε₊, ε₋` satisfy
   `ε₊ε₋=b`. At a split base prime with residue `u`, the relative quadratic
   extension splits if `(u/p)=1`, contributing quotient denominator
   `(1−T)`, and is inert if `(u/p)=−1`, contributing `(1+T)`; in either
   case that contribution is `1−(u/p)T`. Hence
   `E_p(T)=(1−ε₊T)(1−ε₋T)`. If `b=1`, the two signs agree, and writing
   their common value as `ε=(17+2r/p)` gives
   `E_p(T)=1−2εT+T²`. The common-sign fact also makes this independent of
   which square root `r` was chosen. If `b=−1`, the signs are opposite and
   `E_p(T)=1−T²`.

2. **`a=−1` (p is inert in B).** There is one prime of `B` over `p`, with
   residue field `F_{p²}` and norm `p²`. Frobenius on this residue field is
   the nontrivial conjugation of `B/Q`; hence for the residue `u` of `η`,
   `N_{F_{p²}/F_p}(u)=u^{p+1}=u·ū=429`. Its quadratic character in
   `F_{p²}` is therefore
   `u^((p²−1)/2) = (N(u))^((p−1)/2) = b`.
   If this sign is `+1`, the relative prime splits and its quotient
   denominator is `1−T²`; if it is `−1`, it is inert and the quotient
   denominator is `(1−T⁴)/(1−T²)=1+T²`. Thus in both cases
   `E_p(T)=1−bT²`.

Combining the cases gives exactly the mask-1586 twist-`+1` rule in
[`next-dyadic-h5-single.py`](../../../../publication/six-dimensional-lower-bound/research/next-dyadic-h5-single.py),
lines 131–142: when `a=b=1`,
`E_p(T)=1−2εT+T²`; otherwise
`E_p(T)=1+abT²`. In the inert case this is `1−bT²` because `a=−1`;
in the split case outside `a=b=1`, one has `a=1,b=−1` and obtains
`1−T²`. In particular this calculation is for the relative zeta quotient;
it does not assume that `F/Q` is Galois or invoke a two-dimensional Artin
representation of `Gal(F/Q)`.

The exceptional-prime table used by the replay is

| p | `E_p(T)` |
|---:|:---|
| 2 | `1` |
| 3 | `1−T` |
| 5 | `1+T` |
| 7 | `1+T` |
| 11 | `1−T` |
| 13 | `1+T` |
| 17 | `(1−T)²` |

These seven entries are supported by the exact finite PARI maximal-order
calculation in
[`h6-plus-quartic-pari-status.md`](h6-plus-quartic-pari-status.md) and its
receipt, not by the good-prime argument. In particular, 17 is included in
the deleted set for compatibility with the replay although it is not in the
displayed polynomial or base discriminant support.

The pinned `next-dyadic-h5-single.py` routine `prime_data` defines the good
prime polynomials by precisely the rule proved above, and its `coefficients`
routine uses those polynomials together with the seven bad polynomials in
`h6-low-degree-arithmetic.json`. Hence the good-prime derivation plus the
seven exact PARI checks identify the **code-defined row's formal Euler
product** with the relative quotient at every rational prime, subject to
the stated field/order computation and source pins. The finite
3922-coefficient comparison is a separate cross-check of that conclusion.
This paper-level source-to-field identification is not a Lean theorem and
does not identify the row as a factor of the degree-16384 completed field
embedded in the degree-524288 retained field.

## All-coefficient `d₂` majorant

For the code-defined row, the preceding local comparison supplies these
factors at every prime, with the finite PARI and source-pin scope stated
there. Its coefficients are multiplicative and its local series are
`1/E_p(T)`. At a good prime with `a=b=1`, `ε=±1` and
`E_p=(1−εT)²`; the coefficient of `T^k` in the inverse is
`(k+1)ε^k`, of absolute value `k+1`. At every other good prime,
`E_p=1+cT²` for `c=ab=±1`; the inverse has zero odd coefficients and
even coefficients of absolute value 1. These are bounded by `k+1` at
degree `k`.

For the exceptional factors, inverses of `1`, `1±T` have coefficients of
magnitude at most 1, while `(1−T)⁻²` has coefficient `k+1`. Thus all
primes satisfy `|a_{p^k}|≤k+1`. Multiplicativity and
`d₂(n)=∏_{p^k∥n}(k+1)` then give `|a_n|≤d₂(n)` for every `n≥1`.
This is an all-`n` paper-level deduction from the stated all-prime Euler
identity; a finite prefix replay alone does not establish its hypothesis.

## Standard completed Hecke factor: what follows on paper

Because `F/B` is a nontrivial quadratic extension, it has a nontrivial
quadratic finite-order Hecke character `χ_{F/B}`. The standard relative
zeta identity gives
`L_B(s,χ_{F/B}) = ζ_F(s)/ζ_B(s)` initially for `Re(s)>1`. By the standard
analytic continuation theorem for nontrivial finite-order Hecke
characters, this relative factor is entire; its completed functional
equation follows from the Hecke functional equation. Equivalently, after
the field and character identity is established, the quotient of the two
Dedekind zeta functional equations gives sign `+1`.
The analytic continuation and functional-equation theorem invoked here is
treated in [Tate's thesis, Chapter XV of *Algebraic Number Theory*](https://math.arizona.edu/~cais/scans/Cassels-Frohlich-Algebraic_Number_Theory.pdf);
its proof is not reproduced in this repository.

The signatures are `B:(r₁,r₂)=(0,1)` and `F:(r₁,r₂)=(0,2)`: `F` contains
the imaginary quadratic field `B`, so it has no real embeddings. The
quotient gamma factor is consequently one
`Γ_C(s)=2(2π)⁻ˢΓ(s)=Γ_R(s)Γ_R(s+1)`, corresponding to `[0,1]`.
The completed factor has the standard normalization

`Λ(s,χ_{F/B}) = Q^(s/2) Γ_R(s)Γ_R(s+1) L_B(s,χ_{F/B})`,

where the rational degree-two conductor is
`Q=|disc(B)|·N_{B/Q}(𝔣(χ_{F/B}))`. For a quadratic extension, the relative
character conductor ideal equals the relative discriminant ideal, and the
conductor-discriminant formula says
`|disc(F)|=|disc(B)|²·N_{B/Q}(𝔣(χ_{F/B}))`.
Thus `Q=|disc(F)|/|disc(B)|`. The PARI receipt gives
`|disc(F)|=8,408,400`, `|disc(B)|=35`, hence `Q=240,240`; it also checks
the plus-field power-order index is 16. These are exact independent
computational checks, while a Lean proof of the plus-field integral basis,
discriminant and conductor has not been recorded here. The standard
Dedekind zeta functional equations each have sign `+1`, so their quotient
has root number `+1` in this normalization.

The standard Hecke theorem also supplies analytic continuation and
polynomial vertical-strip growth (for example through the usual convexity
bounds for finite-order Hecke characters). Those are the facts needed,
together with the `d₂` bound, to justify the contour shift for the
exponential-integral AFE. They are **standard theorem invocations here,
not checked Lean results**. In particular, FE plus entireness alone is
not enough to justify vanishing of horizontal contour integrals; some
growth or a matched theta/Mellin argument is needed.

The existing checked AINTLIB results control each completed Dedekind zeta
separately and give a meromorphic quotient FE; they do not prove
entireness or a strip bound for this quotient. The source-level distinction
and the requested AFE normalization are detailed in
[`../numerical-audit/h6-plus-afe-analytic-gap.md`](../numerical-audit/h6-plus-afe-analytic-gap.md).

## Remaining identification and verification limits

The residue-field argument proves the all-good-prime factors of the
natural relative zeta quotient; the finite PARI calculation checks the
seven omitted factors. Together with the pinned code-defined Euler rule,
this gives an all-prime paper-level identification for **this one numeric
row**, and the all-`n` coefficient bound above. The guarded finite
coefficient comparison independently tests the first 3,922 entries but is
not the reason the identity extends beyond that prefix.

The staged plus-field Lean bridge is uncompiled. The paper argument does
not establish a Lean proof of this identity, Hecke continuation, FE, strip
growth, AFE or numerical upper bound. It also does not identify this
analytic row as one of the exact relative factors in the degree-524288
completed-field decomposition; that separate Artin/Hecke inventory and the
other analytic rows remain open for an internal proof of H.
