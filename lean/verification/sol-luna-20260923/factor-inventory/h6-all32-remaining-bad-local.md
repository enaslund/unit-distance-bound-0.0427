# H6 mask-1586: remaining bad local factors (source-level analysis)

This note covers the row-dependent local quotient denominators at
`p = 2, 3, 5, 11, 13` for the 32 twists in sector 1586. The already treated
`p=7,17` cases are in the all-prime plus-row note and the all-32 PARI receipt.
The result separates the local field explanation from the exact finite
comparison: the first gives the possible shape of each factor; the pinned
32-row PARI run checks its row-specific value. No Lean theorem for these local
identities is claimed.

## Quotient convention and pinned comparison

Let `B=Q(√−35)`, `η=17+2√−35`, and
`K_D=B(√(Dη))`, equivalently the field presented by
`P_D(X)=X⁴−34D X²+429D²`. For a number field `L`, put
`D_{L,p}(T)=∏_{𝔭|p}(1−T^{f(𝔭/p)})`. The relative zeta quotient has local
denominator

`E_{D,p}(T)=D_{K_D,p}(T)/D_{B,p}(T)`.

The authoritative row values are the `bad_euler_denominators` in the pinned
[`h6-low-degree-arithmetic.json`](../../../../publication/nonabelian-dyadic-lower-bound/research/h6-low-degree-arithmetic.json),
SHA-256 `b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`.
The all-32 checker certified the quartic maximal orders, obtained the rational
prime `e,f` decompositions for the quartic and base fields, formed
`D_K/D_B`, and checked the exact polynomial cross-products at all seven
listed bad primes in every row. Its immutable result JSON has SHA-256
`7002e21b55dc09dd42a306ecc6a5742be5bbf88d0fd1059813cbb06fae044496`; the
status note records 224/224 bad-prime passes and zero mismatches. That is an
exact finite PARI/GP check, not a symbolic proof for arbitrary twists.

The remaining five prime patterns read from the pinned 32-row table are:

| `p` | pinned `E_{D,p}` shapes and count | local reason for this shape |
|---:|---|---|
| 2 | `1` for 24 twists; `1+T²` for 8 | `B` is inert and unramified, so `D_{B,2}=1−T²`. If `2|D`, the radicand `Dη` has odd valuation in `B⊗Q₂`, making the relative quadratic extension ramified and the quotient denominator `1`. For odd `D`, it is a unit. The observed factor `1+T²` is the unramified inert case `(1−T⁴)/(1−T²)`; factor `1` is consistent with split or ramified local extension, both of which leave the quotient denominator `1`. |
| 3 | `1−T` for 16; `1+T` for 16 | `3` splits in `B` and divides `N(η)` to exponent one. One of the two base primes sees odd valuation of `η` (or, if `3|D`, the other prime does); the other prime is the single unramified relative quadratic place. Its split/inert sign gives `1−T` / `1+T`. |
| 5 | `1−T` for 16; `1+T` for 16 | `5` ramifies in `B`, while `η` is a unit at the prime above 5. `v_{mathfrak p}(D)` is either 0 or 2, so the quadratic extension is determined by the residual unit after removing an even valuation. Relative split/inert gives `1−T` / `1+T`. |
| 11 | `1−T` for 16; `1+T` for 16 | As at 3: `11` splits in `B`, divides `N(η)` once, and exactly one of the two local relative extensions is unramified; its split/inert sign determines the linear factor. |
| 13 | `1−T` for 16; `1+T` for 16 | As at 3 and 11: `13` splits in `B`, divides `N(η)` once, and exactly one local relative extension is unramified; its split/inert sign determines the linear factor. |

For the odd primes `3,5,11,13`, the relevant local radicands are units after
removing their even valuations, so their quadratic local alternatives are
split and unramified inert. For a split base
prime of residue degree one, the relative split factor is `(1−T)` and the
relative inert factor is `(1−T²)/(1−T)=1+T`. At `p=5`, the base prime has
rational residue degree one and the same relative quotient calculation
applies. At `p=2`, residue characteristic two also permits ramified unit
extensions; these, like split extensions, give quotient denominator `1`,
so the pinned denominator alone does not classify that local case. The
inert unramified relative case gives `1+T²`.

The residue calculations supporting the case distinctions are elementary:
`(−35/2)=-1`, while `−35` is a square modulo `3,11,13`; `5` divides the
base discriminant. Also `N_{B/Q}(η)=429=3·11·13`, with each of those three
prime divisors occurring to exponent one, and `5∤429`. Each twist is
squarefree, so at a split prime dividing `D`, its valuation is one at each
of the two primes of `B`; at the ramified prime over 5, the valuation of
the rational prime is two.

The symbolic addendum
[`h6-all32-p2-p5-symbolic.md`](h6-all32-p2-p5-symbolic.md) derives and checks
the exact signs at `2` and `5`. In particular, at `2` the factor is `1+T²`
precisely for `D∈{−65,−13,−5,−1,3,11,15,55}`, equivalently for odd twists
`D≡3 (mod 4)`; the other twists give `1`. At `5`, a residue-unit Legendre
symbol gives each row's linear sign. The
[split-prime derivation](h6-all32-p3-p11-p13-symbolic.md) now gives an exact
residual-unit formula for each twist at `3,11,13` and compares all 96
entries with the pinned table. The status JSON preserves each row's `D_K`, `D_B`, quotient
polynomial, and `pass` result.

## Why the finite result is useful, and what is still missing

The local field analysis reduces these five bad-prime factors to simple
ramification and split/inert cases. The maximal-order replay checks the
actual exact polynomial for each of the 32 twists, including primes where
the defining power order may not be maximal. This addresses the concern that
the good-prime character formula cannot simply be extended across primes
dividing `D`, `35`, or `429`.

The finite computation alone does **not** prove an all-prime row/relative-zeta
identity. The separate source-level
good-prime argument covers `p∉{2,3,5,7,11,13,17}`. Combining that argument
with these finitely many exact PARI comparisons is compelling paper-level
evidence for the 32 relative quotient identifications, conditional on the
field presentations; no corresponding all-row Lean bridge is present. The
row `D=1` PARI receipt and the all-32 receipt are finite computation. They
do not establish the conductor/gamma/root-number data, completed functional
equations, analytic growth, AFE tails, or the target scalar inequality.

The all-32 checker source used by the successful run is preserved as
[`h6_all32_quartic_zeta_quotient_attempt2.source`](h6_all32_quartic_zeta_quotient_attempt2.source),
SHA-256 `cf9970fe1386f89c147c7212f2f51e8e6607f47547195535e4b2f1a787738dc7`.
The current working checker has the same digest. The executed attempt-2
source includes the explicit `polisirreducible` checks; this note's pin
refers to that successful source recorded in the status receipt.
