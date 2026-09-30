# H6 mask 1586: good-prime factors for all 32 quadratic twists

This source-only calculation treats the proposed fields
`B=Q(√−35)` and
`K_D=B(√(Dη))`, where `η=17+2√−35` and `D` ranges over the 32 row
twists. It proves the generic local formula away from the common exceptional
set. It does **not** verify the bad-prime table, the conductor/functional
equation data, or the AFE. No Lean or numerical job was run.

The exact twist list in the mask-1586 sector of
[`h6-low-degree-arithmetic.json`](../../../../publication/nonabelian-dyadic-lower-bound/research/h6-low-degree-arithmetic.json)
is

`±1, ±2, ±3, ±5, ±6, ±10, ±11, ±13, ±15, ±22, ±26, ±30, ±55, ±65, ±110, ±130`.

Every prime divisor of every `D` belongs to `{2,3,5,11,13}`. In particular,
the whole set of primes dividing `D` lies in the script's
`BAD={2,3,5,7,11,13,17}`. The pinned source hash for
[`next-dyadic-h5-single.py`](../../../../publication/six-dimensional-lower-bound/research/next-dyadic-h5-single.py)
is `f9a97f5c41485914e9700a5efcebb9df0ffdbc834a56a666b994d397ab3a3ba6`,
matching the mask-1586 arithmetic inventory's source pin.

## Field and unramified-prime conditions

For any nonzero listed `D`,

`P_D(X)=X⁴−34D X²+429D²`

is the polynomial of `α_D=√(Dη)`. Indeed, its constant and middle
coefficients are the norm and trace of `Dη` from `B`:
`N_{B/Q}(Dη)=429D²` and `Tr_{B/Q}(Dη)=34D`. Also
`√−35=(α_D²−17D)/(2D)`, so `Q(α_D)` contains `B`. The element `Dη` is
not a square in `B`: if `Dη=u²`, taking norms and dividing by `D²` would
make `429` a square in `Q`. Thus `K_D/B` is quadratic and `P_D` is
irreducible of degree four.

The quartic discriminant formula gives

`disc(P_D)=16·429·560²·D⁶`.

Its prime support is contained in `{2,3,5,7,11,13}` together with the prime
divisors of `D`. Since `disc(B)=−35`, every prime
`p∉BAD` is unramified in both `B` and `K_D` and does not divide `D`, 35,
or 429. Thus the residue symbols below are all nonzero. The prime 17 is in
`BAD` by the row convention even though it divides neither displayed
discriminant nor any listed `D`.

## Local denominator for `p∉BAD`

Write
`a=(−35/p)`, `b=(429/p)`, and `δ=(D/p)`. For a field `L`, put
`D_{L,p}(T)=∏_{𝔭|p}(1−T^{f(𝔭/p)})`. The local factor of
`ζ_{K_D}/ζ_B` is `1/E_{D,p}(T)`, with
`E_{D,p}=D_{K_D,p}/D_{B,p}`.

If `a=1`, choose `r∈F_p` with `r²=−35`. The two primes of `B` over `p`
have residue values `D(17+2r)` and `D(17−2r)` for `Dη`. Define
`ε₊=(D(17+2r)/p)` and `ε₋=(D(17−2r)/p)`. Both are `±1`, and
`ε₊ε₋=(D²·429/p)=b`. At either split base prime, the relative extension
splits for sign `+1` and contributes quotient denominator `1−T`; it is
inert for sign `−1` and contributes `1+T`. Therefore

`E_{D,p}(T)=(1−ε₊T)(1−ε₋T)`.

If `b=1`, the two signs agree; with
`ε_D=(D(17+2r)/p)` this is
`1−2ε_D T+T²`. If `b=−1`, the signs are opposite and the result is
`1−T²`.

If `a=−1`, there is one prime of `B` over `p`, with residue field
`F_{p²}`. For the residue `u` of `Dη`, its norm to `F_p` is
`u^{p+1}=D²·429`, since Frobenius is the nontrivial conjugation of `B`.
Its quadratic residue symbol in `F_{p²}` is therefore
`(D²·429/p)=b`. A relative split contributes quotient denominator
`1−T²`; a relative inert prime contributes
`(1−T⁴)/(1−T²)=1+T²`. Hence
`E_{D,p}(T)=1−bT²`.

Combining the cases,

`E_{D,p}(T) = 1−2δ ε T+T²` if `a=b=1`,

where `ε=(17+2r/p)`, and

`E_{D,p}(T) = 1+abT²` otherwise.

In the first case `ε_D=δ ε`; in all other cases the linear coefficient is
zero and the quadratic coefficient is unchanged by `D`.

## Comparison with the pinned source

In `next-dyadic-h5-single.py:131–142`, `prime_data` uses the `D=1`
symbols and emits baseline `(trace,det)=(2ε,1)` when `a=b=1`, or
`(0,ab)` otherwise. In `:145–156`, `coefficients` multiplies only the
trace by `(D/p)` for this sector (its cyclic twist base is zero), leaving
the determinant unchanged. The resulting polynomial
`1−trace·δ T+det·T²` is exactly the formula above, for each of the 32
twists and every `p∉BAD`.

## Scope and caveats

The derivation excludes every prime dividing `D`; these are among
`2,3,5,11,13`. It also excludes 7, which divides the common discriminant
support, and 17, which the source deletes by convention. Nothing in this
symbolic good-prime argument establishes the actual relative Euler factor
at those seven primes. Their row-specific `bad_euler_denominators` were
subsequently compared for all 32 twists in a fresh guarded
[maximal-order replay](h6-all32-quartic-zeta-quotient-status.md): all 224
exact denominator cross-products passed. That external finite check is not
a Lean proof of the seven local identities.

The twist parameters are squarefree radicands, not uniformly fundamental
discriminants (the quadratic character's conductor at 2 in particular
needs separate treatment). The formula proves only unramified good-prime
Euler agreement. It does not determine the relative discriminant/conductor
for each `D`, the gamma/root-number data, the completed FE or its vertical
growth, or identify the rows with all factors in the completed-field
decomposition. Therefore it is not by itself a justification of the 32
row AFE or its contribution to `H`.
