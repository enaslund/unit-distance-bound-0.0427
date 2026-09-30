# H6 mask 1586: conditional all-32 relative-Hecke corollary

This note combines the good-prime calculation in
[`h6-all32-good-prime-derivation.md`](h6-all32-good-prime-derivation.md)
with the audited inherited PARI receipt and the later fresh
[all-32 maximal-order replay](h6-all32-quartic-zeta-quotient-status.md).
The conclusion is a paper-level
corollary **conditional on accepting each row's field and local-factor
identification**. It is not a Lean proof or a proof of the global bound H.

## Conditional all-prime identification

For every listed twist `D`, put
`B=Q(√−35)`, `η=17+2√−35`, and `K_D=B(√(Dη))`. The generic argument
proves the exact rational local denominator of `ζ_{K_D}/ζ_B` for every
`p∉{2,3,5,7,11,13,17}` and matches the pinned recurrence in
`next-dyadic-h5-single.py`. It covers all 32 twists; in particular every
prime dividing `D` is among the seven excluded primes.

The stored `h6-low-degree-arithmetic.json` receipt records an inherited
PARI `lfundiv(lfuncreate(K_D),lfuncreate(B))` check for each of the 32
twists. Its checked source compares `lfunparams` with the stored conductor,
root number `+1`, and gamma vector `[0,1]`; compares all seven local
denominators at `2,3,5,7,11,13,17`; and compares the first 10,000
Dirichlet coefficients with the Python recurrence. The audit of the
historical receipt is
[`h6-all32-inherited-pari-audit.md`](../numerical-audit/h6-all32-inherited-pari-audit.md).
The fresh guarded replay separately compared all 224 seven-prime denominator
cross-products using certified maximal orders for all 32 quartics. Accepting
those finite comparisons along with the good-prime proof gives
an all-prime local-factor identity for each **code-defined row** and hence
the corresponding relative Euler product `ζ_{K_D}/ζ_B` on its initial
half-plane of absolute convergence.

The provenance limit matters: this inherited JSON has source and generated
GP-script/stdout hashes, but the raw GP output is not included; it records
no PARI executable/version or guarded invocation, and the audit did not
rerun the computation. It also lacks explicit `nfcertify` and
`idealprimedec` data. A separate fresh attempt-4 maximal-order replay
independently checks twist `D=1` through `n=3922`. The newer direct all-32
replay matches 164,712 finite coefficients and every bad factor; its checker
and receipt are checkout-side after candidate 17 was sealed. The inherited
10,000-prefix record remains historical evidence, while the new replay has
stronger run provenance and a shorter row-specific prefix. Neither finite
check proves the global field identification in Lean.

## What follows from accepting those identifications

For each `D`, `Dη` is nonsquare in `B`: otherwise its norm divided by
`D²` would make 429 a rational square. So `K_D/B` is a nontrivial
quadratic extension. Its associated quadratic finite-order Hecke character
`χ_D` is nontrivial, and the standard Hecke analytic-continuation theorem
gives an entire `L_B(s,χ_D)`. The relative zeta identity identifies this
factor with `ζ_{K_D}(s)/ζ_B(s)` for `Re(s)>1`.

The completed relative Hecke functional equation, conductor and gamma data
then follow from standard Hecke theory, conditional on the accepted
field/row match. Equivalently, the quotient of the two completed Dedekind
zeta functions has the functional equation. Since `B` has signature
`(0,1)` and `K_D`, which contains `B`, has signature `(0,2)`, the quotient
gamma factor is one complex factor
`Γ_C(s)=Γ_R(s)Γ_R(s+1)`, i.e. `[0,1]`. Its sign is `+1`, as both completed
Dedekind zeta functions have sign `+1`. The rational degree-two conductor is
`Q_D=|disc(B)|·N_{B/Q}(𝔣(χ_D))=|disc(K_D)|/|disc(B)|`, where the relative
character conductor ideal equals the relative discriminant ideal. The
norm of that ideal alone is `|disc(K_D)|/|disc(B)|²`. The inherited
`lfunparams` comparisons report the
row-specific values (8 rows with 15015, 8 with 240240, and 16 with
960960). Those values remain external computational data here; individual
relative discriminants have not been proved in Lean or independently
recorded for all 32 by the fresh finite replay. A later
[paper local-ramification derivation](h6-all32-conductor-paper-derivation.md)
does derive their norms and the three rational conductor classes from
the all-32 twist conditions; it has no Lean counterpart. The
[analytic independent audit](h6-all32-analytic-independent-audit.md)
states the conductor-data limit.

Standard finite-order Hecke bounds also give polynomial growth in each
fixed vertical strip. Together with the exact conductor/gamma normalization
and an all-`n` coefficient bound, this supplies the analytic growth premise
for the exponential-integral contour shift. It is a standard theorem
invocation in this corollary, not an existing Lean result. Entireness and
the FE alone would not justify the contour shift.

The all-`n` bound follows on paper under the same all-prime row identity.
For `p∉BAD`, the local factors from the generic derivation have reciprocal
coefficients bounded by `k+1` at `T^k`: they are either
`(1−εT)⁻²` or `1/(1+cT²)` with `ε,c∈{±1}`. At `p∈BAD`, accepting the
receipt identifies the row factor with the local factor of a quadratic
finite-order Hecke character. There are at most two primes of `B` over a
rational prime; each local factor is either omitted when ramified or has
the form `(1−λT^f)⁻¹`, with `|λ|=1` and `f` the residue degree. The
coefficient of degree `k` in their product is a sum of at most `k+1`
unit-modulus terms (solutions of `f₁i+f₂j=k`), so has magnitude at most
`k+1`. Thus `|a(p^k)|≤k+1` at every prime, and multiplicativity gives
`|a_n|≤d₂(n)` for all `n`. The checked Mathlib multiplicative bridge proves
the final abstract implication from local prime-power bounds, but does not
prove these local identities for the 32 rows.

## Scope still open

The all-32 expint replay is a finite external numerical check under the
row-specific FE, conductor, Euler-factor and `d₂` premises. Neither that
replay nor the historical or fresh PARI receipts formalize the 32 field/row
identifications, the relative discriminants, Hecke continuation/FE/growth,
or the AFE contour proof in Lean. Nor does it place these 32 factors in the
exact relative-factor inventory of the degree-16384 completed field
inside the degree-524288 retained field,
prove the remaining analytic rows and genus estimates, or discharge the
selected H inequality. Hence the paper-level conditional package does not
prove H or a Lean AFE.
