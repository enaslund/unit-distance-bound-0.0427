# Independent audit: analytic package for the 32 H6 relative factors

**Later checkpoint:** A separate
[paper local-ramification derivation](h6-all32-conductor-paper-derivation.md)
now derives the 32 relative discriminant norms and rational conductor
classes from local field cases, with exact table comparison. This audit
predates that derivation and did not independently review its proof. Its
statements below about conductor values being only external computational
data describe the earlier evidence state. No Lean conductor theorem or
fresh all-32 discriminant receipt has since passed.

Source-only review of
[`h6-all32-relative-hecke-corollary.md`](h6-all32-relative-hecke-corollary.md),
[`h6-all32-good-prime-derivation.md`](h6-all32-good-prime-derivation.md),
and the historical PARI audit
[`h6-all32-inherited-pari-audit.md`](../numerical-audit/h6-all32-inherited-pari-audit.md).
No Lean or numerical job was run. I find the stated analytic package is
mathematically sound **conditional on the quartic fields, full Euler-factor
identifications, and exact relative discriminants being accepted**. A fresh
guarded all-32 maximal-order replay has now substantially strengthened the
finite field and local-factor evidence; exact relative discriminants and
analytic claims remain open as formal proof obligations.

## Fresh all-32 finite check

The fresh guarded checker
[`h6-all32-quartic-zeta-quotient-status.md`](h6-all32-quartic-zeta-quotient-status.md)
certifies irreducibility and maximal orders for all 32 quartic polynomials
and the base field, then obtains explicit `idealprimedec` residue-degree
data through each row cutoff. It compares 164,712 exact coefficient
positions, including all 224 bad-prime cross-products (seven primes per
row), with zero mismatches. It reports 21,520 quartic and 991 shared-base
prime decompositions, with maximum cutoff 7,843. The JSON receipt
[`h6_all32_quartic_zeta_quotient.json`](h6_all32_quartic_zeta_quotient.json)
has SHA-256
`7002e21b55dc09dd42a306ecc6a5742be5bbf88d0fd1059813cbb06fae044496`
and records PARI/GP 2.17.2, executable/source digests and generated GP
stdout digest. This is a fresh guarded finite check, unlike the inherited
PARI/`lfunan` record described below.

The fresh JSON copies each row's conductor, gamma, and root-number
parameters but does not store any `disc(K_D)`, relative discriminant, or
independently checked conductor. The certified maximal orders and finite
prime profiles are not themselves a recorded discriminant computation.

## What standard quadratic Hecke theory supplies

For each nonzero listed `D`, `Dη` is nonsquare in `B` by its norm: a square
would imply `429` is a square in `Q`. Thus `K_D/B` is a nontrivial quadratic
extension and defines a nontrivial quadratic finite-order Hecke character
`χ_D`. If the displayed `K_D` is the field attached to the row, then

`ζ_{K_D}(s)/ζ_B(s) = L_B(s,χ_D)`

for `Re(s)>1`. Standard Hecke theory gives this nontrivial finite-order
Hecke L-function an entire continuation and a functional equation. The
conductor-discriminant theorem gives
`N_{B/Q}(𝔣(χ_D))=|disc(K_D)|/|disc(B)|²`. The rational degree-two
conductor is `Q_D=|disc(B)|·N_{B/Q}(𝔣(χ_D))=|disc(K_D)|/|disc(B)|`.
For `D=1`, this gives relative conductor-ideal norm `6,864` and rational
conductor `240,240`. Since `B` has signature `(0,1)`
and each quartic `K_D` contains `B` and has signature `(0,2)`, the quotient
gamma factor is one `Γ_C(s)=Γ_R(s)Γ_R(s+1)` factor, i.e. `[0,1]`. Dividing
the two completed Dedekind zeta functional equations gives root number `+1`
in this normalization. Standard finite-order Hecke bounds give polynomial
growth in fixed vertical strips. With the all-prime Euler identity and the
`d₂` bound, these are the usual inputs for a paper-level contour-shift AFE.

These conclusions are standard analytic number theory, not Lean results.
They do not follow from entireness and the FE alone: polynomial vertical
growth (or a matched theta/Mellin decay argument) is still needed to discard
the horizontal contour integrals.

## Conductor data: precise evidence limit

The relative-discriminant formula gives exact row conductors once the
absolute discriminant of each `K_D` is known. The inherited arithmetic
receipt reports 8 rows with conductor 15015, 8 with 240240, and 16 with
960960, and its source asserts matching `lfunparams` tuples for conductor,
root number, and gamma. The audit
[`h6-all32-inherited-pari-audit.md`](../numerical-audit/h6-all32-inherited-pari-audit.md)
establishes that the stored comparison code is consistent with those
claims, but it also records the limitations: this is a historical embedded
receipt; raw GP stdout and executable/version metadata are absent; the
comparison was not rerun; and the inherited receipt does not expose field
discriminants. The new fresh maximal-order checker supplies
`nfcertify` and finite `idealprimedec` profiles for all 32 fields, but it
still does not record discriminants or prove the conductor values. Thus the
32 exact conductors remain external computational premises here. The
conductor-discriminant theorem is not itself a proof that those table values
are correct.

The signature and hence gamma vector `[0,1]` have a direct structural
argument for all 32 fields if `K_D/B` is established as a quadratic
extension: `B` is imaginary quadratic and `K_D` has degree four, so it has
no real embeddings. The root number `+1` likewise follows on paper from
the completed Dedekind zeta quotient once the field/relative-character
identification and compatible completion are established; `lfunparams` is
external corroboration, not the proof.

## Euler factors and coefficient bound

The symbolic good-prime argument proves the local relative factor for all
`p∉{2,3,5,7,11,13,17}` and all 32 twists. The fresh maximal-order run
independently verifies the seven omitted local factors for each twist from
the certified orders and exact prime-decomposition data. Together these
give a paper-level all-prime local-factor identification for the
code-defined rows, conditional on the field presentations; it is external
arithmetic evidence, not a Lean theorem. The inherited `lfunan` receipt
adds a distinct 10,000-prefix check but remains unrerun. Under an accepted
all-prime row match, the relative Hecke Euler product is identified on its
half-plane of absolute convergence. Its finite-order local factors give
prime-power coefficients bounded by `k+1`: over a rational prime there are
at most two primes of `B`; each unramified local factor contributes a
unit-modulus geometric series in `T^f`, while a ramified character factor
is omitted. The coefficient at `T^k` is a sum of at most `k+1` terms.
Multiplicativity then gives `|a_n|≤d₂(n)` for all `n`. This is a paper
deduction conditional on accepting the all-prime row match, not a Lean
theorem for these rows.

## Remaining proof gap

Conditional on the actual fields and their exact relative discriminants,
quadratic Hecke theory supplies the entire completed FE, conductor/gamma/root
data, and strip growth. The fresh replay computationally checks all 32
finite field/order and seven-prime comparisons, but exact relative
discriminants/conductors are still not established here. Matching these
factors to the selected degree-524288 inventory and formalizing the Hecke
continuation, FE, growth and AFE contour shift are also open. Even a
completed proof for all 32 would not by itself prove H: the exact
relative-factor inventory, remaining analytic rows and genus/aggregate
inequalities are separate obligations.
