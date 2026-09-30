# Exact PARI check of the H6 mask-1586 plus field

## Status

The checker [`h6-plus-quartic-local-factors.gp`](h6-plus-quartic-local-factors.gp)
was run once through the shared guard and **passed**. The complete combined
guard/stdout log is
[`h6-plus-quartic-pari-run-20260923.log`](h6-plus-quartic-pari-run-20260923.log),
SHA-256 `bea094c59b94f7b89e1c2dc82c3004b71f47e77ffb7d17934aee0802e9b14765`.
The structured result is
[`h6-plus-quartic-pari-receipt-20260923.json`](h6-plus-quartic-pari-receipt-20260923.json).
The receipt binds the PASS log to the exact GP source bytes used for the run,
SHA-256
`17f9fb721f8e4e042a1da98e66f4138fec46fcd4b770699ef2759a0fd8b07048`.
After that run, only the stale source status comment was refreshed; the current
source SHA-256 is
`39036ede6205251b0e7a18306dce8c17d61738f04eecc9833c74771308a4a258`.
The executable GP statements are unchanged. Receipt SHA-256:
`34b53718133e34b37d28da8789a5633a41fc8ffd5d48c285e5f8423543692256`.
The guard admitted with 16.3 GiB host availability and 1.49 GiB cgroup
headroom, with a 900-second timeout; exit code was 0. PARI/GP version was
2.17.2. The command completed within the timeout; subsecond runtime was not
separately instrumented.

The polynomial is `P(X)=X^4-34X^2+429`. If `α` is a root and
`y=(α^2-17)/2`, then `y^2=-35` and `α^2=17+2y`; this presents
`K=Q(√−35, √(17+2√−35))`. The script checks irreducibility, certifies
PARI's number-field data for `B=Q(√−35)` and `K`, and checks their signatures
and the power-basis discriminant/index identity.

## Discriminant check

The target plus conductor is `Q=240240`. With `|disc(B)|=35`, the expected
absolute field discriminant is `35·240240=8,408,400`. The polynomial
discriminant is `2,152,550,400`, so the expected index of `Z[α]` in `O_K`
is `16`. PARI confirmed these values: `nfcertify` returned `[]` for both
fields, the quartic signature was `[0,2]`, and the integral basis was
`[1, 1/4*x^2 - 15/4, -x, 1/4*x^3 - 19/4*x]`. A useful ring-of-integers
sanity calculation uses
`ω=(1+√−35)/2`: then `η=17+2√−35=15+4ω ≡ 3 (mod 4 O_B)`, whereas
`−η ≡ 1 (mod 4 O_B)`. This predicts relative discriminant norms `16·429`
for the plus field and `429` for the minus field, consistent with the
computed plus discriminant. The latter would give
`|disc|=525525` and index `64`; it is the minus-field prediction and must
not be used for this plus-field polynomial.

## Local quotient calculation

At each listed rational prime, PARI's `idealprimedec` is applied separately
to the certified absolute maximal orders of `B` and `K`. If `f(q/p)` and
`f(P/p)` are their residue degrees, the script forms

`D_B,p(T)=∏_{q|p}(1−T^{f(q/p)})`,
`D_K,p(T)=∏_{P|p}(1−T^{f(P/p)})`, and `Q_p(T)=D_K,p(T)/D_B,p(T)`.

The quotient was checked for zero remainder and compared with the seven
expected H6 twist-`+1` entries at `p=2,3,5,7,11,13,17`:
`1, 1−T, 1+T, 1+T, 1−T, 1+T, (1−T)^2`. All seven computed quotients
matched. The residue-degree lists (base / quartic) were `[2]` / `[2]`,
`[1,1]` / `[1,1,1]`, `[1]` / `[2]`, `[1]` / `[2]`,
`[1,1]` / `[1,1,1]`, `[1,1]` / `[1,2]`, and `[1,1]` / `[1,1,1,1]`.
The pinned H6 table input has SHA-256
`b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`.
The p=17 residue note separately finds roots `±4` for `y²=-35` modulo 17,
and square residues `8=5²` and `9=3²`; that predicts `(1−T)^2` but does
not itself prove the prime-ideal decomposition or quotient factor.

This is an exact finite PARI computation for the maximal orders and seven
local factors. The pass does not prove the all-prime Artin row
identity, identify the global Artin representation, or establish a
functional equation.

## Source provenance and invocation

The script uses PARI/GP `nfinit`, `nfcertify`, `idealprimedec`, and
`divrem`; the corresponding upstream documentation is [General number
fields](https://pari.math.u-bordeaux.fr/dochtml/html/General_number_fields.html),
[relative extensions and number fields](https://pari.math.u-bordeaux.fr/dochtml/html/Relative_extensions_of_number_fields_and__backslashZ_K_minusmodules.html),
and [standard operators including `divrem`](https://pari.math.u-bordeaux.fr/dochtml/html/Standard_monadic_or_dyadic_operators.html).
The revised script computes the two absolute prime decompositions directly,
avoiding dependence on the nested output shape of `rnfidealprimedec`.
