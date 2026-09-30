# Independent review: PARI plus-quartic computation

## Scope and provenance

I reviewed `h6-plus-quartic-local-factors.gp`, its saved stdout log, the H6
mask-1586 twist-`+1` row, the structured receipt, and the status note. I did
not run PARI. The receipt records the command, guard admission, exit code 0,
PARI/GP 2.17.2, timeout, and exact output/source pins. Current SHA-256 values
are:

- Executed GP source (exact PASS input): `17f9fb721f8e4e042a1da98e66f4138fec46fcd4b770699ef2759a0fd8b07048`
- Current GP source: `39036ede6205251b0e7a18306dce8c17d61738f04eecc9833c74771308a4a258`
- stdout log: `bea094c59b94f7b89e1c2dc82c3004b71f47e77ffb7d17934aee0802e9b14765`
- receipt: `34b53718133e34b37d28da8789a5633a41fc8ffd5d48c285e5f8423543692256`
- arithmetic row JSON: `b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`

The receipt binds the PASS log to the exact source bytes used for the run and
records the PARI version, exit status, and guard admission. After the run, the
source header's stale “unrun” comment was replaced with a receipt reference;
the executable GP statements were not changed. Thus the current source SHA
differs from the exact run-source SHA by that comment-only update, and the
receipt records both. The row JSON SHA matches the cited input. The provenance
gap is closed without representing the post-run comment refresh as a rerun.

## Mathematical checks

The polynomial identification is correct. If `α` is a root of
`P(X)=X^4−34X^2+429` and `y=(α²−17)/2`, then the polynomial equation gives
`y²=−35` and `α²=17+2y`. Conversely, adjoining `α=√(17+2y)` to
`B=ℚ(y)` gives a root of `P`. The script checks irreducibility, so this
quartic presentation has the expected absolute degree four.

The log reports `disc(B)=−35`, quartic field discriminant `8,408,400`, and
power-order index `16`; the polynomial discriminant is `2,152,550,400`, and
`16² × 8,408,400 = 2,152,550,400`. The source checks both `nfcertify` calls
return empty and checks the discriminant/index identity. PARI's documented
meaning of empty `nfcertify(nf)` output is that `nf.zk` and `nf.disc` are
unconditionally correct. Thus the transcript, if bound to this source,
certifies the maximal order and discriminant, not just a `nfinit` guess.
The quartic signature `[0,2]` is consistent with a totally imaginary
quartic.

For each listed rational prime, the quotient direction is correct. The
absolute zeta Euler denominators are
`D_F,p(T)=∏_{𝔭|p}(1−T^{f(𝔭/p)})`; hence the denominator polynomial for
`ζ_K/ζ_B` is `D_K,p/D_B,p`, exactly the script's `topDen/baseDen`. The log's
residue-degree lists produce:

| `p` | `B` degrees | `K` degrees | `D_K/D_B` | H6 twist `+1` |
|---:|---|---|---|---|
| 2 | `[2]` | `[2]` | `1` | `1` |
| 3 | `[1,1]` | `[1,1,1]` | `1−T` | `1−T` |
| 5 | `[1]` | `[2]` | `1+T` | `1+T` |
| 7 | `[1]` | `[2]` | `1+T` | `1+T` |
| 11 | `[1,1]` | `[1,1,1]` | `1−T` | `1−T` |
| 13 | `[1,1]` | `[1,2]` | `1+T` | `1+T` |
| 17 | `[1,1]` | `[1,1,1,1]` | `(1−T)^2` | `(1−T)^2` |

These agree with the seven factors in the cited JSON. They are exact local
factor computations in the two certified absolute fields.

## Scope limit

This is finite evidence at `2,3,5,7,11,13,17`. It does not prove the local
factor identity for every rational prime, identify the global induced Artin
representation with the numerical twist-`+1` factor, establish its functional
equation/root number, or prove the all-`n` coefficient majorant. In
particular, matching the conductor-like discriminant quotient and seven
selected factors does not establish the all-prime row identity. I found no
polynomial, discriminant/index, quotient-direction, or listed-factor
mismatch. The recorded PARI result is finite exact evidence for the seven
listed primes, with provenance pinned as described above.

No new numerical work was performed; worker resource counters are unavailable,
not zero.
