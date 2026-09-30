# H6 plus-twist local factor at 17: residue calculation

## Finite residue calculation

For `B = ℚ(√−35)`, the chosen generator `r` satisfies `r² = −35`. Modulo
17, `−35 ≡ 16`, so the quadratic polynomial has two distinct roots
`r ≡ 4, −4`: both square to 16, and their difference 8 is nonzero mod 17.
The plus radicand is `η = 17 + 2r`; its two residues are therefore

| Residue of `r` | Residue of `η` | Square witness in `𝔽₁₇` |
|---:|---:|---:|
| 4 | 8 | `5² = 25 ≡ 8` |
| −4 | 9 | `3² = 9` |

Also `N_{B/ℚ}(η)=429 ≡ 4 (mod 17)`, so these residues are nonzero. The
quadratic field source proves `disc(B) = −35`, and 17 does not divide it, so
the rational prime 17 splits into two
degree-one primes of `B`. At either base prime, the residue of η is a nonzero
square in characteristic 17; Hensel lifting then makes η a square in the
corresponding completion, so the quadratic extension `B(√η)/B` splits at both
primes. Each prime of `B` contributes relative Euler denominator `1−T`, and
the product over the two base primes is `(1−T)^2`.

This predicts the H6 mask-1586 twist-`+1` table entry at 17 and explains why
it must be retained even though `17 ∤ 240240`. It is not a Lean proof of the
prime-ideal decomposition, local square lifting, or equality with the row's
Euler factor: it only computes the residue data and states the local-field
deduction that those missing number-field lemmas must formalize. No Lean build
was run for this calculation.

The target row data are from pinned `h6-low-degree-arithmetic.json`
SHA-256 `b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`;
its mask 1586, twist `+1` row lists `17 : (1−T)^2`.
