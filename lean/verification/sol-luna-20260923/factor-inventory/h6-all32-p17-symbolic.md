# H6 mask 1586: symbolic `p=17` factor for all 32 twists

For each pinned twist `D` in the mask-1586 sector, the relative quartic
field is
`K_D=B(√(Dη))`, with `B=Q(√−35)` and `η=17+2√−35`. The pinned twists
are all coprime to 17. Modulo 17, `−35≡16`, so `B` splits with roots
`r=±4`. The two residues of `η` are

`17+2·4 ≡ 8` and `17−2·4 ≡ 9 (mod 17)`.

Both are squares: `8/17=+1` (since `(2/17)=+1`) and `9=3²`. Thus
`(429/17)=(8·9/17)=+1`, and both split base primes have relative
quadratic residue sign `+1` before twisting. Because `17∤D`, twisting
multiplies each sign by the same
`δ=(D/17)∈{±1}`. For a split base prime, sign `+1` contributes
quotient denominator `1−T`, and sign `−1` contributes `1+T`. Therefore

`E_{D,17}(T)=(1−δT)²`.

This is genuinely an unramified local calculation: `17` divides neither
`disc(B)=−35`, nor
`disc(X⁴−34D X²+429D²)=16·429·560²·D⁶`, nor any pinned `D`. Its
membership in the source's `BAD` list is a row-table convention, not
ramification at 17.

## Exact pinned-table comparison

I read the mask-1586 rows from
[`h6-low-degree-arithmetic.json`](../../../../publication/nonabelian-dyadic-lower-bound/research/h6-low-degree-arithmetic.json)
without modifying or regenerating it. Its SHA-256 is the pinned
`b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`.
All 32 p=17 denominator arrays agree coefficient-for-coefficient with the
formula: for the 16 twists with `(D/17)=+1`, the array is
`[1,−2,1,0,0]`; for the 16 with `(D/17)=−1`, it is
`[1,2,1,0,0]`. This also explains why each pair `D,−D` has the same
entry, as `(−1/17)=+1`.

The comparison is an exact symbolic derivation plus a read-only check of
the hash-pinned row table. It is not a Lean theorem and does not re-run or
reproduce PARI. The other six source-excluded primes
`2,3,5,7,11,13` still require their row-specific local-factor checks;
the inherited PARI receipt claims those checks for all 32 twists but is
historical external evidence. This p=17 result establishes no conductor,
global Hecke identity, functional equation, AFE, or contribution to H.
