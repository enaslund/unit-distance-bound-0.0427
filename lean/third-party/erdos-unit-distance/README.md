# Selected profinite/Galois quotient construction

Two source modules adapt selected proofs from
[logical-intelligence/erdos-unit-distance](https://github.com/logical-intelligence/erdos-unit-distance)
at commit `b6493074dd103ca32ea4f5e9b0bc9cb3a0379f2e`, original
`ErdosUnitDistance/Internal/ClassFieldTheory/Witness.lean`:

- `UnitDistance/ProfiniteQuotientTower.lean` adapts `openNormalChain`, separating
  increasingly many actual distinct elements of an infinite profinite group.
- `UnitDistance/GaloisQuotientTower.lean` adapts the fixed-field construction
  in `cft_D2_infiniteQuotientTower`, for an independently given actual Galois
  extension and continuous surjective infinite profinite quotient. It also
  packages adjoining a retained finite Galois field.

The upstream root LICENSE and NOTICE are preserved here. The original file
has no additional copyright header. Exact source and local hashes are in
`manifest.json`. Local changes port imports/namespaces, expose generic
quotient hypotheses, and package actual finite Galois fields and their degree
limits. No upstream Shafarevich hypothesis, unramified tower realization,
main theorem, or PrimeNumberTheoremAnd proof is imported by these modules.
The actual arithmetic quotient and its ramification/splitting properties
remain separate proof obligations.
