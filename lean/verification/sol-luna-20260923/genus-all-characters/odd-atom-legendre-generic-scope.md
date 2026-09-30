# Generic odd-prime Legendre bridge: scope and status

Status: source-only Lean draft on 2026-09-23. No compile or axiom audit has run. The guarded shared build slot has not been allocated for this file.

[`GenusLunaOddAtomLegendreGeneric20260923.lean`](../../../UnitDistance/GenusLunaOddAtomLegendreGeneric20260923.lean) states the pointwise identity

```text
primeQuadraticCharacter p hp a = (legendreSym p a : ℂ)
```

for any prime `p` and every integer `a`. It uses the definitions
`primeQuadraticCharacter = castIntegerCharacter (quadraticChar (ZMod p))`
and `legendreSym p a = quadraticChar (ZMod p) a`; it should reduce by `rfl` after installing `Fact p.Prime`. The theorem is stronger than the requested odd-prime case and needs no coprimality assumption on `a`; in particular, the nonunit case is included at the prime modulus.

Source SHA-256: `6b303808553e5d629a64a9a675559ddf9d1e521c19f67fddff29756e3c169465`.
Focused axiom audit source: [`GenusLunaOddAtomLegendreGeneric20260923Audit.lean`](../../../UnitDistance/GenusLunaOddAtomLegendreGeneric20260923Audit.lean), SHA-256 `37b9b4eabeb5fb985813dd207a00c94c84a6246ff89b47fc8bdafa76446a3f74`. It requests `#print axioms` for the generic theorem and all six level/corollary results.

**Verification status:** the first guarded command exited 127 before Lean because `lake` was not on `PATH`. The first corrected guarded compile entered Lean and reported missing `Fact p.Prime` instances in the common-level theorem statements. The source was revised to carry explicit local `Fact` instances and use their `.out` proof for the conductor definitions; a source review then removed an unnecessary inner instance declaration. The revised guarded compile was admitted with 16.7 GiB host available and 1.84 GiB cgroup headroom, but Lean terminated with `lean::memory_exception: excessive memory consumption detected at 'interpreter'` and exit 134. No `.olean` was produced. The focused `#print axioms` audit was not run; there is no theorem compile success or axiom output to report. Further work requires a separately allocated attempt under the same resource policy, potentially reducing imported closure or elaboration workload; memory limits were not changed.

The same file adds unit-input common-level consequences for the five odd local factors in [`GenusLunaPrimitiveAtomExpansionLight20260923.lean`](../../../UnitDistance/GenusLunaPrimitiveAtomExpansionLight20260923.lean): prime moduli `3, 5, 7, 11, 13`, corresponding respectively to mask coordinates `2, 3, 4, 5, 6`. These use `DirichletCharacter.changeLevel_eq_cast_of_dvd'` and assume `IsCoprime a commonGenusModulus` because evaluating a character after lifting its level is identified with the old-level value on units.

Application boundary: in the atom expansion, the odd factors are `primitiveThreeAtomAtActual`, `primitiveFiveAtomAtActual`, `primitiveSevenAtomAtActual`, `primitiveElevenAtomAtActual`, and `primitiveThirteenAtomAtActual`. Each is the primitive character of the relevant common-level character raised to its mask bit, then lifted to the full actual conductor. To rewrite an active (`bit = 1`) odd atom as its Legendre symbol on a unit of the full conductor, the next proof should combine this pointwise prime formula with Mathlib's `primitiveCharacter_changeLevel_apply`, `primitiveCharacter_apply_of_primitive`, and the conductor identities already in `GenusDirichletConductorsRun20260920`. An inactive bit should contribute the trivial character on units. The atom expansion itself is valid on every integer and handles nonunits through zero-valued Dirichlet-character factors; one must not claim an individual lifted atom equals its prime Legendre symbol on arbitrary nonunits of the *full* modulus. The generic theorem's all-integer statement is at the base prime level.

This draft removes only the notation/definition bridge from an abstract prime quadratic character to Mathlib's Legendre symbol. It does not prove that the numerical Kronecker/Conrey rows agree with every genus character, does not complete the all-mask atom expansion audit, and does not discharge the generic all-integer character identity or any zeta/AFE assumption. Exact Lean compile status remains pending.
