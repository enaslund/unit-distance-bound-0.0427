# Mathlib-only base for the odd-prime Legendre bridge

Status: compiled and axiom-audited on 2026-09-23 under the selected Lean 4.32/Mathlib pins. This is a small definition bridge, not yet the direct project-character or five-atom theorem.

[`GenusLunaOddAtomLegendreMathlib20260923.lean`](../../../UnitDistance/GenusLunaOddAtomLegendreMathlib20260923.lean) imports `Mathlib.NumberTheory.LegendreSymbol.Basic`, which defines `legendreSym`, plus the direct Mathlib basics for `DirichletCharacter` and `ℂ`. The local `castQuadraticCharacter` is the complex cast of `quadraticChar (ZMod p)` and its pointwise formula is intended to close by `rfl`, for every integer input `a`, including multiples of `p`.

Source SHA-256: `c05ebded917bb109116e6723cc1b55ad7fd163040db6f6498bf7e25331122796`.
Focused axiom audit: [`GenusLunaOddAtomLegendreMathlib20260923Audit.lean`](../../../UnitDistance/GenusLunaOddAtomLegendreMathlib20260923Audit.lean), SHA-256 `8f4d8183ff6598b44e56d225b7e313f6d90bcebdc9ddcd136c0eb100d3180ddd`; it contains `set_option autoImplicit false` and prints the theorem's axioms.

## Guarded verification record

The first light-source compile was admitted at 16.7 GiB host / 1.24 GiB cgroup headroom and exited 1 because the Legendre module did not import `DirichletCharacter` or `ℂ`. After adding direct Mathlib imports `Mathlib.NumberTheory.DirichletCharacter.Basic` and `Mathlib.Data.Complex.Basic`, the revised proof source compiled with exit 0 using `lake env lean -j1 -M2560` through the master guard; admission was 15.3 GiB host / 1.80 GiB cgroup headroom. Its `.olean` SHA-256 is `8d10fd340ca230ffb8fa087ae9f3632400faf07bbe468b28dd848c4d555c4828` (30,440 bytes).

The focused audit ran as a separate guarded job and exited 0 at 15.1 GiB host / 1.69 GiB cgroup headroom. `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`, the permitted standard axioms. This check covers the light lemma only; the heavy `GenusDirichletConductorsRun20260920` bridge and five common-level atom corollaries remain uncompiled here. The earlier heavy attempt remains separately recorded as exit 134 from excessive interpreter memory, with no `.olean` and no audit output.

## Connection to the project character

In [`GenusDirichletConductorsRun20260920.lean`](../../../UnitDistance/GenusDirichletConductorsRun20260920.lean), `primeQuadraticCharacter q hq` is defined by installing `Fact q.Prime` and applying the local `castIntegerCharacter` to `quadraticChar (ZMod q)`. That module's `castIntegerCharacter` is exactly `c.ringHomComp (Int.castRingHom ℂ)`. Mathlib's `legendreSym q a` is defined in `LegendreSymbol.Basic` as `quadraticChar (ZMod q) a`. Therefore, after unfolding the project definitions and introducing the same `Fact` instance, the new light theorem should specialize to the desired identity for `primeQuadraticCharacter q hq` by definitional equality, with no separate nonunit argument.

The earlier heavy file [`GenusLunaOddAtomLegendreGeneric20260923.lean`](../../../UnitDistance/GenusLunaOddAtomLegendreGeneric20260923.lean) attempts to include that direct project bridge plus five common-level corollaries. Its guarded compile was admitted but terminated with Lean's `excessive memory consumption detected at 'interpreter'` at exit 134; no `.olean` was written and the audit was not run. This is retained as a failed resource-bounded attempt, not proof evidence. The present file avoids the heavy `GenusDirichletConductorsRun20260920` import.

This light lemma establishes only a definition bridge. Applying it to the five odd atoms in [`GenusLunaPrimitiveAtomExpansionLight20260923.lean`](../../../UnitDistance/GenusLunaPrimitiveAtomExpansionLight20260923.lean) still requires the project-side level/conductor facts and careful handling of higher-level nonunits. In particular, it does not identify the full external Kronecker/Conrey genus table or prove the all-mask identity.
