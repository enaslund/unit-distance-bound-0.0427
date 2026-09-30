# Lightweight actual primitive atom expansion

## Target

The new source `UnitDistance/GenusLunaPrimitiveAtomExpansionLight20260923.lean`
defines local primitive atoms from the selected common-level factors. The
2-primary atom is the primitive character of `commonTwoCharacter m`; the five
odd atoms are the primitive characters of `commonChi3 ^ bit`, `commonChi5 ^
bit`, ..., `commonChi13 ^ bit`. Each is lifted to the actual conductor of the
full genus character. The checked theorem is
`genusPrimitiveCharacter_apply_eq_local_primitive_atoms`, with the product
formula at every integer.

## Proof route and distinction from the datum endpoint

This route imports `GenusDirichletPrimitiveRun20260920` and
`GenusDirichletConductorsActualRun20260920`; it avoids
`GenusDirichletRootNumbersActualRun20260920b` and the analytic
`GenusDirichletPrimitiveActualRun20260920` leaf. The pure conductor module
supplies `genusDirichletCharacter_eq_normalizedCommonGenusCharacter`,
the factor conductors, and
`expectedGenusPrimitiveConductor_eq_two_mul_odd`. For each odd factor the new
source proves the selected power has conductor `p ^ bit` by splitting the
mask bit into 0/1. Those conductor factors divide the actual conductor.

The proof compares the product of lifted local primitive atoms with the
actual primitive character after lifting both to the common genus modulus.
`changeLevel_primitiveCharacter` recovers each selected common-level factor;
the common-level normalization theorem identifies their product with the
actual genus character. `changeLevel_injective` then gives equality at the
actual primitive conductor, after which evaluation yields the formula for all
integers. This argument makes the all-integer scope visible through equality
of Dirichlet characters; it does not depend on unit-only evaluation.

The atom expressions here are local primitive characters lifted to the full
primitive conductor. They provide the same character-value decomposition
needed by the numerical atom check, but they do not name the literal
`twoDatum` and `optionalDatum` records, which remain declared in the avoided
root-number module.

## Verification status

**Checked theorem and axiom audit.** The all-integer atom expansion compiled
and its focused audit reports only the standard Lean foundations
`propext`, `Classical.choice`, and `Quot.sound`. The matching audit source is
`UnitDistance/GenusLunaPrimitiveAtomExpansionLight20260923Audit.lean`; exact
guard outcomes and artifacts are recorded below.

Pre-build draft hashes (source used by the first full compile):

- Module: `317729bc143c48ca274d83d90ae739fc8b40713c48653e351f9fe5d7c84c0ff1`
- Audit source: `b9bbe4a111b944290948b38eab690f7683b5df64b939fe23833a6ef489af327a`

## First guarded build

The import-only attempt with `lake` found on the shell `PATH` was admitted but
exited 1 immediately because `lake` was not found. Retrying with
`./.toolchain/bin/lake` was manually interrupted after about one minute of
silence (exit 130); it produced no artifact. This is not a proof or resource
result. The parent clarified that separate exec calls cannot inspect the
build's process namespace and that prior successful Lean jobs were silent for
several minutes.

The full source compile was admitted with 16.1 GiB host availability and 1.10
GiB cgroup headroom, under `-j1 -M2560`, then exited 1 after about five
minutes. This confirms the selected import closure loaded under the guard; it
does not establish any theorem. The compile used the draft hash above and
reported:

- Lines 32, 37, 42, 47, 52: the zero-bit cases left
  `DirichletCharacter.conductor 1 = 1`; add the explicit
  `DirichletCharacter.conductor_one` simp theorem.
- Lines 63 onward: `expectedGenusPrimitiveConductor` was not opened from
  `GenusDirichletRowDataRun20260920`.
- Line 193: a missing closing parenthesis caused a parser diagnostic.

These source-level issues have been repaired in the current draft. No `.olean`
was produced by this failed source compile. A rerun and separate axiom audit
remain pending shared-slot admission.

The first draft used `GenusDirichletPrimitiveActualRun20260920`; source review
trimmed this to the direct pair `GenusDirichletPrimitiveRun20260920` and
`GenusDirichletConductorsActualRun20260920`, since the analytic actual leaf
adds imports this character-only theorem does not need.

The repaired, import-trimmed source compiled under the guard far enough to
report one ordinary Lean proof error after about five minutes, with no memory
stop: `ac_rfl` did not unfold `expectedOddConductor` in
`selectedLocalConductorProduct`, leaving the expanded product equal to the
same factors in the opposite grouping/order. The five zero-bit conductor
cases and the earlier missing-name/parser diagnostics are resolved. The
current draft unfolds `expectedOddConductor` before `ac_rfl`, and removes five
unused simp arguments. No `.olean` was produced by this run. Rerun and audit
are pending shared-slot admission.

Current repaired module hash:
`29b3264d7c4d3b7b8c6179a602ada15f4d93bb932a08b5a0f808f57abb1584a1`.

## Guarded compile and axiom audit

The repaired source compiled successfully under the shared guard with
`./.toolchain/bin/lake env lean -j1 -M2560`; admission observed 14.7 GiB host
availability and 1.41 GiB cgroup headroom. The command exited 0 in about five
minutes and produced
`.lake/build/lib/lean/UnitDistance/GenusLunaPrimitiveAtomExpansionLight20260923.olean`.
The audited source hash is the current module hash above.

The separate focused audit also exited 0 under the guard (14.9 GiB host,
1.58 GiB cgroup headroom). Its exact output for
`genusPrimitiveCharacter_apply_eq_local_primitive_atoms` was:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

The audit artifact is
`.lake/build/lib/lean/UnitDistance/GenusLunaPrimitiveAtomExpansionLight20260923Audit.olean`;
the audit source hash is
`b9bbe4a111b944290948b38eab690f7683b5df64b939fe23833a6ef489af327a`.
The temporary import-probe source was removed after the runs; its interrupted
attempt is recorded above as exit 130, not as a proof or resource failure.

## Next source-level step: explicit residue formula

After the atom theorem compiles, the residue interface can be built in small
local lemmas. The 2-primary factor is determined by `b₁` and the parity of
`b₀+b₂+b₄+b₅`: its common character reduces to `1`, `commonChi4`,
`commonChi8`, or `commonChi8'`. The existing identity
`commonChi4_mul_commonChi8` supplies the last case, and
`ZMod.χ₄_nat_eq_if_mod_four`, `ZMod.χ₈_int_eq_if_mod_eight`, and
`ZMod.χ₈'_int_eq_if_mod_eight` provide the explicit mod-4/mod-8 residues.
Mask-bit case splits are at most the five bits that select this local type.

For each odd selected atom, reduce bit 0 to the trivial conductor-1
character and bit 1 to `primeQuadraticCharacter p`. At `p = 3, 5, 7, 11, 13`,
the existing `quadraticChar`/`quadraticCharFun` reduction and `IsSquare`
decisions give short finite residue tables. Their positive residue classes
are respectively `{1}`, `{1,4}`, `{1,2,4}`, `{1,3,4,5,9}`, and
`{1,3,4,9,10,12}`; zero maps to zero and other nonzero classes map to -1.
Each table can be checked by cases on `n % p` or the representative in
`ZMod p`.

The final statement composes the six local residue functions with the proved
atom expansion. For nonunits, retain the full Dirichlet-character evaluation:
`DirichletCharacter.apply_eq_zero_iff` shows a selected local atom vanishes
when its residue is zero, so the product vanishes whenever the integer is not
coprime to the primitive conductor. For units, each residue table directly
gives the sign. This avoids a separate reciprocity theorem and matches a
finite checker that evaluates the six local residue classes.

### One-atom χ₇ source draft

`UnitDistance/GenusLunaPrimitiveSevenAtomResidue20260923.lean` now attempts a
concrete all-integer residue lemma for the optional conductor-seven atom. Its
right side is the Legendre sign `legendreSym 7 a` when mask bit 4 is selected,
and 1 otherwise, with an outer zero cutoff at integers not coprime to the
full actual mask conductor. That outer cutoff is necessary: the local
primitive character is lifted to the entire conductor, so it vanishes at
nonunits of that larger modulus even if they are units modulo 7. The source
reduces the bit cases to the primitive-character change-level theorem and
the definition of `primeQuadraticCharacter`.

This is a **source-only draft**. It has not been compiled or axiom-audited;
the checked atom theorem above does not certify this additional residue
statement. The new source is intended to import only the already checked
light atom module. Source hash:
`a8d8f5e8b7a6dd5dbe1512c4034c1cf232c4d0fe2297f65418489efa21c7459a`.

### All-mask explicit discriminant-factor character draft

`UnitDistance/GenusLunaPrimitiveDiscriminantCharacter20260923.lean` states a
pointwise all-integer reduction from the actual primitive character to the
explicit factorization

```text
χ₂(m,a) · ∏_{p∈{3,5,7,11,13}, bitₚ(m)=1} (a/p),
```

where `χ₂` is selected from `1`, `χ₄`, `χ₈`, and `χ₈'` by the χ₄ exponent
parity and χ₈ bit. In standard Kronecker notation this is the local
factorization of `(D_m/a)`. The arithmetic lemma in the draft decomposes the
repository's `expectedGenusFundamentalDiscriminant m` into this 2-primary
discriminant part and the signed odd part with factors `-3, 5, -7, -11, 13`.
There is no Mathlib Kronecker-symbol function in the current local source, so
the source states the explicit factor formula directly rather than claiming a
library-level equality to an unavailable symbol.

The pointwise theorem puts an explicit coprimality cutoff at the actual
conductor. This handles every nonunit (including selected primes) directly
from `DirichletCharacter.apply_eq_zero_iff`; at units, the six hypotheses are
the remaining atom evaluation lemmas. Those are the exact proof obligations:

* reduce `commonTwoCharacter m` to `1`, `commonChi4`, `commonChi8`, or
  `commonChi8'`, using `commonChi4_sq`,
  `commonChi4_mul_commonChi8`, and the mask parity;
* identify the primitive 2-primary atom with the corresponding modulus 1,
  4, or 8 residue character, then use Mathlib's all-integer
  `ZMod.χ₄_int_eq_if_mod_four`, `χ₈_int_eq_if_mod_eight`, and
  `χ₈'_int_eq_if_mod_eight`;
* for each odd bit, lift the primitive common-level atom to a unit of the
  actual conductor and apply the staged generic
  `primeQuadraticCharacter_apply_eq_legendreSym` theorem, plus the bit-0
  trivial-character case.

All six local equalities are needed only under coprimality to the actual
conductor. The checked atom expansion then gives the product formula. At a
nonunit, the primitive character and the unitized right side both vanish.
Removing the outer cutoff to state a pure symbol at every integer additionally
requires the elementary proof that the local factor product vanishes at every
nonunit of the factored conductor; the draft deliberately does not assume
that lemma without proof.

The source is **uncompiled and unaudited**; the staged generic odd-prime
lemma is also not yet included in a checked build. Source hash:
`ca2c418fe3b8d4b6b2f59c47d67e424077785e1770d17dc9745eb39fc859375b`.

### Mathlib-only lifted odd-atom bridge

`UnitDistance/GenusLunaOddAtomLegendreMathlib20260923.lean` is the checked
Mathlib-only base identity
`castQuadraticCharacter_apply_eq_legendreSym`; its audit reports
`[propext, Classical.choice, Quot.sound]`. I drafted
`UnitDistance/GenusLunaOddAtomLiftMathlib20260923.lean`, which imports only
that small module and states the lift formula for an arbitrary odd prime
dividing a level `C`. On units it rewrites `changeLevel` to the prime-level
character and uses the checked cast identity; on nonunits it uses
`DirichletCharacter.apply_eq_zero_iff`. Its all-integer statement has the
necessary global cutoff
`if IsCoprime a C then (legendreSym p a : ℂ) else 0`.

The generic bridge is structurally enough for each selected odd atom once its
local primitive factor is shown to be the prime-level quadratic character
(selected bit 1), or the trivial conductor-1 character (bit 0). It cannot by
itself prove those five selected-factor identifications. In particular,
importing the checked all-mask atom module to state specialized theorems
inherits its `GenusDirichletConductorsActualRun20260920` and transitive
`GenusDirichletConductorsRun20260920` dependency closure; adding a small
adapter does not remove that closure. A genuinely closure-light specialized
proof would require extracting/refactoring the local atom definitions and
their conductor/divisibility lemmas into a smaller source module. No such
refactor was made here. The current generic bridge is a **source-only draft**;
it was not compiled or audited and does not constitute five checked atom
formulas. Hashes: checked Mathlib base
`c05ebded917bb109116e6723cc1b55ad7fd163040db6f6498bf7e25331122796`, draft
lift bridge
`b594a9447c67c50a9d93cb0ae21a2b4b4bc32191acb546680a161ea7b85f1b70`; focused
audit source `GenusLunaOddAtomLiftMathlib20260923Audit.lean` hash
`ab413d434beec86444cf4755da9f1a7d82f77b5e71f16cd575700d75b8fc3e18`.
The first guarded incremental compile was admitted at 14.4 GiB host available
and 1.31 GiB cgroup headroom, then exited 1 after five seconds on an ordinary
Lean error: `apply_eq_zero_iff` takes the character before the integer. The
source now passes the lifted character explicitly in that call. No artifact
was produced; the repaired source and focused audit remain uncompiled pending
shared-slot admission. Two later guarded retries were deferred with exit 75
after about 57 and 56 seconds, respectively, reporting the shared lock busy
or insufficient host/cgroup headroom (guard minimums 10 GiB host and 1 GiB
cgroup). Neither retry admitted Lean or created an artifact. The audit was
not run; further retries await a new slot/resource allocation.

### 2-primary unit-evaluation draft

`UnitDistance/GenusLunaPrimitiveTwoAtomResidue20260923.lean` isolates the
2-primary obligation without importing the staged odd-prime lemma. It proves
in source the reduction

```text
commonTwoCharacter m =
  if b₁=1 then (if parity=1 then commonChi8' else commonChi8)
  else (if parity=1 then commonChi4 else 1),
```

where `parity = (b₀+b₂+b₄+b₅) mod 2`. The proof derives
`commonChi4 ^ 2 = 1`, reduces the raw χ₄ exponent modulo 2, and uses the
existing identity `commonChi4_mul_commonChi8` in the `χ₈'` case. Each of the
three common-level nontrivial characters is then evaluated by transporting
its primitive character to the primitive base character; the trivial case
uses `DirichletCharacter.primitiveCharacter_one`. Finally,
`changeLevel_eq_cast_of_dvd'` transports the atom from its local conductor to
the actual conductor under the unit hypothesis.

This would discharge `hTwo` in the all-mask discriminant-factor theorem; its
residue definition is definitionally the same χ₄/χ₈/χ₈' case split. The
source contains a complete proof attempt, but remains **uncompiled and
unaudited**. Remaining uncertainty is Lean elaboration, mainly the exponent
reduction rewrite (`Nat.mod_add_div`/`pow_mul`), unfolding the common-level
abbreviations, and rewriting the primitive change-level theorem. Source hash:
`a99d6b41561b8577405c9326c448e8923e390b35903e8758edbbe1c4bd382028`.

## Independent source review of the atom expansion

A pre-build independent read-through found no mathematical counterexample or
missing hypothesis in the atom expansion. The mask coordinates, five odd
factors, and 2-primary parity match the conductor module; the common-level
lift and injectivity argument covers every integer. That review did not
compile the draft at the time; the later guarded build and audit above are the
verification evidence for the atom expansion. It did not review the separate
χ₇ residue draft.
