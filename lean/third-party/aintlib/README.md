# AINTLIB completed Dedekind zeta and explicit formula source

This is an attributed source port of the 28-module dependency closure of
`DedekindResidue.ExplicitFormula.WeilAssembly` in
[AINTLIB](https://github.com/CBirkbeck/AINTLIB), at commit
`a302aeacd86053f9d5f991fbbf664e1cc1051d08`.
The original files are under `projects/DedekindResidue/DedekindResidue/`
and `projects/Chebotarev/CebotarevDensity/NumberFieldEulerProduct.lean`.
Copyright and author headers are preserved. The upstream Apache 2.0 license
is included as `LICENSE`; exact upstream and local hashes and path mappings
are in `manifest.json`. Source files live under
`UnitDistance/Upstream/AINTLIB/`.

Two patch files record the proof and extraction changes against the pinned
upstream source, taken before import relocation: `compatibility.patch`
covers five files (`CebotarevDensity/NumberFieldEulerProduct.lean`,
`CompletedZeta/AnalyticControl.lean`, `ExplicitFormula/AuxAdmissible.lean`,
`ExplicitFormula/GammaSide.lean` and `ExplicitFormula/RectangleContour.lean`),
and `zero-summability-extraction.patch` covers the sixth,
`ExplicitFormula/ZeroSummability.lean`. The proof-only changes accommodate
the repository's earlier Lean 4.32.0 / Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997` pin: explicit parameters in
logarithmic-derivative product lemmas, older product-inequality names,
reversed ideal-product containment lemma names, older Lp convergence API,
and explicit real/imaginary projection coercions. Mathematical statements
and namespaces are preserved. Upstream uses Lean 4.35.0-rc1. The selected
package's current pins are recorded in `lean-toolchain` and the Lake lockfiles;
the selected Lean 4.35 migration has a separate
`lean-v4.35-migration.patch` and pre-migration hash records in `manifest.json`.

Beyond the patches, every shipped file differs from upstream in its import
lines, and the patches do not record these import changes: 23 files relocate
`DedekindResidue.*` imports to `UnitDistance.Upstream.AINTLIB.*`; 25 files
narrow upstream's bare `public import Mathlib` to the specific Mathlib
modules they use; `ExplicitFormula/FourierJordan.lean` and
`ExplicitFormula/GammaSide.lean`, which have no bare Mathlib import upstream,
add specific Mathlib imports instead; `CompletedZeta/GRH.lean` has only a
relocated import; and `CebotarevDensity/NumberFieldEulerProduct.lean` has its
imports unchanged. The 23 files outside the two patches have no proof-text
change at all (checked on 2026-09-22 by applying the patches to the pinned
upstream and diffing against the shipped files). Each shipped file carries an
in-file change notice inside its copyright header stating which of these
apply to it (Apache-2.0 section 4(b)); `NumberFieldEulerProduct.lean`, whose
upstream has no copyright header, has a short source-and-change notice added
above `module`. The `local_sha256` entries in `manifest.json` are the hashes
of the shipped files, notices included; the `upstream_sha256` entries are the
pinned upstream hashes. The notices were added on 2026-09-22 by Claude Fable
5.1 (Anthropic) through Claude Code, under the owner's direction; they change
no Lean proof text.

The closure constructs actual ideal-class theta integrals using lattice
Poisson summation, identifies their Mellin transform with Mathlib's Dedekind
zeta function, constructs the entire pole-cleared completion and proves its
functional equation. The larger closure proves growth and contour bounds,
the prime-side logarithmic derivative, Fourier/gamma identities, zero
capture, and the Weil–Poitou explicit formula. The general endpoint
`DedekindResidue.weil_explicit_formula` assumes explicit admissibility
conditions on its test function, including transform decay; it does not
assume GRH. `GRH.lean` defines a separate proposition and an equivalence;
neither inhabitation nor a GRH hypothesis is used in the general formula.

This source does not itself prove that a quotient of completed zeta
functions is entire, the relative-Hecke paired-product realization, or the
manuscript's residue ceiling. The local Tsfasman–Vlăduţ modules develop the
actual sech kernel needed to discharge the general formula's analytic
conditions. The actual specialization and limit transfer are now checked: the local
`TsfasmanVladutBasicInequality` module proves the unconditional prime-weight
budget from actual prime-count limits, degree growth, total complexity and
a root-discriminant bound.

Build and audit receipts for this port are log files under `verification/`:
`completed-dedekind-zeta-build.log` (the `CompletedZeta` closure),
`zeta-zero-summability-build.log`, `weil-tv-build.log` (the
`ExplicitFormula` closure through `WeilAssembly`), `tv-weil-build.log`, and
the axiom audits `tv-weil-axioms.log` (1,675 project declarations, attributed
ports included) and `full-result-build-and-audit.log` (49,091 project
declarations, attributed ports included), each reporting only `propext`,
`Classical.choice` and `Quot.sound`. Those receipts predate the in-file
notices of 2026-09-22; the notice edits are comment-only, and all 29 modules
were rebuilt with `lake build` after the edits on 2026-09-22 (`Build completed
successfully`); that rebuild log is not among the shipped receipts. The source
port has no network dependency at build time.

`ExplicitFormula/ZeroSummability.lean` is a bounded extraction from upstream
`ExplicitFormula/GRHZeros.lean`: it retains the unconditional global zero
divisor, finite zero counts and inverse-square summability. The two
GRH-dependent statements and unused introductory lemmas are omitted.
Retained proofs are unchanged; `zero-summability-extraction.patch` records
the complete selection and import relocation. The narrowing of its bare
`public import Mathlib` to specific modules is not in that patch; it is
stated in the file's header notice.

The local `UnitDistance/HeckeMellinDecay.lean` also adapts the proof of
`isBigO_exp_neg_rpow` from the pinned `CompletedZeta/FEPair.lean`, under the
name `hecke_isBigO_exp_neg_rpow`, with the same statement and argument.
This extraction permits narrow Mathlib imports for the generic Mellin
estimate; attribution is included next to the lemma.

The signed local extensions `HeckeSignedGammaIntegral.lean` and
`HeckeSignedNormalization.lean` adapt the ordinary unsigned change of
variables and normalization proofs from the pinned `MellinAgreement.lean`
and `Existence.lean`. They prove new statements with half-integer real-place
Gamma shifts; they are local extensions, not unchanged upstream extractions.
Their source headers identify this provenance.

The local `EntireRealRayIdentity.lean` generalizes the real-ray identity
argument from the pinned `CompletedZeta/Existence.lean` to arbitrary entire
functions; its source header records the author and Apache-2.0 attribution.
The signed continuation assembly is new local work and does not change any
vendored theorem statement or dependency pin.
