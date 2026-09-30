# Generic entire-function and canonical-product source

This attributed source port selects 12 generic modules and the initial
negation-pairing section, plus generic adaptations of divisor and involution proofs from
[RiemannHypothesis-Formalization](https://github.com/alejandrozu/RiemannHypothesis-Formalization),
commit `753938937e624d1c8bbe4c208517660a672d1b8e`.
The source is by Tristen Harr and licensed under Apache 2.0. Exact source
and local hashes and each modification are recorded in `manifest.json`.
Of the 12 full modules, `ComplexAnalysis/AntiHerglotz.lean` and
`ComplexAnalysis/GrowthRigidity.lean` are byte-identical to upstream; the other
10 differ only in internal import paths (`RiemannHypothesis.*` relocated to
`UnitDistance.Upstream.Hadamard.*`), and each of those 10 carries an in-file
change notice inside its copyright header saying so (Apache-2.0 section 4(b);
notices added 2026-09-22 by Claude Fable 5.1 (Anthropic) through Claude Code,
under the owner's direction; no proof text changed; the 10 modules were
rebuilt with `lake build` after the edits, successfully). The `local_sha256`
entries in `manifest.json` are the hashes of the shipped files, notices
included. Copyright and author headers are preserved. The upstream Lean
version is 4.31.0; these selected proofs were checked under the repository's
earlier Lean 4.32.0 and matched Mathlib pin. Later selected-source migration
changes have a separate `lean-v4.35-migration.patch` and pre-migration hash
records in `manifest.json`; selected build and provenance checks require
their own exact receipts.

The selection proves local uniform convergence, exact divisor and growth
of genus-one canonical products, removable entire quotients for matching
finite divisors, and growth rigidity using Nevanlinna and real-part bounds.
The paired-product section gives an exact reindexing over a fixed-point-free
negation involution. The divisor proofs originally specialized to xi are generalized to an arbitrary
nontrivial even entire function. No xi function or Riemann Hypothesis assumption
is imported. The upstream repository name does not assert that RH is proved.

The new project modules `EntireQuotientFactorization`, `HadamardFactorization`
and `HeckeEntireMonotonicity` combine these generic results with the local
paired-factor estimate. Their conclusions have explicit entire-function,
divisor, summability, symmetry and growth hypotheses. They do not assert an
entire continuation of a relative Dedekind-zeta quotient.

`CanonicalEntireDivisor` constructs the actual multiplicity-bearing zero index,
proves its exact divisor and norm-properness, and constructs its exact negation
pairing. Its canonical divisor depends on the given entire function itself.
