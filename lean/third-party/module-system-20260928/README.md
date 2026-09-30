# Module-system compatibility layer — September 28, 2026

This layer records the module-system port of the selected conditional unit-distance
proof. It applies to project-owned and vendored files without changing their
copyright, authorship, or licensing. Earlier upstream manifests and compatibility
patches remain historical baselines.

The [manifest](manifest.json) records every insertion and before/after SHA-256
digest against frozen candidate24, archive digest
`bb973e41a5bd4937eee6413fe459340d0009dbd049737b945951b29f18d284b0`.
Of 2,164 active source files, 2,135 legacy files were converted and 29 existing
module-system files were unchanged. The separate generated `UnitDistance.lean`
entrypoint now uses `module` and `public import SolutionZeta`.

The conversion inserts a `module` header, makes the existing imports public,
and opens an exposed public section. It enables Lean 4.35's documented
`backward.privateInPublic` compatibility option to retain access to existing
private helpers without renaming them. Warnings remain enabled. This option
changes module visibility; it does not add an axiom or disable kernel checking.
The recorded insertions can be removed to recover the original source bytes.
The base port preserves mathematical bodies and the ordered import graph.

The subsequent [first repair layer](repairs-01.json) adds two explicit Mathlib
owner imports in `StudentSchwartzGrowth.lean`. Its legacy imports exposed
these declarations through Mathlib's private dependencies; the new module
boundary does not. The two added import edges are recorded with exact
insertions and hashes. This header-only repair leaves the mathematical body
unchanged and passes a focused compile. It requires a new complete build and
verification together with the rest of the port. Reversing the repair and
then the base port recovers the original source.

The [second repair layer](repairs-02.json) similarly adds the explicit
`Mathlib.Analysis.Calculus.ContDiff.Bounds` import in
`StudentSchwartzGaussian.lean`. The repaired Gaussian module and its
Approximation and Coordinates dependents pass a separate focused compile.
This second header repair also leaves every mathematical body unchanged.

The [third repair layer](repairs-03.json) adds explicit Mathlib owner imports
for `FaithfulSMul` and `Commute.zpow_zpow_self`, and an `import all` declaration
for the existing project module containing the private residue
algebraic-closure instances. Its three affected modules pass isolated
compiler checks.

The [fourth repair layer](repairs-04.json) enables Lean's documented
`backward.proofsInPublic` option in five files whose legacy `by` proofs constrain
metavariables during elaboration. The option retains that elaboration behavior;
it adds no axioms and does not alter kernel checking. Two further `import all`
declarations restore private instances from the existing directly imported
`ConcreteReciprocityTransport` and `DivisionPolynomial` modules. Their public
reexports are preserved. All seven affected modules pass isolated compiler
checks. Both layers retain every theorem statement and proof body.

The [fifth repair layer](repairs-05.json) changes one proof slice in
`equalCharacteristicThetaAfterBracketCoefficient_zero`, in
`ThetaFirstIdentity.lean`. Instead of asking `simp [mul_comm]` to normalize
both product orders, the proof composes `mul_comm` with the existing equality
explicitly. Its statement, assumptions, definitions and all other file bytes
are unchanged. The exact repaired module passes a focused compile. This
dedicated proof-repair layer records the old and new slice and its UTF-8 byte
offset; the checker accepts only the tested replacement inside the exact
recorded theorem. Unlike the header-only layers, this layer deliberately
changes one proof body, without adding an axiom or weakening a statement.

The [sixth](repairs-06.json) and [seventh](repairs-07.json) layers repair three
downstream files revealed by the next integration build. `FiniteSubgroupResidueDegree`
imports the private residue-field Galois instances directly;
`ConcreteReciprocityPrimeNorm` imports the private topological and bundled
finite-quotient instances from their two owners; `PrimitiveAction` imports the
private characteristic instances from `DivisionPolynomial`. These four
`import all` declarations retain all mathematical bodies and statements.
All three exact files pass isolated compiler checks, with the direct imported
artifact hashes unchanged before and after each check.

The [eighth layer](repairs-08.json) applies the same explicit commutativity
argument as repair 05 to
`equalCharacteristicDirectThetaAfterBracketCoefficient_zero` in
`DirectThetaFirstIdentity.lean`. Its isolated compile passes and the imported
artifact hashes remain unchanged. The narrow proof-repair validator separately
binds this second exact path, theorem statement, preceding proof context and
replacement slice. No other proof edits are admitted by those two records.

The [ninth layer](repairs-09.json) adds the same targeted `DivisionPolynomial`
import to `FiniteParameters` and the `backward.proofsInPublic` option to
`FiniteResidueFinrankTransfer`. Both header-only repairs pass isolated
compilation, with direct imported artifact hashes unchanged before and after.
Their mathematical statements and proof bodies are unchanged.

The [tenth layer](repairs-10.json) repairs seven downstream modules reached by
the next integration attempt. Six files explicitly import their private
instance owners: `FreeRankOne`, `LevelAutomorphisms`, `CompletedPrimitiveAction`,
`UnramifiedComparison`, `NormSubgroupOrderEmbedding` and
`IntermediateFieldNormResidueNaturality`. `FixedFieldNormResidueNaturality`
uses the legacy proof-elaboration option. All seven exact files pass isolated
compilation with stable direct imported artifact hashes. Every mathematical
statement and proof body is unchanged by this layer.

The [eleventh layer](repairs-11.json) restores private instances for
`FinitePlaceAlgebraicLocalizationAlgClosure` and `RationalPrimeCompletion`.
The first uses the generic algebraic-closure instance from
`ResidueAlgebraicClosureDegree`; Lean omits that instance's unused finite-field
section parameter. The second imports the precise rational-completion algebra
instance used by the existing equivalence. Both exact files pass focused
compilation without mathematical body changes.

The [twelfth layer](repairs-12.json) changes the proof of
`MaxEverywhereUnramifiedProPGaloisGroup.instT2Space` to apply Mathlib's
`krullTopology_t2` theorem explicitly. The complete instance statement is
unchanged, and the required algebraicity already follows from the field
construction. This dedicated instance-proof schema accepts only the exact
recorded statement and replacement. Its focused compile passes with stable
direct imported artifact hashes; it adds no hypothesis or axiom.

The [thirteenth layer](repairs-13.json) repairs thirteen further observed
integration failures. Twelve files explicitly import their existing private
instance owners (`ConcreteReciprocityTransport`, `ConcreteReciprocityCanonical`,
`DivisionPolynomial`, or `CompletedLevel`); `FixedFieldContinuousNaturality`
uses the same documented proof-elaboration compatibility option. All thirteen
isolated compiles pass with unchanged direct imported artifacts. Statements
and proof bodies are preserved exactly.

The [fourteenth layer](repairs-14.json) adds the private-instance owner
`Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances` to
`AdeleBaseChange`. Its unchanged scalar-tower proof then passes an isolated
compile. This restores access to the existing completion-algebra instances
without changing a mathematical statement or adding an assumption.

The [sixteenth layer](repairs-16.json) records three further failures first
reproduced by compiling unchanged direct consumers of repair13 modules.
`DirectThetaFrobeniusFixed`, `AmbientPrimeWitness`, and `HigherUnits` each
need an explicit import of their existing private characteristic or Hausdorff
instance owner. The exact header-only candidates then pass with stable parent
artifacts. The other seven tested direct consumers pass unchanged. No repair15
manifest was needed; its five unchanged baseline checks are retained as evidence.

The [seventeenth layer](repairs-17.json) restores the existing private
`DivisionPolynomial` characteristic instances for `Ramification.PrimitivePoint`.
Its unchanged baseline reproduced four missing-instance errors; the exact
header-only candidate then passed isolated compilation. The statement and
proof bodies are unchanged. Other next-frontier checks are recorded separately;
an isolated wall-clock timeout supplies no negative proof verdict.

The [nineteenth layer](repairs-19.json) explicitly imports `CompletedLevel`
for `CompletedFrobeniusFixedFieldPrimitive` and `HigherUnitFrobeniusFixed`.
Their unchanged baselines failed to find the existing private characteristic
instances; both exact header-only candidates then passed. The neighboring
`CompletedFrobeniusFixedFieldAlgebra` passed unchanged. No mathematical body
changes were needed. The intervening 18 checks produced no source repair.

The [twentieth layer](repairs-20.json) imports the private Hausdorff-instance
owner `ConcreteReciprocityTransport` in `AmbientPrimeWitnessComparison`.
The integration log first reports missing instances, followed by heartbeat
and unknown-symbol errors in dependent declarations. The exact header-only
candidate passes with unchanged heartbeat limits. No mathematical statement
or proof body was changed.

The [twenty-first layer](repairs-21.json) explicitly imports all of
`Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances` in
`NormTopology.ExtensionBehavior`. Its existing proof unfolds the public
`completionMap` definition, whose body is not exposed by that Mathlib module.
Accessing the exact defining module restores this unfolding; the isolated
candidate passes with its complete mathematical body unchanged.

The [twenty-second layer](repairs-22.json) replaces the tensor-induction proof
of `rationalRelativeAdeleEmbedding_comp` with an application of Mathlib's
`Algebra.TensorProduct.map_id_comp`. The complete statement and hypotheses are
byte-identical. The exact revised file passes focused compilation without
raising heartbeat limits. Its dedicated provenance schema records the uniquely
named declaration because the old induction proof appears elsewhere in the
same file; the whitelist binds both exact proof texts, the unchanged statement
and preceding context. Statement changes and unrelated proof edits are rejected.
The subsequent 23 baseline probes required no source repair or manifest.

The [twenty-fourth layer](repairs-24.json) adds exact private-instance owner
imports to `Ramification.DisplacementValuation` and
`FixedFieldIntrinsicReciprocity.PrimeComparison`. The first restores the
`DivisionPolynomial` base/closure characteristic instances, including the
inherited intermediate-field instance; the second restores
`ConcreteReciprocityTransport`'s Hausdorff instance. Both complete files pass
isolated compilation with their statements, assumptions, proof bodies and
heartbeat settings unchanged. The numbered 23 checks required no source repair.

The [thirty-second layer](repairs-32.json) restores `DivisionPolynomial`'s
private characteristic instances in `FiniteLevel.UnitQuotientGalois`. Its
unchanged regression baseline failed at concrete ambient-bracket applications;
the exact import-all candidate passes with stable imported artifacts and no
changes to statements, assumptions, proof bodies or heartbeat settings. Its
parent `RealIndexSteps` passes unchanged. The existing public import is retained.

The [thirty-third layer](repairs-33.json) imports the exact private
`NumberField` instance owner `IdeleClassDirectLimitAbstractFixedField` in
`CyclotomicIdeleClassValuation`. Four statement elaboration failures in the
integrated build are resolved by this header-only change; the complete candidate
passes with statements, assumptions, proof bodies and heartbeat settings
unchanged. The private instance was already present in the pre-port source.

The [thirty-seventh layer](repairs-37.json) enables Lean's
`backward.proofsInPublic` compatibility option in `FiniteGaloisRealizationCore`.
The integrated build reported an unresolved metavariable while elaborating a
public proof. The exact option-only candidate passes focused compilation with
all imports, mathematical statements, hypotheses, proof bodies and heartbeat
settings unchanged.

The [thirty-eighth layer](repairs-38.json) inserts one local, Prop-valued
`T2Space` instance proved by Mathlib's `krullTopology_t2` into
`ideleClassComponentQuotientEquivMaximalAbelianGalois`. This is the fifth
recorded proof-code change, following 05, 08, 12 and 22. It retains the complete
declaration type, underlying equivalence, original proof steps and heartbeat
settings. The exact full file passes focused compilation. The instance-proof
schema accepts only this named definition and the previously recorded instance
in repair 12; it binds the full before/after definition, unchanged type,
preceding docstring and UTF-8 byte offset. It does not permit arbitrary changes
to definition bodies or mathematical data.

The [thirty-ninth layer](repairs-39.json) imports the existing private
compactness-instance owner `AbsoluteUnramifiedGaloisSequence` in
`ProTwoH2AbsoluteKernel`. This owner was already in the module's dependency
closure. The exact header-only candidate passes focused compilation with
statements, hypotheses, proof bodies and heartbeat settings unchanged.

The [fortieth layer](repairs-40.json) adds the direct public import
`Mathlib.Analysis.CStarAlgebra.Classes` to `SolutionZeta`, matching the existing
Challenge import. This exposes the declaration used by its existing local
instance-suppression attribute. The complete candidate passes focused
compilation with that attribute, definitions, proof and hypotheses unchanged;
no project module is added to the selected closure.

The selected project closure still contains 2,163 modules. Three unused
historical diagnostic sources are retained in the research repository and
candidate24 archive, rather than being redistributed as current submission
sources. Their old receipts are unchanged. The new package contains 2,165
Lean files, including the active audit and generated entrypoint.

The source-format gate and reversible source-identity checks are recorded in
`verification/module-port-20260928/source-gate-and-body-identity.json`;
`verification/module-port-20260928/selection-after-port.json` checks the closure.
After the explicit-import repair,
`verification/module-port-20260928/source-gate-repairs-01.json` records a new
passing lexical gate for all 2,165 files, and
`verification/module-port-20260928/source-selection-repairs-01.json` checks
the two recorded import additions and recovery of the original sources.
The corresponding checks including all four repair layers are
`verification/module-port-20260928/source-gate-repairs-04.json`,
`verification/module-port-20260928/source-selection-repairs-04.json`, and
`verification/module-port-20260928/provenance-repairs-04-validation.json`.
They pass for all 2,165 packaged Lean files, preserve the 2,163-module selected
project closure, and recover all 2,164 original source inputs exactly.

The subsequent checks including the fifth proof-repair layer also pass:
`verification/module-port-20260928/source-gate-repairs-05.json`,
`verification/module-port-20260928/source-selection-repairs-05.json`, and
`verification/module-port-20260928/provenance-repairs-05-validation.json`.
The module/file counts are unchanged, and all original source bytes remain
recoverable. These are source-format and provenance checks, not a complete
compilation or independent kernel verdict.
These are source checks. Compilation and full verification of the migrated
candidate require their own receipts; the old candidate's kernel passes do
not certify a changed export.

The provenance helper in `scripts/module_port_provenance.py` checks the current
file against its recorded digest, reverses the exact repair and base-port
insertions and the recorded proof replacement in order, and checks the recovered digests.
The older provenance validators then use the
recovered bytes against their unchanged upstream manifests and patches.
