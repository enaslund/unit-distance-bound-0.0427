# Planar unit distances from one fixed zeta inequality

This is the formalization of the author's interim note at exponent 1.0418235
(`docs/manuscript/`), a private note never released before its inclusion in
the public repository. Its lesser result is superseded by the paper *An
Exponent of 1.04273 for the Unit Distance Problem*, which incorporates its
methods.

This package proves a **conditional theorem**: one explicit inequality H for
the Dedekind zeta function of a fixed number field implies that finite sets
`U_j` in the ordinary Euclidean plane satisfy

```text
|U_j| → infinity,
(number of unordered unit-distance pairs in U_j) / |U_j|^1.0418235 → infinity.
```

The exponent is exactly `2083647/2000000`. H uses threshold
`42165819/1000000000 = 0.042165819`, the zeta value at `1 + 1/12000`, and
its logarithmic derivative at `2`. **H remains unproved in Lean.** The field
is specified by nineteen explicit radicals in the Challenge. Its degree
`524288`, the sufficient pair estimates, discriminant bound, growing
arithmetic family, analytic transfer and planar construction are internal
proof components. The conclusion makes no assertion for every sufficiently
large cardinality.

## Statement, evidence and package

| Item | Source and scope |
| --- | --- |
| Exact independent statement and proof | [ChallengeZeta.lean](ChallengeZeta.lean), [SolutionZeta.lean](SolutionZeta.lean); sole compared declaration `UnitDistanceZetaSubmission.target_of_canonical_zeta_bound` |
| Exact H and its remaining dependencies | [Assumption ledger](docs/ASSUMPTIONS.md) |
| Mathematical argument and public context | [Conditional submission account](docs/CONDITIONAL_SUBMISSION.md), including dated references and the manuscript-to-H comparison |
| Prior sealed candidate | [Archive 17 record](verification/conditional-20260923/candidate17-packaging-preparation.md) and [post-seal errata](verification/conditional-20260923/candidate17-postseal-errata.md); assess any later archive by its own digest and receipts |
| Dated numerical and formal progress | [September 23 final handoff](docs/FINAL_HANDOFF_SOL_LUNA_20260923.md), which separates included records from later checkout-side evidence |
| Reproduction | [PALOMAR_REPRODUCE.md](docs/PALOMAR_REPRODUCE.md); builds, axiom audits, finite replays and full verification have distinct scopes |

**September 29 source update:** the preceding migrated archive completed all
required local verification checks. Its 102.04-GiB comparator peak prompted a
[symbolic discriminant and finite-certificate proof changes](docs/HOSTED_RESOURCE_REPAIR_20260929.md)
for hosted capacity. The changed source retains every public theorem statement,
definition and hypothesis. This source snapshot is sealed before its own full
run; subsequent verification receipts identify the exact archive they certify
and are distributed separately. The older dated checkpoints below describe
their own sources and must not be read as the status of this new snapshot.

The manuscript supplies an external computer-assisted argument for H. Its
numerical certificate and subsequent finite checks are evidence for that
argument, not a Lean proof of H. Research modules added after the selected
proof was sealed lie outside its proof closure. The checked conductor-13
estimate came from the preceding September 22–23 run; the subsequent
128-character, 32-row H6 and large finite-prime checks are external evidence.
Their scopes and shared software dependencies are recorded in the handoff
and linked receipts. In the research repository, `lean-formalization/STATUS.md`
is the canonical live status; `lean-formalization/research/README.md` and its
verification index map integration work and historical evidence. Those live
repository maps are separate from this standalone source package.

**Historical September 28 module-system migration checkpoint:** the selected working sources had
been ported for PalomarSubmission revision
`65f0154ed776cd26c224254aa57b379137f28b0d`. The mechanical port passed the
source-format gate and small visibility/audit pilots. Integration compilation
then exposed dependencies on private transitive imports, private instances,
and legacy proof elaboration. Recorded header repairs add explicit
Mathlib imports, targeted `import all` declarations, and the pinned
`backward.proofsInPublic` compatibility option for legacy proof elaboration. Two proof-only
layers make multiplication-commutativity steps explicit in `ThetaFirstIdentity`
and `DirectThetaFirstIdentity`; both theorem statements are unchanged. A further
proof-only layer supplies the existing Mathlib theorem `krullTopology_t2`
directly for an unchanged Hausdorff-instance statement. A fourth proof-only
layer applies Mathlib's `Algebra.TensorProduct.map_id_comp` to the unchanged
adele-embedding composition theorem, replacing its tensor-induction proof.
A fifth proof-only layer supplies `krullTopology_t2` as a local, Prop-valued
Hausdorff instance in `ideleClassComponentQuotientEquivMaximalAbelianGalois`.
Its declaration type and underlying equivalence are unchanged.
All repaired modules passed isolated compiler checks; the complete package rebuild was then unfinished. The
reversible base port and repairs are recorded under
`third-party/module-system-20260928/`. Mathematical statements, data and
assumptions were unchanged. Full compilation and verification of that migrated candidate
were still pending at that checkpoint; the historical passes below concern earlier snapshots.

At the September 27, 08:04 UTC package checkpoint, candidate23's deterministic
export and archive-only metadata gate passed for the exact archive recorded in
[its gate receipt](verification/conditional-candidate23-20260927/candidate23-archive-check.json),
SHA-256 `a8b47796a275a598e2be85c9f6d4e28b560782047b4b7d6e8ea6c5c3f3d7132d`. Candidate23 has no full verifier result; no current Lean 4.35
full-verifier pass or proof of H is claimed at that checkpoint. Candidate22's
archive-only gate passed earlier, while candidate21's preserved metadata gate
failed because its wrapper omitted the explicit policy revision. The older
archive-07 verifier result remains historical and is not evidence for a later
source archive.
The September 25 PalomarSubmission verifier revision,
[`a59f25bd8a66bf6faf3a4f4260d412989c0185ea`](https://github.com/PalomarRegistry/PalomarSubmission/tree/a59f25bd8a66bf6faf3a4f4260d412989c0185ea),
requires Lean `v4.35.0-rc2` or later. The selected source tree pins that Lean
version and
[matched Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`](https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55)
with 2,163 selected Lean modules. The full selected build passed on the exact
source digest in the [September 24 build receipt](verification/conditional-20260924/accepted-selected-build-20260924.md).
The subsequent candidate 18 fresh build and exports succeeded, but structural
comparison rejected an implicit instance mismatch. The
[September 25 correction](verification/conditional-20260925/comparator-fix.md)
locally fixes the instance choice in the two submission wrappers; its focused
dependency comparison passes. The
[focused check receipt](verification/conditional-20260925/focused-fix-check.json),
[comparison log](verification/conditional-20260925/structural-comparison.log)
and printed declarations
`verification/conditional-20260925/finite-*-local-priority.log`
are included. The original diagnostic Lean sources remain preserved in the
research repository and older sealed archives. Those unused historical sources
are outside the selected proof closure and are not shipped in the new package.
These corrected sources need their own full
verification receipt and are not the exact pass-50 source snapshot.
Candidate 19 subsequently passed fresh build, structural comparison, the
configured axiom check and Lean's default kernel, but its independent
checkers failed: con-ron was terminated by the host memory guard, and NanoDa
overflowed on a vector-valued rational calculation. The
[September 26 repair](verification/conditional-20260925/kernel-repair.md)
replaces that calculation with 256 exact scalar proofs and structural
assembly of the same vector equality, plus 64 scalar proofs of the required
cell-radius values. The
[module compile receipt](verification/conditional-20260925/kernel-repair/candidate20-cell-module-compile.json),
[source receipt](verification/conditional-20260925/kernel-repair/candidate20-cell-source-promotion.json),
[bracket generator](verification/conditional-20260925/kernel-repair/generate-bracket-certificates.py)
and [cell generator](verification/conditional-20260925/kernel-repair/generate-cell-certificates.py)
record the change. Both unchanged independent checkers passed the
[focused export](verification/conditional-20260925/kernel-repair/candidate20-focused-check.json).
A fresh candidate 20 run completed its build and exports, then stopped at the
comparator's 19.6 GiB memory ceiling. Its
[terminal report](verification/conditional-20260925/standalone-20260926T054623Z/local-execution.json)
records `provider.resource_exhausted` without a final comparator verdict.
The subsequent isolated one-worker con-ron
[replay](verification/conditional-20260927/conron-one-worker-20260927T044707Z/replay.json)
stopped at declaration 146,000 of 149,249 when the host memory guard crossed
its 3.5 GiB stop threshold. Retry2 later stopped at 148,000/149,249 when
available host memory reached 3.423931 GiB; both are incomplete infrastructure
stops without a kernel verdict. Candidate23's separate export and metadata
receipt is recorded above; no full verifier run is established by either
package gate. A complete verification of the repaired source is still
required; the theorem and its sole hypothesis H are unchanged.
Archive preparation and full verifier execution have separate receipts;
this embedded account does not claim a current verifier pass. No remote
submission or official Palomar acceptance is claimed.

## Provenance

The source manuscript, *A lower exponent of 1.0418235 for planar unit
distances*, states an unconditional result; the extra H premise is the
material difference in this formalization. It is an unrefereed AI-assisted
preprint produced under Eric Naslund's direction. The exported package
includes it under `docs/manuscript/`. The conditional Lean theorem does not
establish an improved unconditional public bound, and novelty of the
conditional reduction has not been established.

[SUBMISSION_PROVENANCE.md](docs/SUBMISSION_PROVENANCE.md), [NOTICE](NOTICE),
[formalization.yaml](formalization.yaml) and `third-party/` record AI
assistance, substantial upstream ports, revisions and licenses. The permitted
proof axioms are `propext`, `Quot.sound` and `Classical.choice`; there are no
Solution definition holes. The repository license is Apache-2.0 with upstream
notices retained. Dated authorship and review details remain in the handoffs.
