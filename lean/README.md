# Planar unit distances at exponent 1.0427 from one genus-field inequality

This source package states and supplies a Lean proof of the following
conditional theorem: one explicit zeta inequality H on a fixed degree-512
number field implies that there are finite sets `U_j` in the ordinary
Euclidean plane for which

```text
|U_j| → infinity,
(number of unordered unit-distance pairs in U_j) / |U_j|^(10427/10000) → infinity.
```

The exact exponent is `10427/10000 = 1.0427`. This is a sequence theorem;
it asserts no bound at every sufficiently large cardinality. **H remains
unproved in Lean.**

The independent statement is [ChallengeZeta241.lean](ChallengeZeta241.lean),
and [SolutionZeta241.lean](SolutionZeta241.lean) supplies the proof. The
selected declaration is
`UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound`, with
configuration [comparator-zeta241.json](comparator-zeta241.json).

The package also contains the earlier conditional theorem at exponent
`2083647/2000000 = 1.0418235`: [ChallengeZeta.lean](ChallengeZeta.lean),
[SolutionZeta.lean](SolutionZeta.lean), `comparator-zeta.json` and its
metadata `formalization-zeta.yaml`. It assumes a different inequality, for a
fixed field of degree 524288, and 2,048 of its 2,162 modules are shared with
the selected theorem. It is included for reference and is not the Palomar
selection: the default build targets are the 1.0427 theorem, `lake build
SolutionZeta ChallengeZeta` builds the earlier one, and
`verification/ZetaAudit.lean` audits its axioms. `README-zeta.md` was written
as the README of that theorem's separately exported package, where
`formalization.yaml` meant the metadata shipped here as
`formalization-zeta.yaml`.

The field E is generated over the rationals by `sqrt 241` and square roots
of the eight explicit elements listed in the Challenge's `radicandA` and
`radicandB` tables. H is the inequality

```text
log(Re ζ_E(1 + 1/300))/512
  + (1/300) ((L − γ − log(4π))/4 − Re((ζ_E′/ζ_E)(2))/512) < 852/10000,
L = (9/4) log 2 + (1/2) log 3615.
```

The [development account](docs/sqrt241/SUBMISSION.md) describes the arithmetic
tower over `Q(sqrt 241)`, the genus-field bridge, root-discriminant estimate,
finite certificates and planar transfer. The proof uses the ordinary
Euclidean metric on `ℂ` and counts unordered pairs by dividing the ordered
count by two. The intended permitted axioms are `propext`, `Quot.sound` and
`Classical.choice`; H is an explicit theorem parameter.

This archive's [source snapshot](SOURCE_SNAPSHOT.json) and
[selection record](SELECTION.json) identify its exact bytes. Candidate 4 of
this development passed the complete pinned local Palomar pipeline under the
16-CPU/32-GiB profile on September 29, 2026
(`verification/sqrt241-full-20260929/README.md`): fresh build, protected
exports, statement and definition comparison, permitted-axiom checks, con-ron,
NanoDa and Lean's kernel. An earlier attempt had failed when NanoDa ran out of
memory on the dyadic certificate's eightfold multiplication; candidate 4 checks
it through smaller exact multiplications combined by congruence and
transitivity, with the public statement, model data and hypothesis unchanged.

The present sources add proof-internal splits of the pair-mass certificate and
of four group-data certificates so that the kernels fit the 4-CPU/16-GiB
profile; no theorem statement or definition changed. Con-ron, NanoDa and Lean's
kernel each accepted this source's Solution export within 4 CPUs and 16 GiB
(`verification/sqrt241-bounded-20260929/README.md`). The complete pipeline has
not yet run on these exact sources, so this archive needs its own terminal
receipt. Earlier full passes for the 1.0418235 theorem do not verify this
theorem, and a local pass remains distinct from an official Palomar result or
a hosted workflow on an exact public commit.

The [earlier sqrt241 receipts](verification/sqrt241-20260929/README.md) record
a fresh build, imported axiom queries and individual `leanchecker` passes on
239 new closure modules. Their 250-file hash list covers the new wrappers
and all nested Sqrt241 modules, including eleven extras outside the selected
closure. It does not bind all inherited sources or tool binaries. Those
checks predate the merge of the inherited `DyadicCertificates.lean` proof
repair. The new archive and verification therefore have their own identities.

Imported `Lean.collectAxioms` and `#print axioms` results on the pinned rc2
toolchain have the cached-summary limitation documented in
[the preserved assessment](verification/hosted-fit-20260929/requirements/axiom-audit-15226.md).
Read the earlier namespace-audit logs as reported query results. The full
pipeline's separate protected-export traversal checks its own permitted
axioms, statement and definitions, then runs con-ron, NanoDa and Lean's kernel.
Candidate 4's complete run fit within 32 GiB, and the present sources' kernel
replays each within 16 GiB; the complete run of these sources records its own
resource use.

The [quadratic-base research note](docs/quadratic-base-research/README.md)
reports an external computer-assisted result at exponent 1.04273. Its
`certificates/h241_receipt.py` separately computes an upper bound of about
0.0848335193 for H's left side. These are external numerical evidence,
not Lean proofs of H. The [original manuscript](docs/manuscript/README.md)
and the research note are included as source material with their original
authorship and AI-production disclosures. Their local provenance and the
change of conclusion to conditional exponent 1.0427 are recorded in
[formalization.yaml](formalization.yaml).

These embedded research files are provenance copies. Their external replay
drivers expect the full research repository's `papers/` layout and the
original manuscript's supplementary archive; the source-only Lean archive
does not supply that separate external replay environment.

The mathematical development, generators and documentation were produced
with AI tools under Eric Naslund's direction. Earlier reviews were automated
reviews with their stated scopes. They are not human peer review or owner
proof verification. This package is for local verification; publication,
submission, registration and editorial acceptance are not claimed.

The formalization retains its Apache-2.0 [LICENSE](LICENSE), [NOTICE](NOTICE),
and third-party notices under `third-party/`. Embedded manuscript and research
publication material retain their supplied terms; this packaging introduces
no new licence grant for those copies. Historical documentation keeps its
original target and dates. This README supplies the current local verification
scope for the selected sqrt241 source.
