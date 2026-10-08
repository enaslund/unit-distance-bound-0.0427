# An Exponent of 1.043 for the Unit Distance Problem: Lean formalization at exponent 1.04315

This source package accompanies the paper *An Exponent of 1.043 for the Unit Distance
Problem* ([docs/research-1.043171/main.pdf](docs/research-1.043171/main.pdf)), which proves the
exponent 1.043171 with a computer-assisted certificate. It states and supplies a Lean proof of
the following conditional theorem, at the exponent 1.04315: one explicit zeta inequality H_W on
a fixed number field of degree 8192 implies that there are finite sets `U_j` in the ordinary
Euclidean plane for which

```text
|U_j| → infinity,
(number of unordered unit-distance pairs in U_j) / |U_j|^(20863/20000) → infinity.
```

The exact exponent is `20863/20000 = 1.04315`. This is a sequence theorem; it asserts no bound
at every sufficiently large cardinality. **H_W remains unproved in Lean.**

This is version 2 of the package. Version 1 proved the exponent `10427/10000 = 1.0427` from a
different inequality H241, for the genus field of degree 512 (see *Version 1* below).

The independent statement is [ChallengeZeta241.lean](ChallengeZeta241.lean), and
[SolutionZeta241.lean](SolutionZeta241.lean) supplies the proof. The selected declaration is
`UnitDistanceSqrt241Submission.target_of_wide_zeta_bound`, with configuration
[comparator-zeta241.json](comparator-zeta241.json).

## The hypothesis

Let `B = ℚ(√241)` and let `E` be the field of degree 512 generated over the rationals by `√241`
and square roots of the eight elements of `B` listed in the Challenge's `radicandA` and
`radicandB` tables: a basis of the `{2,3,5}`-units of `B` modulo squares, so that `E` is the
maximal elementary abelian 2-extension of `B` unramified outside 2, 3, 5 and the infinite
places. The field `E_W = E(√β₁, √β₂, √β₃, √β₄)` adjoins square roots of four explicit elements
`β_i ∈ E` (the Challenge's `CanonicalWide.wideRadicand`); each `B(√a_i, √b_i, √β_i)` is a
dihedral extension of `B` of degree 8, and `E_W` has degree 8192 over the rationals. H_W is the
inequality

```text
log(Re ζ_{E_W}(1 + 1/4411))/8192
  + (1/4411) ((L − γ − log(4π))/4 − Re((ζ_{E_W}′/ζ_{E_W})(2))/8192) < 50969/1000000,
L = (9/4) log 2 + (1/2) log 3615.
```

[docs/ASSUMPTIONS.md](docs/ASSUMPTIONS.md) states it in full. The proof uses the ordinary
Euclidean metric on `ℂ` and counts unordered pairs by dividing the ordered count by two. The
intended permitted axioms are `propext`, `Quot.sound` and `Classical.choice`; H_W is an explicit
theorem parameter.

## The proof

The [development account](docs/sqrt241/SUBMISSION.md) describes the Lean proof: the infinite
pro-2 tower over `B` with Frobenius caps at both primes above 29 and at one prime above 41 (the
41-cap tower), its fields, which are Galois over `B` and over a fixed base field `M` but not
over the rationals, their local types and signature, the root-discriminant estimate, the field
`E_W` with its degree, its embedding in `M` and its local data, the passage from H_W to the
analytic ceiling, the finite certificates, the numerical margin and the planar transfer. The
[version 2 plan](docs/v2/PLAN.md) records why the Lean statement uses 1.04315: a single
abscissa, the pair profile of version 1 and the census of `M` up to norm 1000 reach it, while the
paper's exponent 1.043171 also uses a census of primes to `4·10¹³`, a signed kernel over 21
abscissae and general shell weights.

## External evidence for H_W

`docs/research-1.043171/certificates/dihedral/h_w_receipt.py` (output `h_w_receipt.json`) bounds
the left side of H_W by **0.0509171473**, which is `5.2·10⁻⁵` below the threshold `0.050969`.
The first term is the certified value of `log ζ_{E_W}(4412/4411)/8192`, from the factorization of
`ζ_{E_W}` into `ζ_E`, 448 Hecke L-functions of degree 4 and 128 of degree 8 and their certified
values (Sections 5 and 6 of the paper); the logarithmic derivative at 2 is bounded prime by prime
from lower bounds for the residue degrees in `E_W/B` up to norm `10⁶`, with an explicit tail.
These are certified numerical computations, not Lean proofs of H_W. Their replay needs the
research repository's `papers/0.043171/certificates` directory, of which this package carries
only the receipt and its program.

## Verification of version 2

In the research repository, on October 8, 2026, `lake build` of the default targets and
`lake build UnitDistance` succeeded, and `#print axioms` of the selected theorem, of the library
theorem `UnitDistance.Sqrt241.V2.target_of_wide_zeta_bound` and of the local data of `E_W`
reports only `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` and no
`native_decide` in the library; the audit of the full closure (59,452 declarations) reports the
same three axioms. The complete pinned Palomar pipeline (PalomarSubmission `65f0154`, profile
`palomar-standard-v1`, 4 CPUs and 16 GiB) passed locally on October 8, 2026 in 6,818 s, peak memory
15.2 GiB, on an export whose Lean files are byte-identical to this archive's (archive
`647219527ad6…`); it is a local reproduction, not an official Palomar report. An independent
fresh-context review of the statement, the field `E_W` and the match between H_W and its external
evidence found no error. This archive's [source snapshot](SOURCE_SNAPSHOT.json) and
[selection record](SELECTION.json) identify its exact bytes; any verification result applies only
to the archive it records.

## Version 1

Version 1 of the package proved the exponent 1.0427 from the inequality H241 for the genus field
`E`, with the selected declaration
`UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound`. Its candidate 4 passed the
complete pinned local Palomar pipeline under the 16-CPU/32-GiB profile on September 29, 2026
(`verification/sqrt241-full-20260929/README.md`), its later sources passed kernel replays within
4 CPUs and 16 GiB (`verification/sqrt241-bounded-20260929/README.md`), and its public package
passed Palomar's own verification and was registered as PALOMAR-2026-10-01-000018, version 1.
These records concern version 1 only: they do not verify the version 2 theorem. The
[earlier sqrt241 receipts](verification/sqrt241-20260929/README.md) record a fresh build and
per-module kernel checks of an earlier state of version 1. Version 1's endpoint modules were
removed from the present sources when the witness changed to the 41-cap tower; the present
sources keep its genus field, tower and analytic machinery. Imported `Lean.collectAxioms` and
`#print axioms` results on the pinned rc2 toolchain have the cached-summary limitation documented
in [the preserved assessment](verification/hosted-fit-20260929/requirements/axiom-audit-15226.md).

## The companion theorem

The package also contains the conditional theorem at exponent `2083647/2000000 = 1.0418235` of
the author's interim note (`docs/manuscript/`), a private note never released before its
inclusion in the public repository and superseded by the later papers:
[ChallengeZeta.lean](ChallengeZeta.lean), [SolutionZeta.lean](SolutionZeta.lean),
`comparator-zeta.json` and its metadata `formalization-zeta.yaml`. It assumes a different
inequality, for a fixed field of degree 524288. It is included for reference and is not the
Palomar selection: the default build targets are the 1.04315 theorem, `lake build SolutionZeta
ChallengeZeta` builds the earlier one, and `verification/ZetaAudit.lean` audits its axioms.
`README-zeta.md` was written as the README of that theorem's separately exported package, where
`formalization.yaml` meant the metadata shipped here as `formalization-zeta.yaml`.

## Research material

[docs/research-1.043171](docs/research-1.043171/README.md) carries the 1.043171 manuscript (LaTeX
sources and PDF), its research README and the H_W receipt.
[docs/quadratic-base-research](docs/quadratic-base-research/README.md) carries the 1.04273
manuscript of the tower over `ℚ(√241)` and its certificates, from which the genus field, the
tower and the version 1 hypothesis come, and [docs/manuscript](docs/manuscript/README.md) the
1.0418235 note. They are provenance copies with their original authorship and AI-production
disclosures: their external replay drivers expect the full research repository's `papers/`
layout, which this source-only Lean archive does not supply. Their local provenance and the
conclusions of the Lean theorems are recorded in [formalization.yaml](formalization.yaml).

The mathematical development, generators and documentation were produced with AI tools under
Eric Naslund's direction. Earlier reviews were automated reviews with their stated scopes. They
are not human peer review or owner proof verification. Publication, registration and editorial
acceptance are not claimed.

The formalization retains its Apache-2.0 [LICENSE](LICENSE), [NOTICE](NOTICE), and third-party
notices under `third-party/`. Embedded manuscript and research publication material retain their
supplied terms; this packaging introduces no new licence grant for those copies. Historical
documentation keeps its original target and dates. This README supplies the current local
verification scope for the selected sqrt241 source.
