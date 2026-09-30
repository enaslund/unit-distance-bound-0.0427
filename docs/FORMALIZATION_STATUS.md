# Formalization status

[`lean/`](../lean/README.md) is a Lean 4 project (Lean `v4.35.0-rc2`, Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`). Its sources are the export of
research commit `c459e36b` of `enaslund/unit-distance-bound`, copied unchanged;
[`provenance/lean-release.json`](../provenance/lean-release.json) records the
archive identity.

## The selected theorem: exponent 1.0427

`UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound` is stated
independently in [`lean/ChallengeZeta241.lean`](../lean/ChallengeZeta241.lean)
(135 lines, importing only Mathlib) and proved in
[`lean/SolutionZeta241.lean`](../lean/SolutionZeta241.lean). It gives finite
sets `U_j` in the Euclidean plane with `|U_j| → ∞` and (number of unordered
unit-distance pairs)`/|U_j|^(10427/10000) → ∞`, assuming one explicit
inequality H241 for the Dedekind zeta function of the degree-512 field
generated over `ℚ` by `√241` and square roots of eight explicit elements of
`ℚ(√241)`. The [package README](../lean/README.md) displays H241.

- **H241 is not proved in Lean.** Outside Lean,
  [`papers/0.04273/certificates/h241_receipt.py`](../papers/0.04273/certificates/h241_receipt.py)
  bounds its left side by 0.0848335 against the ceiling 0.0852, and an
  independent recomputation with PARI's Hecke L-functions agrees.
- Apart from H241, the proof uses only `propext`, `Quot.sound` and
  `Classical.choice`; there is no `sorry` and no `native_decide`.
- The research result claims the exponent 1.04273; the Lean statement uses
  1.0427 to leave room for exact rational enclosures.
- The Palomar selection is project `lean`, metadata `lean/formalization.yaml`
  and comparator `lean/comparator-zeta241.json`.

The theorem's import closure has 2,288 modules and about 653,000 lines of
Lean: 42,000 in the new development over `ℚ(√241)`, 86,000 shared with the
earlier development over `ℚ`, and 525,000 in vendored ports (Yamaguchi's
class-field-theory library, AINTLIB, Hadamard products, Poisson summation),
credited in [`lean/NOTICE`](../lean/NOTICE).

## The companion theorem: exponent 1.0418235

The package also contains the earlier conditional theorem at exponent
`2083647/2000000`: [`lean/ChallengeZeta.lean`](../lean/ChallengeZeta.lean),
[`lean/SolutionZeta.lean`](../lean/SolutionZeta.lean),
`lean/comparator-zeta.json` and `lean/formalization-zeta.yaml`, the
formalization of [papers/0.0418235](../papers/0.0418235/README.md). It assumes
a different inequality, for a fixed field of degree 524288, and 2,048 of its
2,162 modules are shared with the selected theorem. It is included for
reference and is not the Palomar selection; `lake build SolutionZeta
ChallengeZeta` builds it.

## Verification

| Check | Version checked | Result |
| --- | --- | --- |
| Complete pinned Palomar pipeline under the 16-CPU/32-GiB profile: fresh build, protected exports, statement and definition comparison, axiom checks, con-ron, NanoDa, Lean kernel | Candidate 4 (research commit `697c3cd7`) | Passed on September 29, 2026 in 7,876.6 s ([record](../lean/verification/sqrt241-full-20260929/README.md)) |
| con-ron, NanoDa and Lean kernel replays of the Solution export, each within 4 CPUs and 16 GiB | The selected theorem's declarations in this package | Passed; memory peaks 10.3, 10.4 and 8.0 GiB ([record](../lean/verification/sqrt241-bounded-20260929/README.md)) |
| Axiom audit of the 57,394 declarations in the selected closure and the 32 submission declarations | This package | Only the three standard axioms |
| Packaging gate: deterministic re-export and the metadata contract of PalomarSubmission `65f0154` | This package's archive | Passed ([report](../provenance/lean-checks/gate.json)) |
| Fresh build from source, with the axiom audit | The first export of this package, with byte-identical Lean files | Passed: 6,960 build jobs in 62 minutes; the audit of 52,186 project and 32 submission declarations reports only the three standard axioms ([report](../provenance/lean-checks/candidate1-fresh-build.json)) |
| Complete pinned pipeline on this repository's exact commit | This repository | Not yet run |

The sources differ from candidate 4 only inside proofs: certificate splits
that fit con-ron within 16 GiB. Compared declaration by declaration, no
theorem statement or definition changed. The companion theorem passed the
complete pipeline under both Palomar profiles for its own earlier package,
and its Lean sources are unchanged since.

## Next steps

1. Run the manual workflow
   [`.github/workflows/palomar-preflight.yml`](../.github/workflows/palomar-preflight.yml)
   on this repository's exact commit. It runs Palomar's pinned verifier on a
   GitHub-hosted runner under the profile `palomar-standard-v1`.
2. Submit the commit to the Palomar registry. No submission has been made.
