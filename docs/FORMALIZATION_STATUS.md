# Formalization status

[`lean/`](../lean/README.md) is a Lean 4 project (Lean `v4.35.0-rc2`, Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`). Its sources are the export of research commit
`2acbeccb` of `enaslund/unit-distance-bound`, copied unchanged;
[`provenance/lean-release.json`](../provenance/lean-release.json) records the archive identity. It
formalizes the construction of the paper *An Exponent of 1.043 for the Unit Distance Problem* at
the exponent 1.04315, conditional on one zeta inequality.

## The selected theorem: exponent 1.04315

`UnitDistanceSqrt241Submission.target_of_wide_zeta_bound` is stated independently in
[`lean/ChallengeZeta241.lean`](../lean/ChallengeZeta241.lean) (importing only Mathlib) and proved in
[`lean/SolutionZeta241.lean`](../lean/SolutionZeta241.lean). It gives finite sets `U_j` in the
Euclidean plane with `|U_j| → ∞` and (number of unordered unit-distance pairs)`/|U_j|^(20863/20000)
→ ∞`, assuming one explicit inequality **H_W** for the Dedekind zeta function of the field `E_W`
of degree 8192: the genus field `E` of `B = ℚ(√241)` (degree 512) adjoined square roots of four
explicit elements `β_i ∈ E`, which define dihedral extensions of `B` of degree 8.
[`lean/docs/ASSUMPTIONS.md`](../lean/docs/ASSUMPTIONS.md) displays H_W:

```text
log(Re ζ_{E_W}(1 + 1/4411))/8192
  + (1/4411) ((ℓ − γ − log(4π))/4 − Re(logDeriv ζ_{E_W} 2)/8192) < 50969/1000000,
ℓ = (9/4) log 2 + (1/2) log 3615.
```

- **H_W is not proved in Lean.** Outside Lean,
  [`papers/0.043171/certificates/dihedral/h_w_receipt.py`](../papers/0.043171/certificates/dihedral/h_w_receipt.py)
  bounds its left side by 0.0509171473 against the threshold 0.050969, from the certified L-values
  of the paper (Sections 5 and 6) and an explicit bound for the logarithmic derivative at 2.
- Apart from H_W, the proof uses only `propext`, `Quot.sound` and `Classical.choice`; there is no
  `sorry` and no `native_decide`.
- What Lean proves: the infinite 41-cap tower over `B` (presentation, Golod–Shafarevich
  inequality), its fields with their local types and signature, the fixed base `M` and its root
  discriminant, the field `E_W` with its degree, its embedding in `M` and its local data, the
  passage from H_W to the analytic ceiling, the numerical margin and the planar construction.
- The paper proves the exponent 1.043171 with a computer-assisted certificate; the Lean statement
  uses 1.04315, which a single abscissa, the census of the fixed base up to norm 1000 and the
  pair profile of the earlier formalization reach. The full certificate of the paper (the census
  to 4·10¹³, the signed kernel and general shell weights) is not formalized.
- An independent fresh-context review of the statement, the field `E_W` and the match between
  H_W and its evidence found no error
  ([report](../provenance/lean-checks/v2-statement-review-20261008.md)).
- The Palomar selection is project `lean`, metadata `lean/formalization.yaml` and comparator
  `lean/comparator-zeta241.json`.

## The companion theorem: exponent 1.0418235

The package also contains the conditional theorem at exponent `2083647/2000000` of the author's
interim note: [`lean/ChallengeZeta.lean`](../lean/ChallengeZeta.lean),
[`lean/SolutionZeta.lean`](../lean/SolutionZeta.lean), `lean/comparator-zeta.json` and
`lean/formalization-zeta.yaml`, the formalization of [papers/0.0418235](../papers/0.0418235/README.md).
It assumes a different inequality, for a fixed field of degree 524288. It is included for reference
and is not the Palomar selection; `lake build SolutionZeta ChallengeZeta` builds it.

## Verification

| Check | Version checked | Result |
| --- | --- | --- |
| `lake build` (default targets) and `lake build UnitDistance` | The version 2 sources | Passed |
| Axiom audit of the 59,452 declarations in the selected closure and the 55 submission declarations | The version 2 sources | Only `propext`, `Classical.choice`, `Quot.sound` ([record](../provenance/lean-checks/v2-axiom-audit-README.md)) |
| Packaging gate: deterministic re-export and the metadata contract of PalomarSubmission `65f0154` | This package's archive | Passed ([report](../provenance/lean-checks/v2-gate.json)) |
| Complete pinned Palomar pipeline, profile `palomar-standard-v1` (4 CPUs, 16 GiB), on a local trusted setup: fresh build, protected export, statement and definition comparison, axiom checks, con-ron and NanoDa | An earlier export with byte-identical Lean files (archive `64721952…`) | Passed in 6,818 s, peak memory 15.2 GiB ([record](../provenance/lean-checks/v2-local-standard-README.md), [report](../provenance/lean-checks/v2-local-standard-local-execution.json)) |
| Palomar's own preflight workflow ([`palomar-preflight.yml`](../.github/workflows/palomar-preflight.yml)) on this repository's commit | — | Not yet run on the version 2 package |

## Registration

Version 1 of this formalization, the theorem
`UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound` at exponent 1.0427 from an
inequality H241 on the degree-512 genus field, is registered as
[PALOMAR-2026-10-01-000018, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-01-000018&version=1),
from commit `e0ac836` of this repository; Palomar keeps a preserved copy of that commit. The 1.04315
theorem in the current `lean/` is prepared for submission with the same project, metadata and
comparator paths. Because it is a new theorem with a new hypothesis, Palomar may register it as a
new result rather than as a new version of that entry. No submission of it has been made yet.
