# An Exponent of 1.04273 for the Unit Distance Problem

This repository holds the paper *An Exponent of 1.04273 for the Unit Distance Problem* by Eric Naslund, its two
predecessors, and a Lean formalization. The papers give lower bounds for the
number of unit-distance pairs among points in the Euclidean plane. Each
result constructs finite sets `U_j`
with `|U_j| → ∞` and `u(U_j)/|U_j|^(1+δ) → ∞`, where `u` counts unordered pairs
at distance one; equivalently, `u(n) ≥ n^(1+δ)` for arbitrarily large `n`. No
bound is asserted for every sufficiently large `n`.

| Result | Source | Status |
| --- | --- | --- |
| **Exponent 1.04273** (main result): *An Exponent of 1.04273 for the Unit Distance Problem* | [PDF](papers/0.04273/main.pdf) · [sources and certificate](papers/0.04273/README.md) | Manuscript of September 30, 2026: the tower of the 1.0418235 construction built over the real quadratic field ℚ(√241), with a computer-assisted certificate and a finite replay. Independent AI referee reviews found no mathematical error; it has not been peer reviewed. |
| Exponent 1.0418235 | [PDF](papers/0.0418235/main.pdf) · [sources and certificate](papers/0.0418235/README.md) | Interim private note, never released before this repository: a lesser result, with a computer-assisted certificate, whose methods the main paper incorporates. Kept for the record. |
| Exponent 1.0358324 | [PDF](papers/0.0358324/main.pdf) · [sources](papers/0.0358324/README.md) | Formal write-up of the author's MathOverflow answer; the largest exponent claimed before the main paper. |

## Checks

```sh
python3 papers/0.0358324/certificates/verify_t38_certificate.py  # historical T38 certificate
python3 papers/0.0418235/certificates/reproduce.py --check        # identity of the sealed package
python3 papers/0.0418235/certificates/reproduce.py                # finite replay (--analytic also re-evaluates the analytic factors)
cd papers/0.04273/certificates && python3 reproduce241.py         # finite replay at delta = 0.04273
```

The 0.04273 replay reuses certified modules from the 0.0418235 data archive;
it needs PARI/GP and the Python packages in
[papers/0.04273/requirements.txt](papers/0.04273/requirements.txt).

## Lean formalization

[`lean/`](lean/README.md) is a Lean 4 project with Mathlib. It proves the
planar sequence theorem at exponent **10427/10000 = 1.0427**, conditional on
one explicit numerical inequality H241 for the Dedekind zeta function of a
fixed degree-512 number field over ℚ(√241). The proof uses only Lean's
standard axioms `propext`, `Quot.sound` and `Classical.choice`. **H241 is not
proved in Lean**; outside Lean, the certificate of the 1.04273 paper bounds
its left side by 0.0848335 against the ceiling 0.0852. The statement is
[`lean/ChallengeZeta241.lean`](lean/ChallengeZeta241.lean) and the proof
[`lean/SolutionZeta241.lean`](lean/SolutionZeta241.lean).

The project also contains the conditional theorem at exponent 1.0418235,
the formalization of the interim note in `papers/0.0418235`, for reference.

```sh
cd lean
lake build                          # the 1.0427 theorem
lake build SolutionZeta ChallengeZeta  # the 1.0418235 theorem
```

This repository is prepared as the Palomar submission of the 1.0427 theorem
(project `lean`, metadata `lean/formalization.yaml`, comparator
`lean/comparator-zeta241.json`), and Palomar's own preflight check passes on
it; no submission has been made yet.
[docs/FORMALIZATION_STATUS.md](docs/FORMALIZATION_STATUS.md) records what has
been verified and what remains, and the manual workflow
[`palomar-preflight.yml`](.github/workflows/palomar-preflight.yml) runs
Palomar's pinned verifier on this repository's exact commit.

## Authorship, licensing and provenance

The papers and the formalization were produced with AI
tools under Eric Naslund's direction; each paper carries its own disclosure,
and [`lean/NOTICE`](lean/NOTICE) credits the formalization's contributors and
vendored sources. The root [LICENSE](LICENSE) (Apache-2.0) covers the
formalization; the papers keep their own terms
([details](docs/LICENSING_AND_ATTRIBUTION.md)). The
[provenance manifest](provenance/papers.json) records the source and hash of
every copied paper file, and [`provenance/lean-release.json`](provenance/lean-release.json)
identifies the Lean source archive.
