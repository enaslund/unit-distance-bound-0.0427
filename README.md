# An Exponent of 1.043 for the Unit Distance Problem

This repository holds the paper *An Exponent of 1.043 for the Unit Distance Problem* by Eric
Naslund, its predecessors, their computer-assisted certificates, and a Lean formalization. The
papers give lower bounds for the number of unit-distance pairs among points in the Euclidean plane.
Each result constructs finite sets `U_j` with `|U_j| → ∞` and `u(U_j)/|U_j|^(1+δ) → ∞`, where `u`
counts unordered pairs at distance one; equivalently, `u(n) ≥ n^(1+δ)` for arbitrarily large `n`.
No bound is asserted for every sufficiently large `n`.

| Result | Source | Status |
| --- | --- | --- |
| **Exponent 1.043171** (main result): *An Exponent of 1.043 for the Unit Distance Problem* | [PDF](papers/0.043171/main.pdf) · [sources](papers/0.043171/main.tex) · [certificates and research record](papers/0.043171/README.md) | Manuscript of October 8, 2026: the tower over ℚ(√241) of the 1.04273 paper with one Frobenius cap moved from the prime 7 to a prime above 41, and the bound for the relative zeta value lowered through the dihedral quotients of the tower group (a census of primes, a field of degree 8192 whose zeta function is a product of 576 new L-functions of degrees 4 and 8, and a signed kernel), with general shell weights. Computer-assisted certificate with a finite replay. Fresh-context AI reviews of its parts and of the manuscript found no error affecting the theorem; it has not been peer reviewed. |
| Exponent 1.042901 | [research record](papers/0.042901/README.md) | The 41-cap variation of the 1.04273 construction (October 3, 2026), the base of the main result; not a separate manuscript. |
| Exponent 1.04273: *An Exponent of 1.04273 for the Unit Distance Problem* | [PDF](papers/0.04273/main.pdf) · [sources and certificate](papers/0.04273/README.md) | Manuscript of September 30, 2026 ([hexagon:2610.00016v1](https://hexagonmath.org/2610.00016v1)): the tower over the real quadratic field ℚ(√241), with a computer-assisted certificate and a finite replay; certificates corrected on October 2, 2026. |
| Exponent 1.0418235 | [PDF](papers/0.0418235/main.pdf) · [sources and certificate](papers/0.0418235/README.md) | Interim private note, never released before this repository: a lesser result whose methods the later papers incorporate. Kept for the record. |
| Exponent 1.0358324 | [PDF](papers/0.0358324/main.pdf) · [sources](papers/0.0358324/README.md) | Formal write-up of the author's MathOverflow answer. |

## Checks

```sh
python3 papers/0.0358324/certificates/verify_t38_certificate.py     # historical T38 certificate
python3 papers/0.0418235/certificates/reproduce.py --check           # identity of the sealed package
cd papers/0.04273/certificates && python3 reproduce241.py            # finite replay at delta = 0.04273
cd papers/0.042901/certificates && python3 reproduce41.py            # finite replay at delta = 0.042901
cd papers/0.043171/certificates/dihedral && python3 reproduce_w3.py witness_0.043171.json
                                                                     # finite replay of the main result
```

The replays need PARI/GP and the Python packages of
[papers/0.043171/requirements.txt](papers/0.043171/requirements.txt) (mpmath, python-flint, numpy,
scipy); the replay of the main result takes several hours and needs gcc with OpenMP and an x86-64
processor with the AVX-512 IFMA instructions for its census programs. The 0.043171 programs import
the programs of `papers/0.04273/certificates` and `papers/0.042901/certificates` from this
repository's layout, and some routines of the 0.0418235 supplementary archive, whose members are
checked against their SHA-256 hashes when it is unpacked.

## Lean formalization

[`lean/`](lean/README.md) is a Lean 4 project with Mathlib. It proves the planar sequence theorem
at exponent **20863/20000 = 1.04315** for the construction of the main paper, conditional on one
explicit numerical inequality **H_W** for the Dedekind zeta function of a fixed number field `E_W`
of degree 8192 (the field `E_{W''}` of the paper). The proof uses only Lean's standard axioms
`propext`, `Quot.sound` and `Classical.choice`. **H_W is not proved in Lean**; outside Lean,
[`papers/0.043171/certificates/dihedral/h_w_receipt.py`](papers/0.043171/certificates/dihedral/h_w_receipt.py)
bounds its left side by 0.0509171 against the threshold 0.050969. The statement is
[`lean/ChallengeZeta241.lean`](lean/ChallengeZeta241.lean) and the proof
[`lean/SolutionZeta241.lean`](lean/SolutionZeta241.lean);
[`lean/docs/ASSUMPTIONS.md`](lean/docs/ASSUMPTIONS.md) displays H_W.

```sh
cd lean
lake build                             # the 1.04315 theorem
lake build SolutionZeta ChallengeZeta  # the companion theorem at 1.0418235
```

[docs/FORMALIZATION_STATUS.md](docs/FORMALIZATION_STATUS.md) records what has been verified and
what remains. The manual workflow
[`palomar-preflight.yml`](.github/workflows/palomar-preflight.yml) runs Palomar's pinned verifier on
this repository's exact commit.

**Palomar registry.** Version 1 of this formalization, at exponent 1.0427 from an inequality on a
degree-512 field, is registered as
[PALOMAR-2026-10-01-000018, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-01-000018&version=1),
from commit `e0ac836` of this repository. The 1.04315 theorem replaces it in `lean/` and is
prepared for a new submission (project `lean`, metadata `lean/formalization.yaml`, comparator
`lean/comparator-zeta241.json`); the registered version 1 remains at commit `e0ac836`.

## Research notes

[`research/`](research/) holds two notes cited by the papers' records: the design search of
October 2026 that led to the 41-cap and dihedral refinements, and a conditional route to 1.043172
through a larger involution class, found in an agent run and not used by the main result.

## Authorship, licensing and provenance

The papers and the formalization were produced with AI tools under Eric Naslund's direction; each
paper carries its own disclosure, and [`lean/NOTICE`](lean/NOTICE) credits the formalization's
contributors and vendored sources. The root [LICENSE](LICENSE) (Apache-2.0) covers the
formalization; the papers keep their own terms ([details](docs/LICENSING_AND_ATTRIBUTION.md)). The
[provenance manifest](provenance/papers.json) records the research source and hash of every copied
paper and research file, and [`provenance/lean-release.json`](provenance/lean-release.json)
identifies the Lean source archive.
