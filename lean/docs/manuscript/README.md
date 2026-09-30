# A lower exponent of 1.0418235 for planar unit distances

[Read the manuscript](main.pdf) · [LaTeX source](main.tex) · [Bibliography](references.bib)

The theorem constructs finite planar sets (U_j), with (|U_j|\to\infty),
such that (u(U_j)/|U_j|^{1.0418235}\to\infty), counting unordered pairs.
Consequently (u(n)\ge n^{1.0418235}) for arbitrarily large integers (n).

This manuscript brings the complete construction-specific proof into one
document. It uses standard results from the cited literature and a finite
computer-assisted certificate. Earlier repository manuscripts are not
mathematical dependencies of the text.

The [introduction](sections/introduction.tex) opens with a plain outline:
the exponent is set by the gain from equal-norm choices at split primes,
the loss in selecting a common ideal class (governed by the root
discriminant and the relative zeta value), and the geometric window. It
compares the method separately with Sawin and the
[historical 0.0358324 manuscript](../0.0358324/README.md),
and distinguishes that manuscript from the MathOverflow revision history.
It explains mixed signature, norm-one unit averaging, local relation modules,
joint Euler information and the geometric profiles, and its §1.6 matches
each change with the term of Sawin's criterion that it improves. A
[research-development record](evidence/research-development.md) maps the
earlier branch results to their sources and evidence status.

| Part | Contents |
| --- | --- |
| [Introduction](sections/introduction.tex) | Outline, arithmetic mechanism, prior work, key changes, term-by-term comparison with Sawin's criterion |
| [Tower](sections/tower.tex) | Complete global presentation, prescribed dyadic field, finite quotient, filtered Fox calculation, infinite field family |
| [Retained field](sections/retained-field.tex) | Actual Kummer fields, seven-dimensional central space, representation and Hecke data |
| [Analysis](sections/analytic.tex) | Functional equations, coefficient algorithms and tails, complete Euler table, disjoint prime corrections, unconditional transfer to one |
| [Geometry](sections/geometry.tex) | Unit mass and capitulation cancellation, dual-lattice counting, common averaging and energy window |
| [Finite places](sections/finite-windows.tex) | Exact shell kernels, period-based counting, weighted class selection and geometric criterion |
| [Profiles](sections/profiles.tex) | Gaussian and correlated Bernstein profiles, mass, overlap and Fourier bounds |
| [Final certificate](sections/certificate.tex) | All shell weights, exact witness, directed enclosures and completion of the theorem |

## Build and check

Build the PDF from this directory with a standard TeX installation:

```sh
make paper
```

The numerical driver needs Python 3.11 or later and the packages in
`requirements.txt`. Analytic replay also requires PARI/GP. Regenerating
moment files requires a C++17 compiler and GMP development headers and
libraries. The recorded environment uses python-flint 0.9.0, FLINT 3.6.0,
mpmath 1.3.0, and PARI/GP 2.17.2.

```sh
python3 certificates/reproduce.py --check
python3 certificates/reproduce.py --output /tmp/unit-distance-geometry.json
python3 certificates/reproduce.py --analytic --output /tmp/unit-distance-analytic.json
python3 certificates/reproduce.py --moments --workers 4 --output /tmp/unit-distance-moments.json
```

- `--check` checks file identity and the complete transitive manuscript
  dependency list. It does not verify mathematical truth.
- Default replay independently checks the printed tower matrices, norm
  identities, field masks, integral bases and pure projector, checks
  the direct analytic table against exact stored endpoints, and freshly
  evaluates the final geometric witness.
- `--analytic` additionally reevaluates all Hecke factors, checks an
  independent census prefix, recertifies the full finite prime correction,
  and reassembles the Euler ceiling.
- `--moments` includes analytic replay and additionally recompiles all five
  newest producers and regenerates all 64 sector moment files: 103,012 bins
  and 5,515,960 integer moments.

The `--analytic` replay's embedded receipt carries an `exponent` field
reading `1.0418123`, because the analytic driver bundles the pre-retuning
geometry witness; the consolidated receipt's top-level exponent is
`1.0418235`. A fresh `--analytic` replay on September 22, 2026 (253 s,
recorded in the Lean project's `verification/external-zeta-20260922/`)
reproduced the ceiling enclosure, upper endpoint `0.0421618189394842`.
The manuscript's revision date is September 27, 2026.

The [September 27 editorial checks](evidence/publication-revision-20260927.md)
include a clean PDF build and a fresh default certificate replay. The replay
preserves the positive geometric margin. Its analytic inputs were unchanged,
and the analytic-factor evaluations were not rerun for this revision.

The complete prime sieve through (10^{12}), earlier moment tables and
actual-field arithmetic receipts remain supplied finite data in these
commands. Their source code and recorded arithmetic checks are included.
The extended modes do not imply that every historical calculation has
been rerun. `CXX`, `CPPFLAGS` and `MOMENT_LDFLAGS` can configure compilation.

## Portable supplementary data and integrity

The entire folder can be copied out of this repository. The compressed
[source/data archive](certificates/data-manifest.json) contains every original
sealed arithmetic input, together with the previously omitted mathematical
TeX and Markdown sources for provenance. The member-by-member
[data manifest](certificates/data-manifest.json) verifies each extracted
file. All computation occurs in a private temporary copy; the archive and
published inputs remain unchanged.

The archive is stored as `certificates/data.tar.gz.part00`, `part01` and
`part02`, each at most 48 MiB. Replay automatically verifies and joins these
parts in temporary storage, recovering the original archive byte for byte.
A regular Git checkout contains everything needed; Git LFS is not required.

The [package manifest](certificates/manifest.json) includes every nested
TeX input and bibliography file, the finished PDF, the verifier and the
supplementary data. Its checker rejects changed proof files, omitted proof
hashes and newly introduced proof dependencies. Regression checks for
these cases are recorded in [the evidence](evidence/manifest-regression.json).
This closes the proof-provenance gap found in the earlier audit for the
new consolidated package. The original manuscripts and their old manifests
remain historical records.

The mathematical proof and exact error estimates justify the inequalities.
Hash checks establish which files were checked; they are not proof checks.
The [bibliography verification record](evidence/bibliography-check.md)
identifies the literature sources used to prepare the references.

## Revision note

- September 30, 2026 (introduction): added a plain outline of the method
  after Theorem 1.1 and a subsection, §1.6, that writes Sawin's criterion
  in the form of inequality (1.1) and matches each change with the term it
  improves. It compares the towers (root discriminant about 583 here,
  about 1.6·10^8 in Sawin's example) and the zeta terms (C against
  1 + log log λ), and explains why mixed signature helps: averaging over
  the norm-one units makes their regulator cancel in the class-number
  formula, so mixed signature costs only a factor π per complex place,
  which the coupled profile more than repays. §1.2 now names Sawin's
  factor 2^d for units consistently. The theorem, proofs, witness and
  certificate are unchanged.

- September 30, 2026: removed the displayed replay command and command-line
  options from the certificate section. The section now describes the three
  replay levels in prose, and this README gives the commands. The theorem,
  proofs, witness and certificate are unchanged.

- September 27, 2026: revised the abstract, introduction and proof exposition
  using the author's naslund-math-writing guide. Expanded the bibliography
  with primary-source checks and a documented Palomar search. The introduction
  distinguishes the old 0.0358324 manuscript, the public MathOverflow history,
  and the present construction. It also states the conditional scope of the
  separate Lean development. The theorem and numerical witness are unchanged.
  The previous manuscript and PDF
  (`archive/manuscript-versions/unit-distance-1.0418235-before-publication-rewrite-20260927/`)
  and original package manifest are preserved in the repository history at
  the tag `pre-merge-2026-09-29`. New checks and their limits
  are recorded in the [revision account](evidence/publication-revision-20260927.md).

- September 22, 2026: corrected the MathOverflow citation (its June 9,
  2026 change log states the corrected best bound as delta > 0.0357),
  added the Emmerich citation (arXiv:2606.03419), and added the fixed-field
  remark (Remark `an:fixed-field-form`) after equation `an:full-euler` in
  the analytic section; no numerical input, proof, or certificate data
  changed. These edits were made by Claude Fable 5.1 (Anthropic) through
  Claude Code, under the owner's direction.
