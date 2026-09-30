# Current manuscript: delta 0.0418235

[PDF](main.pdf) · [TeX](main.tex) · [Bibliography](references.bib)

*A Lower Exponent of 1.0418235 for Planar Unit Distances*, Eric Naslund.
This is the September 27, 2026 revision, with 41 cited references and a
separate introduction comparing Sawin's method and the historical 0.0358324
manuscript, revised on September 30, 2026. The introduction now opens with a
plain outline of the method, and its §1.6 compares the construction with
Sawin's criterion term by term, including why mixed signature helps. The
certificate section's replay paragraph was rewritten in prose, without the
displayed command. The theorem, proofs, witness and certificate are
unchanged. All TeX, PDF and numerical inputs are byte-identical copies from
the research repository. The distribution README and package identity
manifest are specific to this public layout.

## Build

```sh
make paper
```

Equivalently, run pdflatex, BibTeX, then pdflatex twice on `main.tex`.
The [recorded build](evidence/build-check-20260927.json) found no unresolved
references or overflowing boxes.

## Numerical certificate

Python 3.11 or later and the packages in [requirements.txt](requirements.txt)
are required for numerical replay. Analytic replay also needs PARI/GP.
Moment regeneration additionally requires a C++17 compiler and GMP headers.

```sh
python3 certificates/reproduce.py --check
python3 certificates/reproduce.py --output /tmp/unit-distance-geometry.json
python3 certificates/reproduce.py --analytic --output /tmp/unit-distance-analytic.json
python3 certificates/reproduce.py --moments --workers 4 --output /tmp/unit-distance-moments.json
```

The identity check covers the complete TeX dependency closure and sealed
package files. Default replay checks the tower, retained-field data and
printed analytic table and freshly evaluates the final geometric witness.
The [September 27 replay](evidence/replay-20260927.json) passed with a positive
margin after concentration exceeding 0.00000533204359816794.

`--analytic` reevaluates the Hecke factors and finite-prime correction using
the stored data. Its embedded older exponent field is 1.0418123, while the
consolidated replay's top-level exponent and current witness are 1.0418235.
`--moments` additionally regenerates the newest 64 sector moment files.
Neither mode regenerates every older table or the complete prime sieve
through 10^12. Hash checks establish data identity, not mathematical truth.

The three `certificates/data.tar.gz.part*` files contain the portable
supplementary source and data archive. The replay verifies and joins them in
temporary storage. Each part is smaller than GitHub's file-size limit.
The assembled duplicate archive and generated build products are omitted.

The separate [formalization release status](../../docs/FORMALIZATION_STATUS.md)
explains the remaining Lean hypothesis and release checks.
