# Historical manuscript: delta 0.0358324

[PDF](main.pdf) · [TeX](main.tex) · [Bibliography](references.bib)

*An Improved Explicit Lower Bound for the Unit Distance Problem*, Eric Naslund.
This manuscript is a formal write-up of the construction in the author's
MathOverflow answer. It records the exponent **1.0358324**, the largest
exponent claimed before the paper
[*An Exponent of 1.04273 for the Unit Distance Problem*](../0.04273/README.md).
The [1.0418235 note](../0.0418235/README.md) in between was an interim private
note, never released before this repository.
The old paper counts ordered pairs; the current paper counts unordered pairs.
This constant factor does not change the exponents.

The PDF, TeX chapters, appendices and bibliography are copied byte for byte
from the research repository. On September 30, 2026 the author line gained an
asterisk and an AI Methodology statement was added after the abstract: the
research was carried out with GPT 5.5 Pro, and the paper was written with
Codex 5.6 Sol, under the author's supervision; the author has read all of the
arguments carefully. On October 1, 2026 the author added to that statement that
this paper is the more carefully written version of the author's earlier
MathOverflow answer. The mathematics is unchanged, and its constants may differ
slightly from those posted in the answer. The [provenance manifest](../../provenance/papers.json)
records their identities.

Build with a standard TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The preserved `main.tex` includes its bibliography directly.
