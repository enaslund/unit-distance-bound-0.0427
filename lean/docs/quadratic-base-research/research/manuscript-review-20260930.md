# Review record of the manuscript, 2026-09-30

The manuscript [../main.tex](../main.tex) was drafted on September 30, 2026
from the research note [construction.md](construction.md), the supplementary
programs and the 1.0418235 manuscript. All referees below were AI agents
working in fresh contexts, without the authors' verdicts. They were asked to
find errors, to reconstruct the fragile steps, and to reproduce the essential
finite checks with their own code. Their scratch work is not in the
repository.

## Round 1: while drafting

Each drafting agent had its sections checked by a fresh-context referee
before handing them over.

* **Tower (Section 2).** No error. The referee recomputed every finite fact.
* **Kummer field and analytic ceiling (Sections 3 and 4).** No error
  affecting the ceiling. Some rounded constants from the research note were
  rounded in the unsafe direction; the manuscript uses safe roundings, for
  example the upper endpoint 0.08264460807138.
* **Geometry, profiles and certificate (Sections 5 to 8).** One sign error
  inside a proof step, whose lemma was unaffected, and several notation
  clashes. All fixed.

## Round 2: independent review of the whole draft

Four referees reviewed the integrated draft.

* **Sections 2 and 3.** No mathematical error. The referee reproduced the
  following with its own code:
  * the arithmetic of Q(√241);
  * the Hilbert-symbol tables and the local relator initials;
  * the ranks 21 and 142, the order 2⁴⁹ and the class of size 2¹⁵;
  * the exact value of P_B(34/117);
  * the dyadic field;
  * all 255 conductors, checked against PARI's `rnfconductor`.
* **Section 4.** No error. The referee reproduced every number
  independently, including:
  * all 255 L-values, with PARI;
  * the census of 78,616 primes;
  * R and κ_∞;
  * the final arithmetic, with every rounding in the safe direction.

  It checked the Tsfasman–Vlăduţ normalization against the source.
* **Sections 5 to 8.** No error.
  * Proposition geo:mass was checked in PARI on three explicit fields, two
    of them with nontrivial capitulation.
  * Every certified number, including M_*(θ_*), was reproduced
    independently in Arb.
* **Exposition.** No mathematical problem. It recommended a major revision
  of the presentation:
  * a statement of where the code is;
  * an even-handed status for earlier claims, including the June 9, 2026
    correction to the 1.0358 bound;
  * a responsibility sentence in the AI Methodology paragraph;
  * a notation pass;
  * removal of research-note material.

## Revision

* **Notation.** The complex conjugations are now ι₁, ι₂. The restricted
  square is v^{[2]}. E is now called the Kummer field. The profile
  subscripts are ℝ and ℂ. Covolumes are written covol, the norm-one units
  𝒪_K^1, and the cost functions ψ.
* **Theorems.** Theorems and equations share one counter.
* **Tower section.**
  * The dyadic lemma is stated for an explicit triple of generators.
  * A hand proof replaces the program of the earlier paper for the facts
    about F₂[D]; the new program `dyadic241.py` confirms them.
  * A new Lemma tw:local-forms derives the redundancy of the first dyadic
    relation from Hilbert reciprocity.
* **Computations.** Every computation cited in the text is now done by a
  shipped program:
  * the new programs `check255.gp`, `lvalues255.gp` and `dyadic241.py`;
  * `geom241.py`, which prints every enclosure that Section 8 states;
  * `shells241.py`, which reproduces the shipped weight files byte for byte.
* **Introduction.**
  * Each bound in Table 1 states its kind of source.
  * The 1.0358 row reads 1.0357, with the history of the correction.
  * The trade-off of the base field is stated precisely.
  * A new subsection gives the location of the programs and the software
    versions.
* **Title.** A referee found the working title *A Lower Exponent of 1.04273
  for Planar Unit Distances* ambiguous; at the author's request the title is
  *An Exponent of 1.04273 for the Unit Distance Problem*.

## Round 3: the new tower arguments

A fresh referee checked Lemma tw:local-forms and the hand proof in Lemma
tw:local-fox. No error. It reproduced:

* the order |D| = 32, by coset enumeration;
* the Jennings filtration and the graded injectivity;
* the eight local forms, their sum and their ranks;
* the value of P_B.

It also found that without the reciprocity saving s_D the series is positive
on (0, 1), so that saving is essential. Its one-line clarifications were
added.

## Replay

The full replay `certificates/reproduce241.py`, extended with the three new
checks, passed on September 30, 2026 in 488 s. The recorded margin after
concentration, 0.00017672603353, is unchanged.

## Scope

These reviews are by AI agents; the manuscript has not been peer reviewed.
The referees did not audit PARI, Arb or mpmath themselves. Their independent
recomputations, in PARI, in Arb and at floating-point level, agree with the
certified values.
