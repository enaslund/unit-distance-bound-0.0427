# Readability revision of the manuscript, 2026-10-01

At the author's request, the manuscript [../main.tex](../main.tex) was revised
for a human reader. The aims were:

- every term and symbol is defined before it is used;
- main and intermediate results are stated as numbered Theorems,
  Propositions, Lemmas, Corollaries and Definitions;
- no research-note vocabulary is left undefined.

The mathematics, the constants and the supplementary programs are unchanged.
All referees and editors below were AI agents. The referees worked in fresh
contexts, without the editors' verdicts.

## Process

1. **Audit.** Three referees read Sections 1–3, 4–5 and 6–8 as first-time
   readers. They reported terms used before their definition, key facts left in
   prose, overloaded notation and other obstacles. No finding was of the
   highest severity, "a reader would be stuck".
2. **Conventions.** The coordinator fixed one terminology for the whole paper:
   - *type* and *absolute type*: Definition 2.41;
   - *uniform local types* and the selected primes: Definition 5.4;
   - θ_*: Theorem 2.42;
   - the root discriminant: Definition 2.40;
   - the family 𝒦: Definition 4.1;
   - the *margin*;
   - *window* and *profiles*: Definitions 5.11 and 5.22, which name the masses
     A, the overlaps I and the functionals J;
   - the *geometric transfer* and the *transfer with shell profiles*.

   The words "ceiling", "census" (except in a program name), "floors",
   "certificate" (for Section 8) and "hard window" were retired. The last is
   now the *unweighted shell profile*.
3. **First editing round.** Three editors worked on disjoint files under these
   conventions. The coordinator edited the introduction and the abstract.
4. **Review.**
   - Three referees compared the old and new versions file by file. They found
     no change to any statement's mathematical content and no changed digit.
   - Two further referees read the new version as first-time readers.
5. **Second editing round.** All their findings of the two higher severities,
   and most minor ones, were applied.
6. **Final check.** Two referees verified every second-round change. They
   found no mathematical error, no changed constant and no weakened
   hypothesis. They also found one error in a new plain-language sentence of
   the introduction, about ideal classes, which grouped the wrong ideals; it
   was corrected against the proof of Lemma 5.6. Their wording and citation
   points were applied.

## Result

- **Size and numbered statements.** The paper has 66 pages instead of 57. It
  has 29 Definitions (before: 3), 4 Theorems (3), 16 Propositions (13),
  56 Lemmas (36), 8 Corollaries (2) and 11 Remarks (6).
- **Section titles.**
  - Section 4: "The Relative Zeta Value and an Explicit Upper Bound".
  - Section 5: "Units of Relative Norm One and Planar Point Sets".
  - Section 6: "Shell Profiles at Split Finite Places".
  - Section 8: "Proof of Theorem 1.1".
- **Section 8.** It now runs:
  - Definition 8.1 (the data) and Definition 8.3 (the lower bound 𝓜_* for the
    margin);
  - Proposition 8.4 (exact finite checks) and Proposition 8.5 (rigorous
    enclosures);
  - Corollary 8.9 and Lemma 8.10;
  - a proof of Theorem 1.1 that verifies each hypothesis by a cited numbered
    statement.
- **Statements promoted from prose.** Among them:
  - Jennings' theorem (Theorem 2.2) and the value P_B(34/117) < 0 (Lemma 2.38);
  - the Frobenius vectors of the primes of norm at most 10⁶ (Proposition 4.31);
  - the corrections, the lower bounds for the types and the constant 𝒟 (Lemmas 4.32–4.36);
  - the window lemmas and the product-function lemma (Section 5);
  - Corollary 6.23, which specializes the shell-profile transfer to uniform
    local types.
- **Renamed overloaded symbols.**

  | Before | After |
  |---|---|
  | the Galois group of B_S/B | G_S |
  | the Hilbert polynomials P_D, P_Γ | h_{𝔽₂[D]}, h_{𝔽₂[Γ]} |
  | the Frobenius vector v_𝔭 | \overline{Frob}_𝔭 |
  | the conductor exponent | c_𝔭(e) |
  | valuations | ord |
  | the embeddings of Section 5 | φ |
  | the log-unit lattices | 𝒰_K, 𝒰_F |
  | the gamma term | Υ |
  | the margin bound M_* | 𝓜_* |
  | χ_{241} | χ_B |

- **Short arguments added where the old text left a step implicit:**
  - the conjugacy of the complex conjugations in the proof of Theorem 2.42;
  - injectivity on gr₁ and gr₂ for C₂, C₂×C₂ and C₄ in Proposition 2.39;
  - the probability measure and the averaging measure in the proof of
    Proposition 6.21;
  - the independence of N from the choice of places;
  - Borel measurability in Lemma 5.25.
- **Ā_ℂ\*.** It is now defined as the exact upper end of the rigorous
  enclosure computed by `geom241.py`, so every number in Proposition 8.5 is
  exactly what that program computes. The decimal 38.7888697256861071 is that
  end rounded up.
- **Corrected statements of the old text.**
  - The introduction's "J_ℂ − 2J_ℝ − log π > 0.632" now reads "> 0.6324". The
    old bound did not imply the claimed "> 0.316" at θ ≥ θ_*.
  - The δ = 0.0428 observation concerns the computed lower bound for the
    margin, and Remark 8.12 states what was kept and what was re-optimized.
  - In the abstract, "Golod–Shafarevich polynomial" became "Golod–Shafarevich
    function", and the sentence on the degree-512 field now reads: "The
    relative zeta value is bounded through the zeta function of the degree-512
    field generated over Q(√241) by the square roots of its {2,3,5}-units,
    which is the product of the Dedekind zeta function of Q(√241) and 255
    quadratic Hecke L-functions." Previously it read: "… bounded through the
    255 quadratic Hecke L-functions of the degree-512 field generated over
    Q(√241) by the square roots of its {2,3,5}-units."
- **Left unchanged (the author's text):** the AI Methodology paragraph and the
  abstract's last sentence.

## Checks

- **Build.** The paper builds with no undefined reference, no duplicate label
  and no overfull line.
- **Programs.** The referees ran `geom241.py`, at δ = 0.04273 and at
  δ = 0.0428, and `gs241.py`. The output matches every decimal of Section 8
  and the value of P_B(34/117).
- **Recomputed independently:**
  - the census counts, Σ₂, the conductor table, the ranks of degree two, 𝒟,
    Y_* and the final bound 0.0487128429;
  - the Bernstein data q₀, ρ_𝒬 and log K_ℂ.
- **Not checked by the referees:**
  - the cited external results (Jennings, Quillen, Tsfasman–Vlăduţ,
    Louboutin, DLMF);
  - the archived modules beyond running them;
  - the full replay, which this revision does not affect.
