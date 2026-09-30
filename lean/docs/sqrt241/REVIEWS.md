# Independent reviews of the 1.0427 package (2026-09-29)

Two reviewers worked in fresh contexts. They received the files and their
intended meaning, but no author verdicts. Their scratch work stayed in the
session scratchpad. This record summarizes their findings and what was done.

## Statement review (ChallengeZeta241.lean, evidence for H)

**Verdict: no blocking issue.**

* **Conclusion.** It is the intended planar statement. `dist` is the Euclidean
  metric on ℂ; the reviewer proved this with `Complex.dist_eq_re_im`.
  `unitPairs` halves the ordered count exactly, and `^` is the real power with
  exponent 10427/10000.
* **Field.** The radicands match `kummer241.gp`. The following were checked in
  PARI:
  * integrality and norms;
  * that no nontrivial product of radicands is a square;
  * the S-unit rank 7;
  * h(B) = 1 (`bnfcertify`).

  The field does not depend on the choices of square roots: replacing √241 by
  −√241 maps the radicand span to itself modulo squares.
* **H.** It is well defined (both arguments have real part > 1) and parses as
  documented.
* **Independent recomputation of H.** The reviewer used a different route from
  `h241_receipt.py`: PARI Hecke L-functions for all 256 quadratic characters of
  the ray class group of B modulo 120·∞₁∞₂.
  * The characters were matched to Kummer vectors at 633 primes.
  * All 255 functional-equation checks passed at ≤ −192 bits.
  * Gamma types and conductors agree with the construction.

  | quantity | value |
  |---|---|
  | (1/512) log ζ_E(301/300) | 0.0826446049229 |
  | −(ζ_E′/ζ_E)(2)/512 | 0.0197173400 |
  | left side of H | 0.0848334667 |
  | slack to 852/10000 | 3.665·10⁻⁴ |

  All three agree with the receipt's rigorous upper bounds.
* **Fixed:**
  * the comment justifying the inherited imports and options (they are
    harmless, and the comment no longer claims more);
  * the `logRD` docstring (ℓ bounds the tower fields' root discriminant, not
    E's);
  * "a fundamental unit" in place of "the fundamental unit";
  * wording of the module docstring;
  * an unused `BigOperators`.

## Code review (UnitDistance/Sqrt241, SolutionZeta241, ChallengeZeta241)

**Verdict: no blocking defect.**

* **Soundness.** None of the following occurs: `sorry`/`admit` (apart from the
  Challenge placeholder), `axiom`, `native_decide`, `ofReduceBool`,
  `implemented_by`, `extern`, `unsafe`, `@[csimp]`, `#eval`/`run_cmd` side
  effects, `maxHeartbeats 0`.
* **Statement match.** All 32 constants of the two files were dumped and
  compared. They are identical except the main theorem's proof. That proof is
  exactly `fun hfinite => UnitDistance.Sqrt241.target_of_canonical_genus_zeta_bound hfinite`,
  with no coercion.
* **Axioms.** They are the standard three.
* **Replay.** `leanchecker` passed on 42 modules. The full replay of all 239
  closure modules is recorded in `verification/sqrt241-20260929/`.
* **Generators.** Every generator reproduces its committed files byte for byte.
  The geometry pipeline needed a one-line fix first.
* **Should-fix findings S1–S8.** Fixed in a cleanup pass that changed no
  statement or definition; see `CLEANUP.md`. They were:
  * the broken geometry script;
  * documentation citing unused theorems;
  * a block count;
  * provenance headers and the census generator;
  * stale wording;
  * deprecations;
  * file-wide heartbeat options.

  Deliberately left:
  * 10 unused section variables in hand-written lemmas, because omitting them
    would change those lemmas' statements;
  * the deprecations inside generated copies, which reproduce the verified ℚ
    proofs.
