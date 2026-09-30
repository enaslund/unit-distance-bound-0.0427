# Independent review: selected conditional zeta theorem

## Finding

Within the source scope checked, I found no concrete mismatch in the claim
that the displayed hypothesis (H) implies the exact sequence target. The
exponent, Euclidean plane, unordered-pair normalization, and sequence
quantifiers line up with the target definition. This is a conditional
implication: the truth of (H) remains a separate, unproved numerical
obligation. This review did not independently re-prove the imported tower,
analytic, or geometric developments.

## What (H) says

In `ChallengeZeta.lean:34–39, 119–126`, let

\[
 d=524288,\quad \varepsilon=1/12000,\quad
 L=(9/4)\log 2+(1/2)\log 15015,\quad C=42165819/10^9.
\]

The premise is exactly

\[
\frac{\log(\operatorname{Re}\zeta_K(1+\varepsilon))}{d}
+\varepsilon\left(\frac{L-\gamma-\log(4\pi)}4
-\frac{\operatorname{Re}(\zeta'_K(2)/\zeta_K(2))}{d}\right)<C,
\]

for the explicitly generated field `CanonicalRetained.Carrier`. The actual
Lean term uses `logDeriv (dedekindZeta K) 2`, the logarithmic derivative.
The denominator is the absolute field degree, not a relative degree. There
is one premise; the field and constants are definitions. The conclusion is
that some sequence of finite subsets of `ℂ` has cardinalities tending to
infinity and its unit-pair count divided by cardinality to the power
`2083647/2000000` tends to infinity. It does not promise such a bound at
each sufficiently large cardinality.

`ChallengeZeta.lean:28–36` defines the pair count as half the number of
ordered pairs at standard complex distance one. The diagonal is excluded by
the distance condition, and symmetry gives two ordered representatives per
unordered edge. `UnitDistance/Target.lean:20–48` independently defines the
same count and target; `UnitDistance/Counting.lean` proves the conversion to
the direct unordered `Sym2` count. The exponent is exactly
`1 + increment`, where `increment = 83647/2000000`; the rational identity is
proved in `Target.exponent_eq` (`Target.lean:35–39`).

## Why the premise suffices in the selected proof

The source-level chain checks out:

1. `CanonicalSharperZetaResultRun20260920.lean:20–34` reduces the target to
   a strict fixed-base residue-ceiling bound for the arithmetic retained
   field. It rewrites the degree and the zeta and logarithmic-derivative
   values along `CanonicalRetained.equiv`.
2. `PrimeDebitLogDerivative.lean:56–82` identifies that residue scalar with
   the displayed zeta/log-derivative expression. Its sign is consistent:
   the normalized prime debit equals minus the real logarithmic derivative
   at 2 divided by the degree.
3. `CanonicalRetainedEquiv.lean:20–34, 70–105, 125–162` aligns the arbitrary
   square-root choices, identifies the generated field with the arithmetic
   retained field, and proves degree `524288`. This addresses the apparent
   dependence on signs chosen by `Classical.choose` in the Challenge.
4. The premise is strict. `SharperPairFixedBaseBridgeRun20260920.lean:382–397`
   applies the strict fixed-base endpoint. The midpoint argument
   (`:93–152`) turns the strict inequality into a positive uniform rate
   below the relaxed ceiling.
5. The selected margin is supported internally by
   `PairFunctionalSharperThresholdAstra.lean:19–81`: it proves
   `JPair ≥ 1.379633` and a margin exceeding `4e-6`. The relaxed terminal
   threshold is `0.042161819 + 0.000004 = 0.042165819`
   (`SharperPairFixedBaseCoreRun20260920.lean:18–24`). With the fixed
   root-discriminant and signature bounds, this leaves a positive
   exponential graph-count rate. `ArithmeticSequence.lean:12–37` extracts
   the sequence and both limits.

The selected theorem therefore gives the announced exponent under (H),
conditional on the correctness of its imported Lean proofs. The source
statement does not assume a tower, pair-integral estimate, or local behavior
as extra hypotheses; those are discharged inside the dependency chain. The
margin calculation is coherent at the stated relaxed threshold, which is
four millionths above the earlier `0.042161819` threshold.

## Verification boundary

`SolutionZeta.lean:1–3, 101–108` imports and applies the assembled theorem.
`ChallengeZeta.lean:119–127` is the separate statement file and deliberately
ends with `sorry`; that placeholder is not used as the solution proof. The
review was source-level and did not run Lean or the numerical certificate,
following the one-expensive-slot restriction. I did not inspect every
transitive lemma in the large imported proof closure. The checked files and
the theorem chain above support the conditional implication only; they do
not establish (H) or the unconditional exponent claim.

No build, numerical replay, or other resource-intensive verification was
run. No repository files were changed except this review report. Workspace
status showed numerous pre-existing user changes, which I left untouched.
