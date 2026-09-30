# Poisson summation reuse and analytic scope

## Source and license

`UnitDistance/ThirdParty/PoissonSummation.lean` is an adaptation of
[`DedekindZeta/PoissonSummation.lean`](https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean)
from `mathlib-initiative/sum_product`, exact commit
`80e4127a67742659d521466204c6d2d7e0ca2b3f`.
The original copyright notice credits the Formal Frontier Team, 2026, under
Apache-2.0. The full upstream license is preserved at
`third-party/sum_product/LICENSE`. The original namespace and proof text are
preserved. The upstream checkout was read only.

The local adaptation was produced by the autonomous OpenAI Codex GPT-6 Astra
Ultra run requested by Eric Naslund. That provenance does not attribute the
upstream mathematical proofs to this run.

## Dependency reconciliation and modifications

The source project used Lean v4.31.0-rc1. This project uses Lean v4.32.0 with
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
The source file imports only Mathlib. The adaptation adds a provenance block,
corrects a stale comment claiming that its now-present Fourier expansion
proof was deferred, and replaces one finite-product continuity proof with an
explicitly typed intermediate continuous character product. The latter
resolves a changed elaboration/typeclass inference behavior; it changes no
theorem statement or mathematical argument.

## Mathematical audit

The principal upstream identity `periodisation_eq_tsum_fourier` is the
translated Poisson formula in an arbitrary finite-dimensional real inner
product space `V`, for a full-rank discrete `ℤ`-submodule `L` and an actual
`SchwartzMap V ℂ`. It sums over the independently defined dual lattice of
integral inner pairings. The file proves periodization summability and
continuity, dual-lattice discreteness, descent to the compact quotient,
Fourier coefficients, summability of the resulting Fourier series, and the
pointwise Fourier reconstruction. These are proofs, not theorem inputs.
There are no custom axioms or admitted declarations in the adapted file.

All Fourier transforms, integrals and covolumes use Mathlib's same canonical
inner-product-space Lebesgue measure. No arbitrary extra `MeasureSpace V`
instance is introduced. The nonzero translate contributes a character of
modulus one. Thus the absolute Fourier-tail estimate is uniform in the
translate, exactly as required by the joint favorable-parameter argument.
This identity is unaffected by any later choice of adelic compact Haar
normalization, which must be reconciled explicitly in a field specialization.

`UnitDistance/PoissonBound.lean` develops the ensuing Fourier-tail bound.
Its `nonzeroFourierMass` is the actual sum of absolute values of nonzero dual
Fourier coefficients, not a flag, point count, or a number defined from a
desired geometric conclusion. The proved bound states that a nonnegative
Schwartz weight of integral `A`, with this tail at most `A`, has sum at most
`2*A/covolume(L)` on every finite subset of every translate of `L`.
`finite_coset_schwartz_bound` sums this uniform estimate over arbitrary
nonnegative finite fiber weights and independent fiber translates.
`finite_period_schwartz_bound` exposes the exact identity
`covolume(L) = D / cellVolume` and therefore obtains the mixed numerator
`2*A*(cellVolume*∑ weight)`, with no hidden residue-unit multiplier.
`translated_limit_weighted_sum_le` proves the corresponding estimate for a
pointwise limit of nonnegative Schwartz weights, provided their integral
masses converge and their actual Fourier tails satisfy the stated bounds.
It passes only finite sums through the limit; no infinite lattice sum is
silently exchanged with a limit.

## Remaining analytic specialization

The paper's optimized Student weights have polynomial decay and are not
Schwartz functions. Applying the Schwartz theorem directly to those weights
would be incorrect. The proved limit corollary supplies the final finite-sum
limit step for Gaussian damping, but constructing the Gaussian-damped
Schwartz functions, proving pointwise and integral convergence, and
controlling their actual Fourier tails remain necessary. An exponential Fourier envelope, the trace-dual product
separation estimate on the actual arithmetic ideal lattices, and the bound
for every sufficiently large field must still be established in Lean.
The periodic finite-place fiber/CRT realization and the identification of
the Euclidean covolume with the mixed adelic covolume also remain to connect
this analytic theorem to `WeightedWindowModel`.

None of these structural and analytic inputs is represented as a numerical
certificate or discharged merely by porting Poisson summation. This library
reduces one established analytic-foundation gap; it does not prove the
arithmetic-family uniform estimate or the 1.0418235 theorem.

## Verification

Build and axiom-check results are recorded after execution in the project
verification logs. The source build command is:

```sh
source env.sh
lake build UnitDistance.ThirdParty.PoissonSummation UnitDistance.PoissonBound
```

Both modules built successfully on the pinned project toolchain. The last
build log is `verification/poisson-bound-build.log`; it includes the imported
Poisson module and the new bound module. The vendored file emits upstream
unused-variable and unused-section-variable style warnings. The local bound
module builds without warnings.

The following check was run successfully:

```sh
lake env lean verification/PoissonAudit.lean > verification/poisson-axioms.log
```

The translated and unshifted Poisson identities, Fourier norm split,
translated Schwartz bound, finite-sum limit bound, and finite-period bound
all depend only on `propext`, `Classical.choice`, and `Quot.sound`, as recorded
in that log. The separate Mathlib-only `ChallengePoisson.lean` and
`SolutionPoisson.lean` target `translated_limit_weighted_sum_le` and
`finite_period_schwartz_bound`, whose dependencies include the full translated
Poisson proof. The actual command

```sh
bash scripts/verify-comparator.sh comparator-poisson.json > verification/poisson-comparator-recheck.log 2>&1
```

passed exact theorem/definition comparison, the independent NanoDa kernel,
and the reconstructed Lean default kernel. The saved log ends with all three
successful results. An earlier attempt terminated during its Solution build
with SIGTERM (exit143), before comparison; this is saved separately in
`verification/poisson-comparator.log`. A direct Solution build then succeeded,
and the complete retry passed. No source theorem was weakened for the retry.
