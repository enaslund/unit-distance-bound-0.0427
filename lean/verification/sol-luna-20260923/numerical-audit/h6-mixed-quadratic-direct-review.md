# H6 mixed-quadratic direct replay: interval review

## Scope

This is a source and result review of the admitted pointwise replay for mask
1586, twist `+1` (degree 2, conductor 240240, cutoff 3922). I did not run a
replay, alter the replay script, or change the frozen source data. The replay
result is `FAIL direct upper exceeds frozen allowance`, with a direct log upper
larger than the stored endpoint by `4.4446443000903371e-26`.

That result is a failure of this replay's *endpoint comparison*. It is not a
contradiction with the frozen row, and it does not show the frozen upper bound
is false. Both compared numbers are upper bounds; one upper bound can be
slightly weaker than another. A contradiction would require a certified lower
bound for the same target above the frozen upper, or incompatible enclosures
of the same value. This diagnostic supplies neither.

## What the two finite-sum evaluators compute

The frozen evaluator in `nonpositive-afe.py` first contracts each bin's exact
moments against the Taylor polynomial: it translates from the bin midpoint,
forms the coefficients using the binomial formula, multiplies by the stored
moments, and accumulates the Taylor remainder weighted by the bin mass
([`nonpositive-afe.py`](../../../../publication/five-prime-lower-bound/research/nonpositive-afe.py:149),
especially lines 170–178). After multiplying by the common prefactor, its
`evaluate` routine adds primary and dual real parts for root number `+1`, adds
two one-sided error debits, multiplies by the removed-factor modulus, and takes
the logarithm ([`h6-low-degree-euler.py`](../../../../publication/nonabelian-dyadic-lower-bound/research/h6-low-degree-euler.py:93)).

The direct replay instead evaluates each nonzero coefficient against its
piece's Taylor polynomial separately, sums those terms, and debits the same
piece remainder weighted by `|re|+|im|`
([`h6_mixed_quadratic_direct.py`](h6_mixed_quadratic_direct.py:132)). It
reconstructs the full coefficient vector, matches its hash, and checks every
stored exact moment bin before doing this contraction (lines 189–203). Its
final signed-root-number calculation uses `abs(A+B).upper + 2*error.upper`,
then the same removed-factor product and logarithm (lines 233–258).

Algebraically these are two contractions of the same Taylor polynomial against
the same coefficient vector: the binomial translation in the frozen route is
the expansion of the pointwise polynomial at `t*n - center`. They use the same
pinned `SplitKernels`, Taylor remainder, and Arb/FLINT implementation; the
direct route is an independent coefficient contraction, not an independent
kernel or interval backend. The result records 384-bit pointwise arithmetic;
the frozen production source sets 256-bit Arb precision.

## Diagnostic and interval comparison

The recorded exact comparison margin is
`printed upper − direct upper = −4.4446443000903371e-26`. At displayed
precision:

| Quantity | Pointwise replay | Frozen moment row |
|---|---:|---:|
| A finite-sum interval width | `6.1840650480e-22` | `6.1833748815e-22` |
| B finite-sum interval width | `3.1501377345e-22` | `3.1495470237e-22` |
| Signed A+B interval width | `9.3342027826e-22` | `9.3329219052e-22` |
| Modulus upper | `1.44095333595383141826171319402437108` | `1.44095333595383141826171312997892355` |
| Log upper | `0.133316063778537035184834794656877152` | `0.13331606377853703518483475021043415` |

The frozen A interval is contained in the pointwise A interval, and likewise
for B. Their intersections are therefore nonempty; the direct enclosure is
only a little wider. The direct interpolation debit is below the frozen debit.
Its Rankin tail overlaps the frozen tail interval, and its bad-factor modulus
overlaps the frozen interval. The diagnostic also reports that all coefficient
and bin checks passed. These are compatible computations, not competing
values whose enclosures exclude one another.

The frozen row's own signed moment contraction remains a valid route to its
stored upper, conditional on the row assumptions and the correctness of the
pinned evaluator. The replay does **not** produce a fresh pointwise upper
below the stored endpoint. A future checker could intersect the pointwise and
moment enclosures for A and B before adding the shared remainder and tail;
the frozen intervals are already the tighter ones here. That would recover
the frozen endpoint only if the shared Taylor-polynomial identity and both
outward-enclosure calculations are accepted. This review does not provide an
independent formal proof of those interval calculations.

## Conditional scope and provenance

This remains one conditional row. The replay source lists the required
assumptions: the conductor, gamma signature and root number identify the
intended degree-two factor; `|a_n| <= d_2(n)` holds globally; the listed bad
Euler factors are complete; and the pinned Mellin-kernel/tail bound and
outward Arb arithmetic are sound (lines 300–305). Matching the finite vector
and moment bins establishes none of the all-`n` or factor-identification
claims, and this row alone does not establish global H.

Reviewed file hashes:

- Replay result JSON: `5ad1872e87f6c9a823fc3d0ad9491b29807a8cfa9ff61b70335130f1a4caabcf`
- Replay script: `d43c99a4a1ea87a4a7a1bd4ff67f2207ec409092d6cfeb0316a64bbd0563bbd0`
- Frozen H6 evaluation JSON: `bd9c19c7b128a17fd1ea84afae062f812bb2915b4fe2dfea813bfb074496d459`
- Shared quadratic AFE source: `8d6b82b12f7de4a3d53feccde8aaffe0d0fbdf4b623c1447af6ea68ed399cba7`
- Frozen H6 evaluator source: `9fdee8fe5bd9fcbc90c9b28ccbdd0ec5066d49b8b52757ee3f20cc89af707f38`

## Review usage

Source/result inspection and exact endpoint arithmetic only; no Lean build,
guarded numerical run, or frozen-data edit. Worker usage counters were
unavailable (not measured as zero).
