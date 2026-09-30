# Independent review: H6 exponential-integral formula

## Scope

This is a source-only mathematical check of the statement supplied for this
review. I did not consult prior verdicts, build Lean, or run numerical jobs.
The conclusion separates the Mellin-contour derivation from the hypotheses
needed to justify its contour shift.

## Formula and normalization

Put `t = 2π/√Q > 0`. The stated completion is

\[
  \Lambda(w)=2t^{-w}\Gamma(w)L(w).
\]

For `Re(w) > max(0, 1−ν)`, Mellin inversion of
\(E_\nu(x)=\int_1^\infty e^{-xu}u^{-\nu}\,du\) gives

\[
 E_\nu(x)=\frac1{2\pi i}\int_{(c)}
       \frac{\Gamma(w)x^{-w}}{w+\nu-1}\,dw.
\]

Assuming `L(w) = Σₙ₌₁∞ aₙ n^(−w)` in a right half-plane, take
`c > max(3/2, s)`. The coefficient bound gives absolute convergence there,
and summing the two Mellin integrals yields

\[
 \sum_{n\ge1}a_n\big(E_s(tn)+E_{1-s}(tn)\big)
 =\frac1{2\pi i}\int_{(c)}\frac{\Lambda(w)}2
   \left(\frac1{w-s}+\frac1{w+s-1}\right)dw.
\]

Write the parenthesized kernel as `Kₛ(w)`. It satisfies
`Kₛ(1−w) = −Kₛ(w)`. With the stated root number `+1`,
`Λ(1−w) = Λ(w)`; consequently the centered-line integrand
`Λ(w)Kₛ(w)` is odd under `w = 1/2 + iy ↦ 1/2 − iy`,
and its symmetric truncated integral is zero. Shifting the line from `c` to
`1/2` crosses the pole `w = s`, since `s = 12001/12000 > 1/2`, but not
`w = 1−s`. The residue is
\(\Lambda(s)/2=\Gamma(s)t^{-s}L(s)\). Therefore the displayed formula
follows with multiplier `tˢ/Γ(s)`, exactly as proposed.

This checks the factor `2`, the power of `t`, and the **plus** sign. With
root number `−1`, the completed function would be antisymmetric and the same
two-term-plus derivation would not apply. There is no conjugation in the given
exact functional equation. Real coefficients imply the resulting right-hand
side is real at this real `s`; they are not needed for the contour algebra
itself.

## Hypotheses needed to make the derivation rigorous

The statement as supplied should explicitly say that `L(w)` is represented
by `Σ aₙ n^(−w)` in a right half-plane (the bound here ensures absolute
convergence for `Re(w) > 3/2`). Merely naming real numbers `aₙ` does not
connect them to `L`.

The contour shift also needs a vertical-growth or contour-decay condition
that makes the horizontal sides vanish and the centered-line integral
meaningful. Entireness and the functional equation alone do not state such
an estimate. For example, a suitable standard finite-order/vertical-growth
hypothesis, or a separately established bound for this particular completed
Dirichlet series in the strip, would discharge this step. The coefficient
bound directly controls the Dirichlet series only to the right of
`Re(w) = 3/2`; using the functional equation controls the reflected
half-plane, but an explicit strip-growth argument is still part of the
proof. This is a justification gap in the supplied assumptions as written,
not a detected sign or constant error in the formula.

The Mellin integral and smoothed sums themselves converge absolutely on a
line `c > max(3/2, s)`. The proposed sum over `n` also converges absolutely:
for fixed positive `t`, both kernels decay exponentially as `tn → ∞`, which
dominates `|aₙ| ≤ 2√n`.

## Tail inequalities

Here `s−1 = 1/12000 > 0` and `s > 0`. For `x > s−1`, use
`log u ≤ u−1`, `u ≥ 1`, to get
\[
 u^{s-1}\le e^{(s-1)(u-1)}.
\]
Thus
\[
 E_{1-s}(x)=e^{-x}\int_1^\infty e^{-x(u-1)}u^{s-1}du
 \le e^{-x}\int_0^\infty e^{-(x-(s-1))v}dv
 =\frac{e^{-x}}{x-(s-1)}.
\]
For `s > 0`, `u^(−s) ≤ 1` on `u ≥ 1`, and hence
\[
 E_s(x)\le e^{-x}\int_1^\infty e^{-x(u-1)}du=\frac{e^{-x}}x.
\]
All arguments `x = tn` satisfy the first condition: `Q = 240240 < 500²`
and `π > 1` imply `t = 2π/√Q > 1/250 > 1/12000 = s−1`.
So both proposed elementary inequalities apply to every `n ≥ 1`.

## Conclusion and usage

Under the usual Dirichlet-series identity and a sufficient strip-growth
condition for the contour shift, the formula and both tail bounds are
correct; the normalization and sign match root number `+1`. The given
statement alone leaves the series identity implicit and does not state the
growth needed for the contour argument, so those points should be supplied
or cited before treating the formula as established.

No Lean or numerical job was run. Resource counters are unavailable for this
source-only review; they were not measured as zero.
