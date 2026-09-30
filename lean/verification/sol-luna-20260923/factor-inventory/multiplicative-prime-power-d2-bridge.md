# Multiplicative prime-power to `d₂` bridge

## Exact status

The importable Mathlib-only source is
[`MultiplicativePrimePowerD2Bridge20260923.lean`](../../../UnitDistance/MultiplicativePrimePowerD2Bridge20260923.lean).
Its source SHA-256 is
`c58754aaef8d2e90ab1c7cb2540741b9c027b2a3e63c588ab1a337ee4d68233a`.
**Status: PASS, compiled under the shared guard with pinned Lean v4.32.0.**
The final source bytes were copied into the `UnitDistance/` module unchanged;
both copies had the source hash above before the verification copy was removed.
The admitted retry used `-j1 -M2560`, with 16.4 GiB host available and 1.58
GiB cgroup headroom; it exited 0. Each of the three focused audits printed
exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` or custom axiom appears in the successful declarations. The
direct `lean` invocation did not request or emit an `.olean`, so an `.olean`
hash is unavailable (not zero); a module-path `-o` build and import check
remain pending guarded allocation.

For provenance, an earlier attempt deferred before admission with exit 75
(`shared build lock busy or insufficient available RAM`; gate thresholds were
host 10 GiB and cgroup 1 GiB). The next attempt, admitted with 16.4 GiB host
available and 1.76 GiB cgroup headroom, compiled the two helper lemmas but
failed at the main theorem because `Finset.prod_le_prod'` required
`MulLeftMono ℝ`. Its source SHA was
`c2ed78fca89e45af5e9d5c6ef128199989d7aee57e7ad7f5ddd38f70ddd64148`; the
main theorem's post-error `sorryAx` print was invalid. The final source uses
`Finset.prod_le_prod` and supplies nonnegativity of norm factors explicitly.

## Theorem and assumptions

`norm_le_zeta_sq_of_prime_power_bound` takes a complex arithmetic function
`a`, a proof `ha : a.IsMultiplicative`, and the local estimate
`‖a (p^k)‖ ≤ k+1` for every rational prime `p` and exponent `k`. It concludes,
for every natural `n`,

\[
\|a(n)\| \le ((\zeta^2)(n):\mathbb N):\mathbb R,
\]

where `ζ²` is the Dirichlet-convolution square of Mathlib's zeta arithmetic
function, hence the two-fold divisor function `d₂`. The proof uses
`IsMultiplicative.multiplicative_factorization` for both `a` and `ζ²`, the
prime-power identity `ζ²(p^k)=k+1`, multiplicativity of `ζ²`, and comparison of
the finite products over prime factors. The case `n=0` follows because both
arithmetic functions vanish there.

The theorem does **not** assume or prove that the actual H6 twist-`+1` row is
multiplicative, nor does it derive its local prime-power bound from an Artin
representation. Those facts must be established for the chosen coefficient
sequence first. In particular, applying it to coefficients of
`ζ_{B(√η)}/ζ_B` requires constructing that sequence and proving its local
coefficient bounds; applying the result to the manuscript row further
requires equality of the row's all-rational-prime Euler factors with this
quotient. This bridge is only the multiplicative local-to-global step.

## Expected instantiation route

For a two-dimensional finite-image representation, at each rational prime the
local factor on inertia invariants has dimension 0, 1, or 2. Its finite-order
Frobenius eigenvalues have norm one; pad dimensions 0 or 1 with zero
eigenvalues to length two. The separately compiled
`norm_twoEigenEulerCoeff_le` lemma then gives the coefficient bound `k+1` at
each prime power. The staged theorem here combines those bounds using
multiplicativity. Neither step supplies the missing H6 row/quotient
identification or the finite-image representation construction.
