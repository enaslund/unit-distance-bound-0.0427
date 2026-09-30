# Two-eigenvalue Euler coefficient lemma

## Artifact and exact status

The standalone Lean source is
[`TwoEigenEulerCoefficientBound20260923.lean`](TwoEigenEulerCoefficientBound20260923.lean).
Its current SHA-256 is
`e937aece97d10dc33eadf7753f6d3fbf12770e6c78c56ac763da197cefe39262`.
It imports only Mathlib modules (`Mathlib.Analysis.Normed.Group.Basic`,
`Mathlib.Analysis.Complex.Basic`, `Mathlib.Data.Complex.Basic`, and
`Mathlib.Algebra.Order.GroupWithZero.Basic`) and contains the theorem and a
focused `#print axioms norm_twoEigenEulerCoeff_le` command. Static inspection
finds no `sorry`, `admit`, or declared axiom; `git diff --check` passes.

**Status: PASS, compiled under the shared guard with pinned Lean v4.32.0.**
The successful invocation used `lake env lean -j1 -M2560` and was admitted
with 15.9 GiB host available and 1.13 GiB cgroup headroom; it exited 0. The
in-file focused axiom audit printed exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, custom axiom, or admission in the successful theorem.
The final source SHA-256 is
`e937aece97d10dc33eadf7753f6d3fbf12770e6c78c56ac763da197cefe39262`.
A `.olean` was not requested or emitted by this direct `lean` invocation, so
an `.olean` hash is unavailable (not zero). The two preceding guarded failures
were against earlier source hashes: the first stopped before launching because
`lake` was absent from `PATH`; source SHA
`25a384ed9a425145344d41bd2c55cc1b51f336ecb1bbca6f1b33c03b66f41b1c` then
failed on missing `Norm ℂ`; source SHA
`95917efe22419fc63c7a76eca7535d2ba68d455c3f7252a94a9cfb886b077b7c` failed
on unknown `norm_mul`. Their post-error `sorryAx` prints were invalid audits.
The final source uses `Mathlib.Analysis.Complex.Basic`, which provides the
complex `NormedField` instance.

## Statement

For all complex `α`, `β` and every natural `k`, the file proves
statement from `‖α‖≤1` and `‖β‖≤1`:

\[
\left\|\sum_{j=0}^{k}\alpha^j\beta^{k-j}\right\|\le k+1.
\]

The proof applies the norm triangle inequality to the `k+1` terms. Each term
has norm `‖α‖^j ‖β‖^(k-j)≤1`, using nonnegativity of norms and
`pow_le_one₀`. The theorem is independent of Artin representations, fields,
primality, and H6 data.

## Use and limits

If a local Artin factor is
`((1-αT)(1-βT))⁻¹`, its `T^k` coefficient is the displayed sum. For an
inertia-invariant eigenspace of dimension zero or one, first pad its eigenvalue
list with zero eigenvalues to length two; this gives the same local factor and
lets the proved inequality apply. To use it globally still requires proving
that every prime's actual local factor has this form with eigenvalue norms at
most one, that its local coefficients are the intended row coefficients, and
that the global coefficients are multiplicative. Finite image supplies
unit-modulus eigenvalues on inertia invariants, but that representation and
row-factor identification must themselves be formalized.

This source establishes no all-n coefficient bound for H6 twist `+1` and
makes no claim about any H6 row. The existing all-n twist `−1` coefficient
bound and the finite twist `+1` coefficient hash are distinct results, as
recorded in
[`artin-degree-two-coefficient-majorant.md`](artin-degree-two-coefficient-majorant.md).
