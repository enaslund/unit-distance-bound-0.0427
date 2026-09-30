# Actual number-field normalization and Euler series

This continuation follows `analytic.tex`, particularly the definition of
`L_F(1)` and equation `an:class-formula`, and the class-number normalization
preceding `geo:mass-density`. It uses the sealed manuscript at commit
`eec70fd25ebe045c5df1c98370d613eaa3719c0c` without changing it.

## Historical full-result component checkpoint

The analytic obligations listed later in this component record were open at
its original normalization/Euler checkpoint. Subsequent modules prove the
actual relative entire continuation, completed-function comparison,
Tsfasman–Vladut prime budget, regulator/capitulation mass and eventual
relative-residue ceiling along the required growing families. The actual
family is now constructed in `SigmaCutFamily` and assembled by `SigmaCutTarget`,
whose terminal theorem passes a direct Lean check with the standard three
axioms only.

The following paragraph records a separate full-result component checkpoint;
its claims and open-verification list are historical, not the selected
Palomar package described in this handoff.

At that historical checkpoint, the full-result candidate was [FullResult.lean](../UnitDistance/FullResult.lean),
with [SolutionFull.lean](../SolutionFull.lean) and its independent
[Mathlib-only Challenge](../ChallengeFull.lean). It was described as retaining only the three
fixed numerical hypotheses, including a root-discriminant bound and a
specified zeta/logarithmic-derivative inequality for the independently
specified canonical field. At that checkpoint, the final normal composition/build, imported
audit, Comparator/NanoDa/Lean replay and fresh-source rebuild were pending.
See [the proof path](FULL_RESULT.md),
[the frozen source manifest](../verification/full-comparator-inputs.json), and
[the verification record](../verification/README.md). The earlier component
evidence below does not by itself certify this larger source closure.

The selected conditional package uses the one-hypothesis `ChallengeZeta` and
`SolutionZeta` sources. Its displayed fixed-field inequality H remains open;
the FullResult/three-hypothesis checkpoint above is not its statement or proof.
At the September 27, 08:04 UTC package checkpoint, candidate23's source export
and archive-only metadata gate passed, but it had no full verifier result.
These package facts do not change or upgrade the historical FullResult evidence.

## Compiled normalization

Declarations in the first three modules have namespace
`UnitDistance.NumberFieldAnalysis`.

| Module | Actual proved quantities and statements |
|---|---|
| `RelativeZeta` | The integral-ideal counting asymptotic, absolute convergence of the actual Dedekind L-series for `Re(s)>1`, positivity and reality above one, and the right limits of the actual relative zeta quotient and its real logarithm. `relativeResidue` is the positive quotient of the two actual Mathlib residues. |
| `RelativeDiscriminant` | Ordinary finite unramifiedness is equivalent to the relative different being the unit ideal. The actual discriminant is the corresponding base-discriminant power, so the actual root discriminants agree. The root discriminant and its square-root normalization use exact real powers. |
| `RelativeClassNumber` | For an actual finite-unramified quadratic extension with totally complex upper field, the relative residue is `2^c*pi^(b+c)*rootDiscriminant(F)^(-[F:Q]/2)*h_K*R_K*w_F/(h_F*R_F*w_K)`. A real embedding derives `w_F=2` and hence the class/regulator formula used in the mass calculation. |

The formulas use Mathlib's independently defined field discriminants,
class numbers, ordinary weighted regulators and torsion orders. The proofs
do not assign these quantities desired values, assume a mass identity, or
assume a limit of graph counts. Finite unramifiedness, quadratic degree and
signature are genuine field hypotheses; they are not numerical certificates.
Their realization along the intended tower was open at this component checkpoint;
the subsequent actual-family assembly now supplies it.

## Ideal-series development

`IdealCounting` compiles the actual norm-counting coefficient multiplicativity,
the prime-power bound via actual ideal multiplicities and inertia degrees,
the divisor-function majorant, and the Dirichlet-series convolution identity.
The coefficient at zero is suppressed only in `idealCountArith`, as required
for an arithmetic function; positive-norm coefficients agree exactly with
the actual ideal counts. This agrees with Dedekind L-series conventions.

This is an attributed port of `SumProduct/EulerBound.lean` through
`LSeriesSummable_and_LSeries_zeta_pow`, at sum_product commit
`80e4127a67742659d521466204c6d2d7e0ca2b3f`, by the Formal Frontier Team under
Apache-2.0. The specialized bound at two was not copied. Changes comprise
the project namespace and documentation, and the July 2026 Mathlib renaming
of the old two-ideal `inertiaDeg` API to `inertiaDeg'`, including its
nonvanishing theorem. The original copyright and license are preserved.

`DedekindEuler` compiles an adaptation of the same source's
`DedekindZeta/Statements.lean`: ideal-series regrouping, summable geometric
monomials, and the actual nonzero-ideal/finitely-supported-exponent
bijection. It uses the proved summability in `RelativeZeta` rather than
repeating the ideal-counting asymptotic. Its strengthened ideal-series
conclusion is `HasSum`. The new `dedekindZeta_eulerProduct` proves the full
Euler product over actual prime ideals throughout `Re(s)>1`. The proof
restricts the proved absolutely summable ideal series to prime ideals,
proves every prime factor has norm less than one, and transports the
monomial series through the actual ideal-factorization equivalence.
These operations are proved, not supplied as Euler-product hypotheses.
`DedekindEulerLog` now proves the actual positive real Euler product and the
summable prime-ideal logarithm series. `RelativeEuler` constructs the actual
prime fibers over an arbitrary number-field extension, identifies them with
the finite prime-ideal set, uses the proved residue norm and fiber-cardinality
bounds, and regroups the logarithmic series. It proves
`log(zeta_K(s)) <= [K:F]*log(zeta_F(s))` for all real `s>1`. For quadratic
extensions this gives exactly `an:relative-euler`, with denominator
`2*[F:Q]`. This step requires no Galois or unramifiedness premise.

## Analytic obligations at the earlier checkpoint

The normalized class formula and the right limit alone do not bound that
limit. The original remaining work comprised the completed relative-Hecke
function and its monotonicity/zero arguments, selected-prime and global
explicit estimates, and a bound for **every sufficiently large field** in the
actual retained family. The precise target was
`log(relativeResidue K F)/[F:Q] < 42161819/10^9` along that family.
Neither the ordinary divisor majorant nor a finite scalar optimization
implies this assertion. Relative logarithmic covolumes and capitulation
cardinalities are also logically separate from the class-number formula.

These obligations have subsequent proofs: `ImaginaryQuadraticContinuation`
constructs the actual entire relative factor; `RelativeHeckeEntireComparison`
and `RelativeHeckeDiscriminant` give the actual completed-function comparison;
`TsfasmanVladutBasicInequality`, `RelativeResidueFixedBase` and the
`SIntegerWitnessAnalytic`/`SIntegerWitnessQuadratic` chain give the eventual
ceiling from the fixed numerical bound; and `RelativeUnitsMass` supplies the
actual regulator/capitulation normalization. The new final candidate applies
them to the constructed fields. This records mathematical scope, while the
pending final verification remains distinguished from the earlier checks.

## Verification

Lean v4.32.0 and Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` compile
these modules. The expanded targeted audit successfully checked all 177
owned declarations across the seven modules, including private/generated
auxiliaries. Only `propext`, `Quot.sound` and `Classical.choice` occur.
Saved records are `number-field-analysis-build.log` and
`number-field-analysis-axioms.log`. Reproduce with:

```sh
source env.sh
lake build UnitDistance.RelativeEuler UnitDistance.RelativeClassNumber UnitDistance.IdealCounting AuditSupport
lake env lean -DstderrAsMessages=false verification/NumberFieldAnalysisAudit.lean
scripts/verify-comparator.sh comparator-number-field.json
scripts/verify-comparator.sh comparator-euler.json
```

The standalone Challenges contain only Mathlib imports and ordinary field
definitions. The two configurations separately test the relative boundary
limit/class formula and the Euler product. Three initial attempts exposed
an unused binder and differing elaborated complex topology instances when
combining imports. Their failed logs are preserved under
`number-field-comparator-initial.log`, `number-field-comparator-topology.log`
and `number-field-comparator-mixed-imports.log`. The statements have been
separated into two small Challenges, with explicit fully elaborated type
comparisons passing. The Euler configuration now exited 0 after successful statement/axiom
comparison, NanoDa checking and Lean kernel replay; see
`verification/euler-comparator.log`. Its first independent run failed from
a full /tmp; that failed log is retained as `euler-comparator-space.log`.
The successful rerun used `TMPDIR="$PWD/.cache/comparator-tmp"`.
The NumberField configuration also exited 0 after NanoDa and Lean kernel
acceptance for both targets; see `verification/number-field-comparator.log`.
The remaining universe-parameter-name mismatch was repaired by declaring
FiniteUnramified before the unrelated section variables; its failed log
is retained as `number-field-comparator-universe-names.log`. These checks are separate
from the preserved conditional checkpoint archive.

New proof and integration work was produced by the requested GPT-6 Astra
Ultra Codex continuation under Eric Naslund's direction. Reused proofs retain
their upstream authorship; no independent human review is claimed.
