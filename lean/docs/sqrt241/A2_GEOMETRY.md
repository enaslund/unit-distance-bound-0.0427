# Stream A2: geometric/downstream chain for ℚ(√241)

Status (2026-09-29): **done.** `UnitDistance.Sqrt241.target_of_growing_galois_fields`
is proved in `UnitDistance.Sqrt241.Geometry.FixedBaseBridge`; the whole
directory `UnitDistance/Sqrt241/Geometry/` (87 modules, ≈9.1k lines) builds,
and `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

## Deliverable

```lean
theorem UnitDistance.Sqrt241.target_of_growing_galois_fields
    (M : Type) [Field M] [NumberField M]
    (Ks : ℕ → Type) [∀ j, Field (Ks j)] [∀ j, NumberField (Ks j)]
    [∀ j, IsGalois ℚ (Ks j)] [∀ j, Algebra M (Ks j)]
    (φ : ∀ j, Ks j →+* ℂ) (c : ∀ j, Gal(Ks j/ℚ))
    (hc : ∀ j, NumberField.ComplexEmbedding.IsConj (φ j) (c j))
    (hc1 : ∀ j, c j ≠ 1)
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop)
    (hunrM : ∀ᶠ j in atTop, NumberFieldAnalysis.FiniteUnramified M (Ks j))
    (he : ∀ᶠ j in atTop, ∀ a : Fin 5,
      (NumberFieldAnalysis.rationalPrimeIdeal (Witness.primes a)).ramificationIdxIn
        (𝓞 (Ks j)) = Witness.ramification a)
    (hf : ∀ᶠ j in atTop, ∀ a : Fin 5,
      (NumberFieldAnalysis.rationalPrimeIdeal (Witness.primes a)).inertiaDegIn
        (𝓞 (Ks j)) = Witness.residueDegree a)
    (hfree : ∀ᶠ j in atTop, ∀ a : Fin 5,
      ∀ P : NumberFieldAnalysis.PrimeNormFiber (Ks j) (Witness.primeNorm a),
        Ideal.map (NumberField.RingOfIntegers.mapRingHom (c j).toRingHom)
          P.1.asIdeal ≠ P.1.asIdeal)
    (hindex : ∀ᶠ j in atTop,
      65536 ≤ (Subgroup.centralizer (Set.singleton (c j))).index)
    (hdiscM : Real.log (NumberFieldAnalysis.rootDiscriminant M) ≤ Witness.logRD)
    (r3 : M) (hr3 : r3 ^ 2 = 3) (ii : M) (hii : ii ^ 2 = -1)
    (hmargin : ∀ θ : ℝ, Witness.thetaMin ≤ θ →
      0 < Witness.margin θ - 4 * Witness.epsilon)
    (hfinite : NumberFieldAnalysis.fixedBaseResidueCeiling M Witness.logRD (1 / 300) <
      Witness.ceiling) :
    Target
```

Inside `namespace UnitDistance.Sqrt241`: `Witness` is `UnitDistance.Sqrt241.Witness`,
`Target` is `UnitDistance.Sqrt241.Target`, `Witness.primeNorm a = primes a ^ residueDegree a`
(in `Geometry.WitnessPrimePairs`); `NumberFieldAnalysis.*` are the ℚ
development's generic declarations.

`hmargin` is discharged by stream A1's
`UnitDistance.Sqrt241.Witness.uniform_margin (θ) (hθ) : 1189/10^7 < margin θ - 4 * epsilon`
(`UnitDistance.Sqrt241.Numerics.Margin`), e.g.
`fun θ hθ => lt_trans (by norm_num) (Witness.uniform_margin θ hθ)`; this wiring
is left to the assembly.

Intermediate statements (same module):

* `SIntegerCRT.target_of_witnessFields_of_residueCap (hmargin) … (hU : U < Witness.ceiling)`,
  analogue of `target_of_witnessFields_of_sharperPair_residueCap_run20260920`;
* `SIntegerCRT.target_of_witnessFields_entire_fixedBase (hmargin) M … (hentire)
  (hfinite : fixedBaseResidueCeiling M Witness.logRD (1/300) < Witness.ceiling)`,
  analogue of `target_of_witnessFields_entire_sharperFixedBase_run20260920`.

## Differences from the ℚ bridge

* Threshold `Witness.ceiling` (no `4e-6` allowance); margin positivity is the
  hypothesis `hmargin` (`Geometry.RateCore.fixedBaseGap_le_arithmeticRate`).
* Fixed base `M` arbitrary with `r3² = 3`, `ii² = −1` (ℚ: retained field with
  `√7`, `i`); ε = 1/300 (ℚ: 1/12000); centralizer index `2^16`, giving
  `thetaMin = 65535/131072` via the parametric
  `complexPlaceRatio_bounds_of_retained_index` (`Geometry.GaloisFixedField`).
* Entireness of `ζ_K/ζ_F`: the √7 argument is generalized to an admissible
  radicand `d` (`QuadraticRoot.Admissible d`: `d` prime, `d % 4 = 3`) and used
  with `d = 3` (`QuadraticRoot.admissible_three`): unit norms `+1`,
  `χ₄(|N x|) = sign(N x)` for odd norms (`a² − d b² ≡ a² + b² mod 4`), and
  `τ = (√d + i)/2` integral with minimal polynomial `X² − √d X + (d+1)/4`
  and unit derivative `2τ − √d = i` (for `d = 3`, `τ = ζ₁₂`).
* Five local types: `Fin 5`, `Σ 1/(ef) = 29/32` (ℚ: 69/32).
* Period separation (`Geometry.WitnessPeriodSeparation`): `24 ≤ periodLogDensity`
  fails (value ≈ 15.69); proved `periodLogDensity ≥ (1579/70) log 2` (powers of
  two: `2^19 ≤ 3^12`, `2^23 ≤ 5^10`, `2^34 ≤ 29^7`, `2^14 ≤ 7^5`),
  `logRD ≤ (33/4) log 2` (`3615 ≤ 2^12`), `3 log 5 ≤ 7 log 2`; then
  `log 2 + 2 log 5 + 2 ≤ 2 exp(periodLogDensity/2 − logRD)` follows from
  `1 + x ≤ eˣ` (it needs `17/3 ≤ 212/35`).

## Method

A ℚ module containing a needed declaration that mentions ℚ-witness data gets
a copy `UnitDistance.Sqrt241.Geometry.<Name>` (docstring line "Copy of
`UnitDistance.<Name>` …"). A copy keeps only the needed witness-dependent
declarations (plus the private helpers, attributed private lemmas and local
instances they use), moved from namespace `UnitDistance.X` to
`UnitDistance.Sqrt241.X`; generic declarations are used from the ℚ module,
which the copy imports. References are rewritten from the compiled `.ilean`
reference data of the ℚ originals so that every reference to a copied
declaration resolves to the copy and every other reference to the same ℚ
declaration as before (Lean's first resolution step, longest namespace prefix
first, is simulated; `open` lines are rewritten to full ℚ namespaces).

Pipeline (scripts in `scripts/sqrt241/`, run from `lean-formalization/`):

1. `Analyze.lean`, the taint analysis:
   `SQRT241_ANALYSIS_OUT=scripts/sqrt241/geometry_analysis.json ./.toolchain/bin/lake env ./.toolchain/bin/lean scripts/sqrt241/Analyze.lean`
   (≈9 min, ≈6 GB). Its output is committed as `scripts/sqrt241/geometry_analysis.json`
   (rerun on 2026-09-29: byte-identical). A declaration is copied iff its type (definitions: also
   its value) mentions a constant of the module `UnitDistance.Witness`,
   `increment`/`exponent`, or `Fin 11`, or (in the √7 entireness modules) the
   literal 7, directly or through copied declarations. Traversal from the ℚ
   bridge theorem, cut at the margin lemmas
   (`sharperFixedBaseGap_le_shiftedMargin_run20260920`,
   `uniform_margin_sharper_astra`, …) and at the retained-field lemmas of
   `GaloisFixedArithmetic`. Result: 562 declarations in 85 ℚ modules.
2. `scripts/sqrt241/regenerate_geometry.sh [ANALYSIS_JSON [SCRATCH_DIR]]` (defaults:
   the committed `geometry_analysis.json` and a new temporary directory; it reads
   only repository files and the `.ilean` files of the built ℚ development) runs
   `copy_geometry.py` (copies; `Fin 11 → Fin 5`; first line
   `-- Generated by scripts/sqrt241/regenerate_geometry.sh — do not edit by hand.`),
   installs them except the generated `QuadraticSeven*`/`ImaginarySevenUnramified`
   copies, then `postprocess_values.py` (`69/32 → 29/32`, new period-separation
   proofs) and `postprocess_root.py` (radicand `7 → d` in `HeckeSigned*`,
   `HeckeQuadraticContinuation`, `ImaginaryQuadraticContinuation`). Run in a scratch
   copy of the tree, the pipeline reproduces the 79 generated files byte for byte
   (checked 2026-09-29).
3. Hand-written modules (not touched by the pipeline):
   `QuadraticRootField`, `QuadraticRootIntegrality`,
   `QuadraticRootNormCongruence`, `QuadraticRootConjugation`,
   `ImaginaryRootUnramified` (the √7 leaves for a radicand `d`), `RateCore`,
   `GaloisFixedField`, `FixedBaseBridge`.

## Modules (`UnitDistance.Sqrt241.Geometry.*`)

* Bridge and hand-written: `FixedBaseBridge`, `RateCore`, `GaloisFixedField`,
  `QuadraticRootField`, `QuadraticRootIntegrality`,
  `QuadraticRootNormCongruence`, `QuadraticRootConjugation`,
  `ImaginaryRootUnramified`.
* Entireness chain (generated, radicand `d`): `HeckeSignedArithmetic`,
  `HeckeSignedOddSupport`, `HeckeSignedMellinOrbit`, `HeckeSignedMellinLattice`,
  `HeckeSignedMellinClass`, `HeckeSignedMellinTotal`, `HeckeSignedMellinFinite`,
  `HeckeSignedBochner`, `HeckeSignedMassDifference`,
  `HeckeSignedMellinAgreement`, `HeckeSignedThetaIdentities`,
  `HeckeSignedEntire`, `HeckeQuadraticContinuation`,
  `ImaginaryQuadraticContinuation`.
* Witness, S-integer and tensor chain (generated): `ArithmeticSequence`,
  `WitnessPrimePairs`, `WitnessLocalFunctional`, `WitnessPeriodSeparation`,
  `WitnessFourierConstants`, `LocalOneDimensionalProfiles`,
  `GaussianProfiles`, `GaussianMoments`, `GaussianWindows`, `Student*` (20),
  `Tensor*` (18), `RelativeArithmeticAmplitude`, `RelativeFieldEnergy`,
  `RelativeFieldProfile`, `RelativeWitnessAmplitude`, `SInteger*` (14).

## Rebuild

* `./.toolchain/bin/lake build UnitDistance.Sqrt241.Geometry.FixedBaseBridge`
  builds all 87 modules (≈10 min sequentially from scratch).
* Axioms: a scratch file outside the repository with
  `import UnitDistance.Sqrt241.Geometry.FixedBaseBridge` and
  `#print axioms UnitDistance.Sqrt241.target_of_growing_galois_fields`.
* The copies import `UnitDistance.Sqrt241.Witness`, `Target`,
  `FiniteFunctionalArithmetic` and `FiniteCertificates.Data`; rebuild after
  changes there. If the witness data change (types, `periodPower`, `logRD`),
  rerun the pipeline and recheck the period-separation proofs and `29/32`.

## Open items

* `hmargin` is a hypothesis (A1 proves it; wiring at assembly).
* All other hypotheses (`M`, `r3`, `ii`, `hdiscM`, `hfinite`, the family `Ks`
  with its local types, freeness and index) are for streams B–E.

## Log

* 2026-09-29 08:20. Taint analysis, generator; entireness chain generalized
  to a radicand `d` and built.
* 2026-09-29 ≈09:10. A1 changed `Witness.s` to the manuscript value. The base
  of the taint analysis was widened to every constant of the module
  `UnitDistance.Witness` (lemmas about `a`, `bernsteinCoefficients`,
  `polynomial` are copied as well: +40 declarations, +3 modules), and
  attributed private lemmas are kept. All 87 modules build; final theorem
  proved; axioms standard.
