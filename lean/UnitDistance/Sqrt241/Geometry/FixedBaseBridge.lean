module

public import UnitDistance.Sqrt241.Geometry.ArithmeticSequence
public import UnitDistance.Sqrt241.Geometry.SIntegerWitnessGraph
public import UnitDistance.Sqrt241.Geometry.RateCore
public import UnitDistance.Sqrt241.Geometry.GaloisFixedField
public import UnitDistance.Sqrt241.Geometry.WitnessPrimePairs
public import UnitDistance.Sqrt241.Geometry.ImaginaryQuadraticContinuation
public import UnitDistance.RelativeResidueFixedBase
public import UnitDistance.RelativeHeckeRightHalfPlane
public import UnitDistance.HeckeQuadraticContinuation
public import UnitDistance.GaloisConjugationFixedField

@[expose] public section
set_option backward.privateInPublic true


/-!
# Fixed-base bridge for the tower over `ℚ(√241)`

Copy of the first three theorems of
`UnitDistance.SharperPairFixedBaseBridgeRun20260920` for the witness
`UnitDistance.Sqrt241.Witness` (five local types). Differences from the ℚ
bridge:

* the threshold is `Witness.ceiling` itself; the positivity of the margin over
  the signature range is the explicit hypothesis `hmargin` instead of the
  internally proved sharper pair margin with its `4e-6` allowance;
* the fixed base is an arbitrary number field `M` containing `r3² = 3` and
  `ii² = -1` (the ℚ bridge used the retained field with `√7` and `i`); the
  entireness of `ζ_K/ζ_F` uses the radicand `3` in place of `7`;
* the fixed-base parameter is `ε = 1/300` (ℚ: `1/12000`);
* the centralizer index is at least `65536`, giving
  `thetaMin = 65535/131072`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open NumberField NumberField.InfinitePlace Filter
open scoped Classical BigOperators

namespace UnitDistance.Sqrt241

namespace SIntegerCRT
open UnitDistance.RelativeIdealCosets UnitDistance.RelativeUnits UnitDistance.NumberFieldAnalysis

/-- A family with residue cap `U` reaches the target whenever `U` is below
the threshold `Witness.ceiling` and the margin is positive. -/
theorem target_of_witnessFields_of_residueCap
    (hmargin : ∀ θ : ℝ, Witness.thetaMin ≤ θ →
      0 < Witness.margin θ - 4 * Witness.epsilon)
    (Fs Ks : ℕ → Type) (Ss : ℕ → Type*)
    [∀ j, Field (Fs j)] [∀ j, Field (Ks j)]
    [∀ j, NumberField (Fs j)] [∀ j, NumberField (Ks j)]
    [∀ j, Algebra (Fs j) (Ks j)]
    [∀ j, Algebra.IsQuadraticExtension (Fs j) (Ks j)]
    [∀ j, IsTotallyComplex (Ks j)] [∀ j, Fintype (Ss j)]
    (ι : (j : ℕ) → Ks j ≃ₐ[Fs j] Ks j)
    (D : (j : ℕ) → PrimePairFamily (ι j) (Ss j)) (v : (j : ℕ) → Ss j → Fin 5)
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Fs j)) atTop atTop)
    (hunr : ∀ᶠ j in atTop, FiniteUnramified (Fs j) (Ks j))
    (hι : ∀ᶠ j in atTop, ι j ≠ 1)
    (hb : ∀ᶠ j in atTop, 0 < nrRealPlaces (Fs j))
    (hQ : ∀ᶠ j in atTop, ∀ s,
      (Ideal.absNorm ((D j).prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v j s))
    (hmultiplicity : ∀ᶠ j in atTop, ∀ a,
      (Fintype.card {s // v j s = a} : ℝ) *
        ((Witness.ramification a : ℝ) * Witness.residueDegree a) = Module.finrank ℚ (Fs j))
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Fs j)) ≤ Witness.logRD)
    (U : ℝ)
    (hresidue : ∀ᶠ j in atTop,
      Real.log (relativeResidue (Ks j) (Fs j)) /
        (Module.finrank ℚ (Fs j) : ℝ) ≤ U)
    (hsignature : ∀ᶠ j in atTop, Witness.thetaMin ≤ signatureRatio (Fs j))
    (hU : U < Witness.ceiling) : Target := by
  have hd : Tendsto (fun j => (Module.finrank ℚ (Fs j) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdegree
  have hepsilon : 0 < Witness.epsilon := by norm_num [Witness.epsilon]
  have hlarge : ∀ᶠ j in atTop,
      4 * Witness.mixedEnergyVarianceConstant ≤
        Witness.epsilon^2 * (Module.finrank ℚ (Fs j) : ℝ) := by
    filter_upwards [tendsto_atTop.mp hd
      (4 * Witness.mixedEnergyVarianceConstant / Witness.epsilon^2)] with j hj
    have h := (div_le_iff₀ (sq_pos_of_pos hepsilon)).mp hj
    simpa only [mul_comm] using h
  apply target_of_eventual_exponential_graphs _ hd
    (sub_pos.mpr hU) (show 0 < (2 : ℝ)^(3 + increment) by positivity)
  filter_upwards [hunr, hι, hb, hQ, hmultiplicity, hdisc, hresidue,
    hsignature, hlarge] with j hu hi hb hq hm hdiscj hres hs hl
  obtain ⟨V, _, hV⟩ := witnessSInteger_exponential_graph hu hi hb (D j) (v j)
    hq hm hdiscj hepsilon hl
  refine ⟨V, le_trans ?_ hV⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (degree_pos_real (F := Fs j)).le
  exact Sqrt241.RelativeUnits.fixedBaseGap_le_arithmeticRate hmargin
    (F := Fs j) (K := Ks j) hdiscj hres hs

/-- Fixed-base inheritance at a strict midpoint converts the threshold into a
positive uniform family rate (ε = 1/300). -/
theorem target_of_witnessFields_entire_fixedBase
    (hmargin : ∀ θ : ℝ, Witness.thetaMin ≤ θ →
      0 < Witness.margin θ - 4 * Witness.epsilon)
    (M : Type*) [Field M] [NumberField M]
    (Fs Ks : ℕ → Type) (Ss : ℕ → Type*)
    [∀ j, Field (Fs j)] [∀ j, Field (Ks j)]
    [∀ j, NumberField (Fs j)] [∀ j, NumberField (Ks j)]
    [∀ j, Algebra (Fs j) (Ks j)] [∀ j, Algebra M (Ks j)]
    [∀ j, Algebra.IsQuadraticExtension (Fs j) (Ks j)]
    [∀ j, IsTotallyComplex (Ks j)] [∀ j, Fintype (Ss j)]
    (ι : (j : ℕ) → Ks j ≃ₐ[Fs j] Ks j)
    (D : (j : ℕ) → PrimePairFamily (ι j) (Ss j)) (v : (j : ℕ) → Ss j → Fin 5)
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Fs j)) atTop atTop)
    (hunr : ∀ᶠ j in atTop, FiniteUnramified (Fs j) (Ks j))
    (hι : ∀ᶠ j in atTop, ι j ≠ 1)
    (hb : ∀ᶠ j in atTop, 0 < nrRealPlaces (Fs j))
    (hQ : ∀ᶠ j in atTop, ∀ s,
      (Ideal.absNorm ((D j).prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v j s))
    (hmultiplicity : ∀ᶠ j in atTop, ∀ a,
      (Fintype.card {s // v j s = a} : ℝ) *
        ((Witness.ramification a : ℝ) * Witness.residueDegree a) = Module.finrank ℚ (Fs j))
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Fs j)) ≤ Witness.logRD)
    (hentire : ∀ᶠ j in atTop, ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ z : ℂ, 1 < z.re →
        completedZetaRight (Ks j) z = completedZetaRight (Fs j) z * L z)
    (hfinite : fixedBaseResidueCeiling M Witness.logRD (1 / 300) < Witness.ceiling)
    (hsignature : ∀ᶠ j in atTop, Witness.thetaMin ≤ signatureRatio (Fs j)) : Target := by
  have hquad : ∀ j, Module.finrank (Fs j) (Ks j) = 2 := fun j =>
    Algebra.IsQuadraticExtension.finrank_eq_two (Fs j) (Ks j)
  have hdegreeK : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop := by
    apply tendsto_atTop_mono _ hdegree
    intro j
    have hd := Module.finrank_mul_finrank ℚ (Fs j) (Ks j)
    rw [hquad] at hd
    omega
  have hdiscK : ∀ᶠ j in atTop,
      Real.log (rootDiscriminant (Ks j)) ≤ Witness.logRD := by
    filter_upwards [hunr, hdisc] with j hu hd
    rwa [rootDiscriminant_eq_of_finiteUnramified (Fs j) (Ks j) hu]
  have hcomp : ∀ eta : ℝ, 0 < eta → ∀ᶠ j in atTop,
      relativeCompletedReal (Ks j) (Fs j) Witness.logRD 1 ≤
        relativeCompletedReal (Ks j) (Fs j) Witness.logRD (1 + eta) := by
    intro eta heta
    filter_upwards [hunr, hdisc, hentire] with j hu hd hL
    obtain ⟨L, hL, hfactor⟩ := hL
    exact relativeCompletedReal_monotoneOn_of_unramified_entire_factor
      (Ks j) (Fs j) (hquad j) hu hL hfactor hd
      (by simp) (by change 1 ≤ 1 + eta; linarith) (by linarith)
  let X : ℝ := fixedBaseResidueCeiling M Witness.logRD (1 / 300)
  let U : ℝ := (X + Witness.ceiling) / 2
  have hXU : X < U := by dsimp only [X, U]; linarith
  have hUT : U < Witness.ceiling := by
    dsimp only [X, U] at hfinite ⊢
    linarith
  have hresidue := eventual_normalized_log_relativeResidue_lt_of_fixed_base
    M Ks Fs hquad hdegreeK
    (Eventually.of_forall fun j => IsTotallyComplex.nrRealPlaces_eq_zero (Ks j))
    (by norm_num : (0 : ℝ) < 1 / 300) hdiscK hcomp hXU
  exact target_of_witnessFields_of_residueCap hmargin
    Fs Ks Ss ι D v hdegree hunr hι hb hQ hmultiplicity hdisc U
    (hresidue.mono fun _ h => h.le) hsignature hUT

end SIntegerCRT

open UnitDistance.NumberFieldAnalysis UnitDistance.RelativeIdealCosets UnitDistance.RelativeUnits

/-- **Downstream theorem for the tower over `ℚ(√241)`.** A growing family of
Galois number fields `K_j`, each containing the fixed base `M` (with `√3` and
`√-1`) and unramified over it at all finite primes, with the local types of the
five witness primes, conjugation acting freely on the primes of those norms,
centralizer index at least `2^16`, gives the planar target at exponent
`1.0427`, provided the fixed-base residue ceiling of `M` (ε = 1/300) is below
`Witness.ceiling` and the witness margin is positive. Analogue of
`UnitDistance.SIntegerCRT.target_of_growing_retained_galois_fields_sharperFixedBase_run20260920`. -/
theorem target_of_growing_galois_fields
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
    Target := by
  let Fs : ℕ → Type := fun j => UnitDistance.GaloisConjugation.fixedField (Ks j) (c j)
  let : ∀ j, Algebra (Fs j) (Ks j) := fun _ => by
    dsimp only [Fs]
    infer_instance
  let : ∀ j, Algebra.IsQuadraticExtension (Fs j) (Ks j) := fun j =>
    GaloisConjugation.fixedFieldQuadratic (φ j) (c j) (hc j) (hc1 j)
  have hi : ∀ j, (algebraMap M (Ks j) ii)^2 = -1 := fun j =>
    GaloisConjugation.algebraMap_imaginary_sq ii hii
  let : ∀ j, IsTotallyComplex (Ks j) := fun j =>
    GaloisConjugation.totallyComplex_of_sqrt_neg_one _ (hi j)
  let ι : ∀ j, Ks j ≃ₐ[Fs j] Ks j := fun j =>
    GaloisConjugation.fixedAutomorphism (c j)
  have hι : ∀ j, ι j ≠ 1 := fun j =>
    GaloisConjugation.fixedAutomorphism_ne_one (c j) (hc1 j)
  let Ss : ℕ → Type := fun j => Witness.ActualPrimePairIndex (ι j) (hι j)
  let D : ∀ j, PrimePairFamily (ι j) (Ss j) := fun j =>
    Witness.actualPrimePairs (ι j) (hι j)
  let v : ∀ j, Ss j → Fin 5 := fun _ s => s.1
  have hdegreeF : Tendsto (fun j => Module.finrank ℚ (Fs j)) atTop atTop :=
    UnitDistance.GaloisConjugation.fixedField_degree_tendsto Ks φ c hc hc1 hdegree
  have hunr : ∀ᶠ j in atTop, FiniteUnramified (Fs j) (Ks j) :=
    Eventually.of_forall fun j =>
      GaloisConjugation.fixedField_finiteUnramified (φ j) (c j)
        (hc j) (hc1 j) r3 hr3 ii hii
  have hb : ∀ᶠ j in atTop, 0 < nrRealPlaces (Fs j) :=
    Eventually.of_forall fun j =>
      UnitDistance.GaloisConjugation.nrRealPlaces_pos (φ j) (c j) (hc j)
  have hQ : ∀ᶠ j in atTop, ∀ s,
      (Ideal.absNorm ((D j).prime (s, false)).asIdeal : ℝ) =
        Witness.residueCard (v j s) :=
    Eventually.of_forall fun j s => Witness.actualPrimePairs_norm (ι j) (hι j) s
  have hmultiplicity : ∀ᶠ j in atTop, ∀ a,
      (Fintype.card {s // v j s = a} : ℝ) *
        ((Witness.ramification a : ℝ) * Witness.residueDegree a) =
          Module.finrank ℚ (Fs j) := by
    filter_upwards [he, hf, hfree] with j hje hjf hjfree
    intro a
    exact Witness.actualPrimePairs_multiplicity (ι j) (hι j) a
      (hje a) (hjf a) (hjfree a)
  have hdisc : ∀ᶠ j in atTop,
      Real.log (rootDiscriminant (Fs j)) ≤ Witness.logRD := by
    filter_upwards [hunrM] with j hj
    change Real.log (rootDiscriminant
      (UnitDistance.GaloisConjugation.fixedField (Ks j) (c j))) ≤ Witness.logRD
    rw [GaloisConjugation.fixedField_rootDiscriminant_eq
      (φ j) (c j) (hc j) (hc1 j) r3 hr3 ii hii hj]
    exact hdiscM
  have hentire : ∀ᶠ j in atTop, ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ z : ℂ, 1 < z.re →
        completedZetaRight (Ks j) z = completedZetaRight (Fs j) z * L z := by
    filter_upwards [hunr, hb] with j hu hbj
    have h3 := GaloisConjugation.algebraMap_root_sq (K := Ks j) r3 hr3
    obtain ⟨L, hL, hfactor⟩ :=
      NumberFieldAnalysis.exists_entire_relative_factor_of_imaginary_quadratic
        (Fs j) (Ks j)
        (QuadraticRoot.fixedRoot (φ j) (c j) (hc j) (algebraMap M (Ks j) r3) h3)
        (QuadraticRoot.fixedRoot_sq (φ j) (c j) (hc j) (algebraMap M (Ks j) r3) h3)
        hbj (algebraMap M (Ks j) ii) (hi j)
        (Algebra.IsQuadraticExtension.finrank_eq_two (Fs j) (Ks j)) hu
    exact ⟨L, hL, fun z hz =>
      rightHalfPlaneFactor_of_entireFactor (Fs j) (Ks j) hfactor hz⟩
  have hsignature : ∀ᶠ j in atTop, Witness.thetaMin ≤ signatureRatio (Fs j) := by
    filter_upwards [hindex] with j hj
    exact GaloisConjugation.fixedField_signature_lower
      (φ j) (c j) (hc j) (hc1 j) hj
  exact SIntegerCRT.target_of_witnessFields_entire_fixedBase hmargin
    M Fs Ks Ss ι D v hdegreeF hunr
    (Eventually.of_forall hι) hb hQ hmultiplicity hdisc hentire hfinite hsignature

end UnitDistance.Sqrt241
