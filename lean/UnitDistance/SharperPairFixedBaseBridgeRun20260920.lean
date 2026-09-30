module

public import UnitDistance.ArithmeticSequence
public import UnitDistance.SIntegerWitnessGraph
public import UnitDistance.RelativeResidueFixedBase
public import UnitDistance.ImaginaryQuadraticContinuation
public import UnitDistance.GaloisRetainedFamily
public import UnitDistance.GaloisFixedArithmetic
public import UnitDistance.WitnessPrimePairs
public import UnitDistance.RationalGaloisAlgebra
public import UnitDistance.SigmaCutFamilyRamification
public import UnitDistance.SigmaCutFamilyPrimeFreedom
public import UnitDistance.SigmaCutUnconditional
public import UnitDistance.SharperPairArithmeticRateCoreRun20260920
public import UnitDistance.RetainedDyadicDifferentComplement

@[expose] public section
set_option backward.privateInPublic true


/-!
# Sharper-pair bridge to a relaxed fixed-base ceiling

This research module keeps the selected endpoint sources unchanged.  The
already proved sharper pair-functional margin can absorb an extra `4e-6` in
the fixed-base residue ceiling.  Because the fixed-base hypothesis is strict,
the proof applies residue inheritance at the midpoint between the actual
fixed-base value and the relaxed terminal threshold; the remaining midpoint
gap is a fixed positive exponential growth rate.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

open NumberField NumberField.InfinitePlace Filter
open scoped Classical BigOperators

namespace UnitDistance
open NumberFieldAnalysis Witness

namespace SIntegerCRT
open RelativeIdealCosets RelativeUnits NumberFieldAnalysis Witness

/-- A family with residue cap `U` reaches the target whenever `U` is below
the relaxed terminal threshold.  The sharper pair bound is internal. -/
theorem target_of_witnessFields_of_sharperPair_residueCap_run20260920
    (Fs Ks : ℕ → Type) (Ss : ℕ → Type*)
    [∀ j, Field (Fs j)] [∀ j, Field (Ks j)]
    [∀ j, NumberField (Fs j)] [∀ j, NumberField (Ks j)]
    [∀ j, Algebra (Fs j) (Ks j)]
    [∀ j, Algebra.IsQuadraticExtension (Fs j) (Ks j)]
    [∀ j, IsTotallyComplex (Ks j)] [∀ j, Fintype (Ss j)]
    (ι : (j : ℕ) → Ks j ≃ₐ[Fs j] Ks j)
    (D : (j : ℕ) → PrimePairFamily (ι j) (Ss j)) (v : (j : ℕ) → Ss j → Fin 11)
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Fs j)) atTop atTop)
    (hunr : ∀ᶠ j in atTop, FiniteUnramified (Fs j) (Ks j))
    (hι : ∀ᶠ j in atTop, ι j ≠ 1)
    (hb : ∀ᶠ j in atTop, 0 < nrRealPlaces (Fs j))
    (hQ : ∀ᶠ j in atTop, ∀ s,
      (Ideal.absNorm ((D j).prime (s, false)).asIdeal : ℝ) = residueCard (v j s))
    (hmultiplicity : ∀ᶠ j in atTop, ∀ a,
      (Fintype.card {s // v j s = a} : ℝ) *
        ((ramification a : ℝ) * residueDegree a) = Module.finrank ℚ (Fs j))
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Fs j)) ≤ logRD)
    (U : ℝ)
    (hresidue : ∀ᶠ j in atTop,
      Real.log (relativeResidue (Ks j) (Fs j)) /
        (Module.finrank ℚ (Fs j) : ℝ) ≤ U)
    (hsignature : ∀ᶠ j in atTop, thetaMin ≤ signatureRatio (Fs j))
    (hU : U < sharperFixedBaseCeilingRun20260920) : Target := by
  have hd : Tendsto (fun j => (Module.finrank ℚ (Fs j) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdegree
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hlarge : ∀ᶠ j in atTop,
      4 * mixedEnergyVarianceConstant ≤
        epsilon^2 * (Module.finrank ℚ (Fs j) : ℝ) := by
    filter_upwards [tendsto_atTop.mp hd
      (4 * mixedEnergyVarianceConstant / epsilon^2)] with j hj
    have h := (div_le_iff₀ (sq_pos_of_pos hepsilon)).mp hj
    simpa only [mul_comm] using h
  apply target_of_eventual_exponential_graphs _ hd
    (sub_pos.mpr hU) (show 0 < (2 : ℝ)^(3 + increment) by positivity)
  filter_upwards [hunr, hι, hb, hQ, hmultiplicity, hdisc, hresidue,
    hsignature, hlarge] with j hu hi hb hq hm hdiscj hres hs hl
  obtain ⟨V, _, hV⟩ := witnessSInteger_exponential_graph hu hi hb (D j) (v j)
    hq hm hdiscj (show 0 < epsilon by norm_num [epsilon]) hl
  refine ⟨V, le_trans ?_ hV⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (degree_pos_real (F := Fs j)).le
  exact sharperFixedBaseGap_le_arithmeticRate_run20260920
    (F := Fs j) (K := Ks j) hdiscj hres hs

/-- Fixed-base inheritance at a strict midpoint converts the full relaxed
`4e-6` threshold into a positive uniform family rate. -/
theorem target_of_witnessFields_entire_sharperFixedBase_run20260920
    (M : Type*) [Field M] [NumberField M]
    (Fs Ks : ℕ → Type) (Ss : ℕ → Type*)
    [∀ j, Field (Fs j)] [∀ j, Field (Ks j)]
    [∀ j, NumberField (Fs j)] [∀ j, NumberField (Ks j)]
    [∀ j, Algebra (Fs j) (Ks j)] [∀ j, Algebra M (Ks j)]
    [∀ j, Algebra.IsQuadraticExtension (Fs j) (Ks j)]
    [∀ j, IsTotallyComplex (Ks j)] [∀ j, Fintype (Ss j)]
    (ι : (j : ℕ) → Ks j ≃ₐ[Fs j] Ks j)
    (D : (j : ℕ) → PrimePairFamily (ι j) (Ss j)) (v : (j : ℕ) → Ss j → Fin 11)
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Fs j)) atTop atTop)
    (hunr : ∀ᶠ j in atTop, FiniteUnramified (Fs j) (Ks j))
    (hι : ∀ᶠ j in atTop, ι j ≠ 1)
    (hb : ∀ᶠ j in atTop, 0 < nrRealPlaces (Fs j))
    (hQ : ∀ᶠ j in atTop, ∀ s,
      (Ideal.absNorm ((D j).prime (s, false)).asIdeal : ℝ) = residueCard (v j s))
    (hmultiplicity : ∀ᶠ j in atTop, ∀ a,
      (Fintype.card {s // v j s = a} : ℝ) *
        ((ramification a : ℝ) * residueDegree a) = Module.finrank ℚ (Fs j))
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Fs j)) ≤ logRD)
    (hentire : ∀ᶠ j in atTop, ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ z : ℂ, 1 < z.re →
        completedZetaRight (Ks j) z = completedZetaRight (Fs j) z * L z)
    (hfinite : fixedBaseResidueCeiling M logRD (1 / 12000) <
      sharperFixedBaseCeilingRun20260920)
    (hsignature : ∀ᶠ j in atTop, thetaMin ≤ signatureRatio (Fs j)) : Target := by
  have hquad : ∀ j, Module.finrank (Fs j) (Ks j) = 2 := fun j =>
    Algebra.IsQuadraticExtension.finrank_eq_two (Fs j) (Ks j)
  have hdegreeK : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop := by
    apply tendsto_atTop_mono _ hdegree
    intro j
    have hd := Module.finrank_mul_finrank ℚ (Fs j) (Ks j)
    rw [hquad] at hd
    omega
  have hdiscK : ∀ᶠ j in atTop,
      Real.log (rootDiscriminant (Ks j)) ≤ logRD := by
    filter_upwards [hunr, hdisc] with j hu hd
    rwa [rootDiscriminant_eq_of_finiteUnramified (Fs j) (Ks j) hu]
  have hcomp : ∀ eta : ℝ, 0 < eta → ∀ᶠ j in atTop,
      relativeCompletedReal (Ks j) (Fs j) logRD 1 ≤
        relativeCompletedReal (Ks j) (Fs j) logRD (1 + eta) := by
    intro eta heta
    filter_upwards [hunr, hdisc, hentire] with j hu hd hL
    obtain ⟨L, hL, hfactor⟩ := hL
    exact relativeCompletedReal_monotoneOn_of_unramified_entire_factor
      (Ks j) (Fs j) (hquad j) hu hL hfactor hd
      (by simp) (by change 1 ≤ 1 + eta; linarith) (by linarith)
  let X : ℝ := fixedBaseResidueCeiling M logRD (1 / 12000)
  let U : ℝ := (X + sharperFixedBaseCeilingRun20260920) / 2
  have hXU : X < U := by dsimp only [X, U]; linarith
  have hUT : U < sharperFixedBaseCeilingRun20260920 := by
    dsimp only [X, U] at hfinite ⊢
    linarith
  have hresidue := eventual_normalized_log_relativeResidue_lt_of_fixed_base
    M Ks Fs hquad hdegreeK
    (Eventually.of_forall fun j => IsTotallyComplex.nrRealPlaces_eq_zero (Ks j))
    (by norm_num : (0 : ℝ) < 1 / 12000) hdiscK hcomp hXU
  exact target_of_witnessFields_of_sharperPair_residueCap_run20260920
    Fs Ks Ss ι D v hdegree hunr hι hb hQ hmultiplicity hdisc U
    (hresidue.mono fun _ h => h.le) hsignature hUT

end SIntegerCRT

namespace SIntegerCRT
open RelativeIdealCosets RelativeUnits NumberFieldAnalysis Witness
open GaloisQuotient ArithmeticRetained

/-- The Galois fixed-field construction, separated from the profinite-level
transport so that each kernel term remains small enough to elaborate
independently. -/
theorem target_of_growing_retained_galois_fields_sharperFixedBase_run20260920
    (Ks : ℕ → Type) [∀ j, Field (Ks j)] [∀ j, NumberField (Ks j)]
    [∀ j, IsGalois ℚ (Ks j)] [∀ j, Algebra RetainedField (Ks j)]
    (φ : ∀ j, Ks j →+* ℂ) (c : ∀ j, Gal(Ks j/ℚ))
    (hc : ∀ j, NumberField.ComplexEmbedding.IsConj (φ j) (c j))
    (hc1 : ∀ j, c j ≠ 1)
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop)
    (hunrM : ∀ᶠ j in atTop, FiniteUnramified RetainedField (Ks j))
    (he : ∀ᶠ j in atTop, ∀ a : Fin 11,
      (rationalPrimeIdeal (primes a)).ramificationIdxIn
        (𝓞 (Ks j)) = ramification a)
    (hf : ∀ᶠ j in atTop, ∀ a : Fin 11,
      (rationalPrimeIdeal (primes a)).inertiaDegIn
        (𝓞 (Ks j)) = residueDegree a)
    (hfree : ∀ᶠ j in atTop, ∀ a : Fin 11,
      ∀ P : PrimeNormFiber (Ks j) (primeNorm a),
        Ideal.map (RingOfIntegers.mapRingHom (c j).toRingHom)
          P.1.asIdeal ≠ P.1.asIdeal)
    (hindex : ∀ᶠ j in atTop,
      4096 ≤ (Subgroup.centralizer (Set.singleton (c j))).index)
    (hdiscM : Real.log (rootDiscriminant RetainedField) ≤ logRD)
    (hfinite : fixedBaseResidueCeiling RetainedField logRD (1 / 12000) <
      sharperFixedBaseCeilingRun20260920) : Target := by
  let Fs : ℕ → Type := fun j => GaloisConjugation.fixedField (Ks j) (c j)
  letI : ∀ j, Algebra (Fs j) (Ks j) := fun _ => by
    dsimp only [Fs]
    infer_instance
  letI : ∀ j, Algebra.IsQuadraticExtension (Fs j) (Ks j) := fun j =>
    GaloisConjugation.fixedFieldQuadratic (φ j) (c j) (hc j) (hc1 j)
  letI : ∀ j, IsTotallyComplex (Ks j) := fun _ =>
    GaloisConjugation.totallyComplex_of_retained
  let ι : ∀ j, Ks j ≃ₐ[Fs j] Ks j := fun j =>
    GaloisConjugation.fixedAutomorphism (c j)
  have hι : ∀ j, ι j ≠ 1 := fun j =>
    GaloisConjugation.fixedAutomorphism_ne_one (c j) (hc1 j)
  let Ss : ℕ → Type := fun j => ActualPrimePairIndex (ι j) (hι j)
  let D : ∀ j, PrimePairFamily (ι j) (Ss j) := fun j => actualPrimePairs (ι j) (hι j)
  let v : ∀ j, Ss j → Fin 11 := fun _ s => s.1
  have hdegreeF : Tendsto (fun j => Module.finrank ℚ (Fs j)) atTop atTop :=
    GaloisConjugation.fixedField_degree_tendsto Ks φ c hc hc1 hdegree
  have hunr : ∀ᶠ j in atTop, FiniteUnramified (Fs j) (Ks j) :=
    Eventually.of_forall fun j =>
      GaloisConjugation.fixedField_finiteUnramified (φ j) (c j)
        (hc j) (hc1 j)
  have hb : ∀ᶠ j in atTop, 0 < nrRealPlaces (Fs j) :=
    Eventually.of_forall fun j =>
      GaloisConjugation.nrRealPlaces_pos (φ j) (c j) (hc j)
  have hQ : ∀ᶠ j in atTop, ∀ s,
      (Ideal.absNorm ((D j).prime (s, false)).asIdeal : ℝ) = residueCard (v j s) :=
    Eventually.of_forall fun j s => actualPrimePairs_norm (ι j) (hι j) s
  have hmultiplicity : ∀ᶠ j in atTop, ∀ a,
      (Fintype.card {s // v j s = a} : ℝ) *
        ((ramification a : ℝ) * residueDegree a) = Module.finrank ℚ (Fs j) := by
    filter_upwards [he, hf, hfree] with j hje hjf hjfree
    intro a
    exact actualPrimePairs_multiplicity (ι j) (hι j) a
      (hje a) (hjf a) (hjfree a)
  have hdisc : ∀ᶠ j in atTop,
      Real.log (rootDiscriminant (Fs j)) ≤ logRD := by
    filter_upwards [hunrM] with j hj
    change Real.log (rootDiscriminant
      (GaloisConjugation.fixedField (Ks j) (c j))) ≤ logRD
    rw [GaloisConjugation.fixedField_rootDiscriminant_eq
      (φ j) (c j) (hc j) (hc1 j) hj]
    exact hdiscM
  have hr : ∀ᶠ j in atTop, ∃ r : Fs j, r^2 = 7 := by
    filter_upwards [hb] with j hj
    exact QuadraticSeven.exists_root_of_positive_real_places hj
      (ArithmeticRetained.sevenRootIn (Ks j))
      (ArithmeticRetained.sevenRootIn_sq (Ks j))
      (Algebra.IsQuadraticExtension.finrank_eq_two (Fs j) (Ks j))
  have hi : ∀ᶠ j in atTop, ∃ z : Ks j, z^2 = -1 :=
    Eventually.of_forall fun j =>
      ⟨ArithmeticRetained.imaginaryUnitIn (Ks j),
        ArithmeticRetained.imaginaryUnitIn_sq (Ks j)⟩
  have hentire : ∀ᶠ j in atTop, ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ z : ℂ, 1 < z.re →
        completedZetaRight (Ks j) z = completedZetaRight (Fs j) z * L z := by
    filter_upwards [hunr, hb, hr, hi] with j hu hbj hrj hij
    obtain ⟨r, hrj⟩ := hrj
    obtain ⟨ii, hij⟩ := hij
    obtain ⟨L, hL, hfactor⟩ := exists_entire_relative_factor_of_imaginary_quadratic
      (Fs j) (Ks j) r hrj hbj ii hij
      (Algebra.IsQuadraticExtension.finrank_eq_two (Fs j) (Ks j)) hu
    exact ⟨L, hL, fun z hz =>
      rightHalfPlaneFactor_of_entireFactor (Fs j) (Ks j) hfactor hz⟩
  have hsignature : ∀ᶠ j in atTop, thetaMin ≤ signatureRatio (Fs j) := by
    filter_upwards [hindex] with j hj
    exact GaloisConjugation.fixedField_signature_lower
      (φ j) (c j) (hc j) (hc1 j) hj
  exact target_of_witnessFields_entire_sharperFixedBase_run20260920
    RetainedField Fs Ks Ss ι D v hdegreeF hunr
    (Eventually.of_forall hι) hb hQ hmultiplicity hdisc hentire hfinite hsignature

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [T2Space Q] [CompactSpace Q] [TotallyDisconnectedSpace Q] [Infinite Q]
variable (ρ : Gal(Ω/ℚ) →ₜ* Q) (hρ : Function.Surjective ρ)
variable (e : RetainedField →ₐ[ℚ] Ω)
variable {C : Type} [Group C] [Fintype C] [TopologicalSpace C] [DiscreteTopology C]
variable (χ : Gal(Ω/ℚ) →ₜ* C)
variable (hM : ρ.toMonoidHom.ker ≤ e.fieldRange.fixingSubgroup)
variable (hχ : ρ.toMonoidHom.ker ≤ χ.toMonoidHom.ker)

/-- The existing retained-level construction, with all local and signature
facts unchanged, feeds the midpoint fixed-base theorem. -/
theorem target_of_infinite_retained_quotient_sharperFixedBase_run20260920
    (hχsurj : Function.Surjective χ) (Φ : Ω →+* ℂ) (c : Gal(Ω/ℚ))
    (hc : NumberField.ComplexEmbedding.IsConj Φ c)
    (hindex : 4096 ≤ (Subgroup.centralizer ({χ c} : Set C)).index)
    (hunrM : ∀ᶠ j in atTop,
      FiniteUnramified RetainedField (retainedLevel ρ hρ e χ hM hχ j))
    (he : ∀ᶠ j in atTop, ∀ a : Fin 11,
      (rationalPrimeIdeal (primes a)).ramificationIdxIn
        (𝓞 (retainedLevel ρ hρ e χ hM hχ j)) = ramification a)
    (hf : ∀ᶠ j in atTop, ∀ a : Fin 11,
      (rationalPrimeIdeal (primes a)).inertiaDegIn
        (𝓞 (retainedLevel ρ hρ e χ hM hχ j)) = residueDegree a)
    (hfree : ∀ᶠ j in atTop, ∀ a : Fin 11,
      ∀ P : PrimeNormFiber (retainedLevel ρ hρ e χ hM hχ j) (primeNorm a),
      Ideal.map (RingOfIntegers.mapRingHom
        (retainedLevelConjugation ρ hρ e χ hM hχ c j).toRingHom)
          P.1.asIdeal ≠ P.1.asIdeal)
    (hdiscM : Real.log (rootDiscriminant RetainedField) ≤ logRD)
    (hfinite : fixedBaseResidueCeiling RetainedField logRD (1 / 12000) <
      sharperFixedBaseCeilingRun20260920) : Target := by
  let Ks : ℕ → Type := fun j => retainedLevel ρ hρ e χ hM hχ j
  let φ : ∀ j, Ks j →+* ℂ := retainedLevelEmbedding ρ hρ e χ hM hχ Φ
  let E (j : ℕ) := @RationalGalois.autEquiv (Ks j) _
    (retainedLevel_algebra ρ hρ e χ hM hχ j) DivisionRing.toRatAlgebra
  let cN (j : ℕ) := E j (retainedLevelConjugation ρ hρ e χ hM hχ c j)
  letI : ∀ j, @IsGalois ℚ _ (Ks j) _ DivisionRing.toRatAlgebra := fun j => by
    have hG : @IsGalois ℚ _ (Ks j) _
        (retainedLevel_algebra ρ hρ e χ hM hχ j) := by
      exact retainedLevel_galois ρ hρ e χ hM hχ j
    exact RationalGalois.isGalois (Ks j)
      (retainedLevel_algebra ρ hρ e χ hM hχ j)
      DivisionRing.toRatAlgebra hG
  have hconj : ∀ j, @NumberField.ComplexEmbedding.IsConj
      (Ks j) _ ℚ _ DivisionRing.toRatAlgebra (φ j) (cN j) := by
    intro j
    change ComplexEmbedding.conjugate _ = _
    apply RingHom.ext
    intro x
    change star (retainedLevelEmbedding ρ hρ e χ hM hχ Φ j x) =
      retainedLevelEmbedding ρ hρ e χ hM hχ Φ j (cN j x)
    have hx : cN j x = retainedLevelConjugation ρ hρ e χ hM hχ c j x :=
      RationalGalois.autEquiv_apply _ _ _ _ _
    rw [hx]
    exact (retainedLevel_isConj ρ hρ e χ hM hχ Φ c hc j).eq x |>.symm
  have hcN1 : ∀ j, cN j ≠ 1 := by
    intro j heq
    apply retainedLevel_conjugation_ne_one ρ hρ e χ hM hχ Φ c hc j
    exact (E j).injective (heq.trans (E j).map_one.symm)
  have hdegreeK : Tendsto (fun j =>
      @Module.finrank ℚ (Ks j) _ _
        (@Algebra.toModule ℚ (Ks j) _ _ DivisionRing.toRatAlgebra))
      atTop atTop := by
    convert retainedLevel_degree_tendsto ρ hρ e χ hM hχ using 1
    funext j
    exact (RationalGalois.finrank_eq (Ks j)
      (retainedLevel_algebra ρ hρ e χ hM hχ j)
      DivisionRing.toRatAlgebra).symm
  have hfreeN : ∀ᶠ j in atTop, ∀ a : Fin 11,
      ∀ P : PrimeNormFiber (Ks j) (primeNorm a),
        Ideal.map (RingOfIntegers.mapRingHom (cN j).toRingHom)
          P.1.asIdeal ≠ P.1.asIdeal := by
    filter_upwards [hfree] with j hj
    intro a P
    have heq : (cN j).toRingHom =
        (retainedLevelConjugation ρ hρ e χ hM hχ c j).toRingHom := by
      apply RingHom.ext
      intro x
      exact RationalGalois.autEquiv_apply _ _ _ _ _
    rw [heq]
    exact hj a P
  have hindexN : ∀ᶠ j in atTop,
      4096 ≤ (Subgroup.centralizer (Set.singleton (cN j))).index := by
    apply Eventually.of_forall
    intro j
    have h0 := retainedLevel_conjugacy_index ρ hρ e χ hM hχ hχsurj c hindex j
    have h1 := GaloisConjugation.centralizer_index_le_of_surjective
      (E j).symm.toMonoidHom (E j).symm.surjective (cN j)
    dsimp only [cN] at h1
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h1
    exact h0.trans h1
  exact target_of_growing_retained_galois_fields_sharperFixedBase_run20260920
    Ks φ cN hconj hcN1 hdegreeK hunrM he hf hfreeN hindexN hdiscM hfinite

end SIntegerCRT

namespace ArithmeticProP.SigmaCut
open NumberFieldAnalysis Witness SIntegerCRT ArithmeticRetained GaloisQuotient

/-- Terminal presentation theorem with the genuinely weaker fixed-base scalar
hypothesis. -/
theorem target_of_arithmeticPresentation_sharperFixedBase_run20260920
    (hgen : ArithmeticPresentation)
    (hdiscM : Real.log (rootDiscriminant RetainedField) ≤ logRD)
    (hfinite : fixedBaseResidueCeiling RetainedField logRD (1 / 12000) <
      sharperFixedBaseCeilingRun20260920) : Target := by
  letI : Infinite ActualQuotient := infinite_of_arithmeticPresentation hgen
  apply target_of_infinite_retained_quotient_sharperFixedBase_run20260920
    (arithmeticProjection actualExtra hgen)
    (arithmeticProjection_surjective actualExtra hgen)
    retainedFieldEmbeddingMaximalSigmaProTwo (arithmeticCubic hgen)
    (arithmeticProjection_retained_kernel hgen) (arithmeticCubic_kernel hgen)
    (arithmeticCubic_surjective hgen) sigmaComplexEmbedding sigmaComplexConjugation
    sigmaComplexConjugation_isConj (arithmeticCubic_conjugacy_index hgen)
    ?_ ?_ ?_ ?_ hdiscM hfinite
  · exact Eventually.of_forall (level_finiteUnramified_retained hgen)
  · exact Eventually.of_forall fun j a => (level_ramification_residue hgen j a).1
  · exact Eventually.of_forall fun j a => (level_ramification_residue hgen j a).2
  · exact Eventually.of_forall fun j a P => level_prime_moved hgen j a P

end ArithmeticProP.SigmaCut

/-- Canonical one-hypothesis endpoint.  All pair, dyadic, presentation, local,
and signature inputs are discharged internally. -/
theorem target_of_retained_fixedBaseCeiling_sharperPair_run20260920
    (hfinite : fixedBaseResidueCeiling ArithmeticRetained.RetainedField logRD
      (1 / 12000) < sharperFixedBaseCeilingRun20260920) : Target := by
  apply ArithmeticProP.SigmaCut.target_of_arithmeticPresentation_sharperFixedBase_run20260920
    ArithmeticProP.SigmaCut.arithmetic_presentation
  · have hcanon :=
      CanonicalRetained.log_rootDiscriminant_le_logRD_of_relativeDifferentTwoExponent
        ArithmeticRetained.retainedRelativeDifferentTwoExponent_le
    simpa only [rootDiscriminant_eq_of_algEquiv CanonicalRetained.equiv] using hcanon
  · exact hfinite

end UnitDistance
