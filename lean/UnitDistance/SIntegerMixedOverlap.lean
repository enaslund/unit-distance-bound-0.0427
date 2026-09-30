module

public import UnitDistance.SIntegerMixedInvariance
public import UnitDistance.SIntegerReferenceFiniteSteps
public import UnitDistance.SIntegerWitnessVertices
public import UnitDistance.TensorMixedLabels

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual S-integer field overlaps equal the canonical mixed overlap -/

noncomputable section
set_option synthInstance.maxSize 512
open Set MeasureTheory NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped Classical BigOperators ENNReal nonZeroDivisors

namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeUnits Local.ValuedHaar Witness

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

local instance overlapLocalMeasurableSpace (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance overlapLocalBorelSpace (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

def witnessUnitDirection (D : PrimePairFamily ι S) (s : S) :
    ValuationOneUnits (WitnessLocalType D s) := ⟨1, map_one _⟩

def witnessOverlapProfile (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (T : ℝ) (n : S → ℤ) (u : PairPlaceIndex F → ℝ) : ℝ≥0∞ :=
  mixedCanonicalOverlap (β := RealPlaceIndex F) v (witnessPairHaar D)
    (witnessPairBallSystem D v hQ) (witnessPairSteps D v hQ) (witnessUnitDirection D) T n u

theorem measurable_witnessOverlapProfile (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (T : ℝ) (n : S → ℤ) : Measurable (witnessOverlapProfile D v hQ T n) :=
  measurable_mixedCanonicalOverlap v (witnessPairHaar D) (witnessPairBallSystem D v hQ)
    (witnessPairSteps D v hQ) (fun s n => reciprocalSteps_measurable (WitnessLocalType D s) n)
    (witnessUnitDirection D) T n

theorem witnessOverlapProfile_eq_zero (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (T : ℝ) (n : S → ℤ) (hn : n ∉ finiteValuationLabels v) (u : PairPlaceIndex F → ℝ) :
    witnessOverlapProfile D v hQ T n u = 0 :=
  mixedCanonicalOverlap_eq_zero v (witnessPairHaar D) (witnessPairBallSystem D v hQ)
    (witnessPairSteps D v hQ) (witnessUnitDirection D) T n hn u

/-- Arbitrary actual completion units yield exactly the same overlap. -/
theorem witnessMixed_overlap_unit_direction (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (T : ℝ) (n : S → ℤ) (u : PairPlaceIndex F → ℝ)
    (a : (s : S) → ValuationOneUnits (WitnessLocalType D s)) :
    mixedPositionMeasure (witnessPairHaar D)
      (overlapSet
        (supportedWindow (mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
          (mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T)
        (mixedStep (β := RealPlaceIndex F) v (witnessPairHaar D) (witnessPairBallSystem D v hQ)
          (witnessPairSteps D v hQ) (u, fun s => (n s, a s)))) =
      witnessOverlapProfile D v hQ T n u := by
  apply witnessMixed_overlap_eq_of_norm_valuation_eq
  · intro i; rfl
  · intro j; rfl
  · intro j; rfl
  · intro s
    change intValuation (WitnessLocalType D s) (uniformizer (WitnessLocalType D s) ^ (n s)*(a s : WitnessLocalType D s)) =
      intValuation (WitnessLocalType D s) (uniformizer (WitnessLocalType D s) ^ (n s)*1)
    rw [map_mul, (a s).property, mul_one, mul_one]
  · intro s
    change intValuation (WitnessLocalType D s) (uniformizer (WitnessLocalType D s) ^ (-(n s))*(a s : WitnessLocalType D s)⁻¹) =
      intValuation (WitnessLocalType D s) (uniformizer (WitnessLocalType D s) ^ (-(n s))*1⁻¹)
    simp only [map_mul, map_inv₀, (a s).property, inv_one, mul_one]

/-- Simultaneous actual reference normalization and relative archimedean deformation. -/
def witnessNormalizedCoordinates (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (n₀ : S → ℤ) (h : PairPlaceIndex F → ℝ) :
    (EuclideanIdeal.Space K × LocalProduct D.prime) ≃+ WitnessMixedPosition D :=
  ((EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)).toAddEquiv.prodCongr
    (referenceRescaling D n₀)).trans (witnessMixedCoordinates hι D)

theorem witnessNormalizedCoordinates_measurePreserving (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (n₀ : S → ℤ) (h : PairPlaceIndex F → ℝ) :
    MeasurePreserving (witnessNormalizedCoordinates hι D n₀ h) (semiLocalHaar D.prime)
      (mixedPositionMeasure (witnessPairHaar D)) :=
  (witnessMixedCoordinates_measurePreserving hι D).comp
    ((reciprocalDeformation_measurePreserving ι hι h).prod
      (referenceRescaling_measurePreserving D n₀))

theorem witnessNormalizedCoordinates_window (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (n₀ : S → ℤ) (h : PairPlaceIndex F → ℝ) (T : ℝ) :
    witnessNormalizedCoordinates hι D n₀ h ⁻¹'
      supportedWindow (mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
        (mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T =
      witnessDeformedWindow hι D v n₀ T h := by
  ext x
  have hx := congrArg (fun A => witnessDeformation hι D h x ∈ A)
    (witnessSAdicWindow_referenceRescaling hι D v hQ n₀ T)
  have hy := congrArg (fun A => semiLocalReferenceRescaling D n₀ (witnessDeformation hι D h x) ∈ A)
    (witnessMixedCoordinates_window hι D v hQ T)
  exact (hy.trans hx).to_iff

/-- No formal local displacement is assumed here: every input displacement
is the image of the stated actual norm-one field element. -/
theorem witnessSAdic_field_overlap_eq (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (n₀ n : S → ℤ) (h : PairPlaceIndex F → ℝ) (T : ℝ)
    (z : K) (hz : Algebra.norm F z = 1)
    (hv : ∀ s, (D.prime (s, false)).valuation K z = WithZero.exp (-(n s-n₀ s))) :
    semiLocalHaar D.prime
      (overlapSet (witnessDeformedWindow hι D v n₀ T h)
        (EuclideanIdeal.embedding K z, localEmbedding D.prime z)) =
      witnessOverlapProfile D v hQ T n (elementDifferenceLog ι z-h) := by
  let e := witnessNormalizedCoordinates hι D n₀ h
  let δ : EuclideanIdeal.Space K × LocalProduct D.prime :=
    (EuclideanIdeal.embedding K z, localEmbedding D.prime z)
  let W := supportedWindow
    (mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
    (mixedPositionEnergy (β := RealPlaceIndex F) (γ := PairPlaceIndex F)
      v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T
  have hW : MeasurableSet W := measurableSet_supportedWindow
    (measurableSet_mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
    (measurable_mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T
  have hpre : e ⁻¹' overlapSet W (e δ) =
      overlapSet (witnessDeformedWindow hι D v n₀ T h) δ := by
    rw [← witnessNormalizedCoordinates_window hι D v hQ n₀ h T]
    ext x
    change (e x ∈ W ∧ e x+e δ ∈ W) ↔ (e x ∈ W ∧ e (x+δ) ∈ W)
    rw [map_add]
  have hO : MeasurableSet (overlapSet W (e δ)) :=
    hW.inter (hW.preimage (measurable_id.add_const (e δ)))
  rw [← hpre, (witnessNormalizedCoordinates_measurePreserving hι D n₀ h).measure_preimage
    hO.nullMeasurableSet]
  obtain ⟨a, ha⟩ := referenceFiniteStep_of_normOne hι D v hQ n₀ n z hz hv
  have hfin : (e δ).2 = fun s => (witnessPairSteps D v hQ s).step (n s) (a s) := ha
  trans mixedPositionMeasure (witnessPairHaar D) (overlapSet W
    (mixedStep (β := RealPlaceIndex F) v (witnessPairHaar D) (witnessPairBallSystem D v hQ)
      (witnessPairSteps D v hQ) (elementDifferenceLog ι z-h, fun s => (n s, a s))))
  · apply witnessMixed_overlap_eq_of_norm_valuation_eq
    · intro i
      change ‖(EuclideanIdeal.tensorCoordinates K (relativePlaceGrouping ι hι)
        (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h) (EuclideanIdeal.embedding K z))).1 i‖ = ‖(1:ℂ)‖
      rw [EuclideanIdeal.tensorCoordinates_singleton, norm_one]
      exact reciprocal_compact_modulus ι hι h hz i
    · intro j
      change ‖((EuclideanIdeal.tensorCoordinates K (relativePlaceGrouping ι hι)
        (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h) (EuclideanIdeal.embedding K z))).2 j).1‖ =
          ‖(Real.exp ((elementDifferenceLog ι z-h) j) : ℂ)‖
      rw [EuclideanIdeal.tensorCoordinates_pair_fst, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact reciprocal_first_modulus ι hι h hz j
    · intro j
      change ‖((EuclideanIdeal.tensorCoordinates K (relativePlaceGrouping ι hι)
        (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h) (EuclideanIdeal.embedding K z))).2 j).2‖ =
          ‖(Real.exp (-((elementDifferenceLog ι z-h) j)) : ℂ)‖
      rw [EuclideanIdeal.tensorCoordinates_pair_snd, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact reciprocal_second_modulus ι hι h hz j
    · intro s; rw [hfin]; rfl
    · intro s; rw [hfin]; rfl
  · exact witnessMixed_overlap_unit_direction D v hQ T n _ a

end UnitDistance.SIntegerCRT
