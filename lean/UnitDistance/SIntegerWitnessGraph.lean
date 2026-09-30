module

public import UnitDistance.SIntegerWitnessModel
public import UnitDistance.SIntegerWitnessAmbient
public import UnitDistance.SIntegerWitnessConcentration
public import UnitDistance.SIntegerWitnessPeriodSeparation
public import UnitDistance.GeometryConcentratedTransfer
public import UnitDistance.RelativeWitnessAmplitude
public import UnitDistance.IdealRootDiscriminant

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual weighted S-integer unit-distance graphs

All windows, vertices, norm-one steps, unit-log averaging, relative ideal
classes, and measure normalizations are constructed from the stated fields.
The remaining inputs specify the arithmetic prime data and field bounds.
-/

noncomputable section
set_option synthInstance.maxSize 512
open Set MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units IsDedekindDomain
open scoped Classical BigOperators ENNReal nonZeroDivisors
namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeUnits Local.ValuedHaar Witness NumberFieldAnalysis

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

local instance graphLocalMeasurableSpace (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance graphLocalBorelSpace (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

/-- A finite ordinary planar set attaining the actual weighted-shell
arithmetic amplitude. No geometric model or edge bound is assumed. -/
theorem witnessSInteger_arithmetic_graph (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (hmultiplicity : ∀ a, (Fintype.card {s // v s = a}:ℝ)*
      ((ramification a:ℝ)*residueDegree a) = Module.finrank ℚ F)
    (hdisc : EuclideanIdeal.logarithmicRootDiscriminant K ≤ logRD)
    {ε : ℝ} (hε : 0 < ε)
    (hlarge : 4*mixedEnergyVarianceConstant ≤ ε^2*(Module.finrank ℚ F:ℝ)) :
    ∃ U : Finset ℂ, 0 < U.card ∧
      (U.card:ℝ) ≤
        2*mixedPositionMass v (RealPlaceIndex F) (PairPlaceIndex F)*
          Real.exp (p*(witnessOverlapMean D v hQ+ε*(Module.finrank ℚ F:ℝ)))/arithmeticCovolume K ∧
      arithmeticAmplitude ι (tensorFiniteFunctional v) ε ≤ unitPairs U/(U.card:ℝ)^exponent := by
  letI := differenceLattice_discrete ι hι
  letI := differenceLattice_isZLattice ι hι
  letI : Fintype (torsion K) := Fintype.ofFinite _
  letI := diagonalSIntegers_vaddInvariant D.prime
  letI : VAddInvariantMeasure (differenceLattice ι) (PairPlaceIndex F → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure (differenceLattice ι).toAddSubgroup _ volume)
  let mean := witnessOverlapMean D v hQ
  let T := mean+ε*(Module.finrank ℚ F:ℝ)
  let A := mixedPositionMass v (RealPlaceIndex F) (PairPlaceIndex F)
  let Z := mixedOverlapMass v (RealPlaceIndex F) (PairPlaceIndex F)
  let Ω := witnessSAdicWindow hι D v 0 T
  let Φ : WitnessLabel v → (PairPlaceIndex F → ℝ) → ℝ≥0∞ :=
    fun n => witnessOverlapProfile D v hQ T n.val
  obtain ⟨model, hweighted⟩ := exists_witnessWeightedWindowModel hι hb D v hQ T
  have hbase0 : semiLocalHaar D.prime Ω ≠ 0 :=
    witnessSAdicWindow_volume_positive hι D v hQ hmultiplicity hε hlarge
  have hbasefin : semiLocalHaar D.prime Ω ≠ ∞ := by
    rw [show Ω = witnessSAdicWindow hι D v 0 T from rfl, witnessSAdicWindow_volume_mixed hι D v hQ T]
    exact mixed_supportedWindow_finite v (witnessPairHaar D) (witnessPairBallSystem D v hQ) T
  have hVolume : (semiLocalHaar D.prime Ω).toReal ≤ A*Real.exp (p*T) := by
    rw [show Ω = witnessSAdicWindow hι D v 0 T from rfl, witnessSAdicWindow_volume_mixed hι D v hQ T]
    simpa only [A, measureReal_def, mul_comm] using mixed_supportedWindow_volume_bound
      (β := RealPlaceIndex F) (γ := PairPlaceIndex F) v (witnessPairHaar D)
      (witnessPairBallSystem D v hQ) T
  obtain ⟨U, hU0, hUB, hratio⟩ := model.concentrated_transfer
    volume (relativeLogDomain ι hι) (relativeLogDomain_fundamental ι hι)
    (relativeLogDomain_finite ι hι) (relativeLogDomain_positive ι hι)
    (diagonalSIntegers D.prime) (semiLocalHaar D.prime)
    (productDomain D.prime 0) (productDomain_fundamental D.prime
      (fun a b h => D.distinct (congrArg (fun p => p.asIdeal) h)) 0)
    (productDomain_finite D.prime 0) Ω Φ
    A (arithmeticCovolume K) p increment Z ε (Module.finrank ℚ F) mean
    hbase0 hbasefin
    (fun n => measurable_witnessOverlapProfile D v hQ T n.val)
    (fun n => witnessOverlapProfile_integral_finite D v hQ T n.val)
    (mixedPositionMass_pos v) arithmeticCovolume_pos (mixedOverlapMass_pos v)
    witness_basic.2.2.1.le increment_pos.le p_mul_exponent
    (witnessOverlapProfile_concentration D v hQ hmultiplicity hε hlarge)
    hVolume (fun n₀ h r => by
      simpa only [A, mixedPositionMass, arithmeticCovolume, absoluteDiscriminant_eq_abs,
        mul_assoc] using hweighted n₀ h r
          (witnessPeriod_fourier_separation D v hQ hmultiplicity hdisc n₀.val))
  refine ⟨U, hU0, hUB, ?_⟩
  rw [exponent_eq]
  have hfunc := mixedFunctional_eq v (β := RealPlaceIndex F) (γ := PairPlaceIndex F)
  change Z/A^(1+increment) = _ at hfunc
  rw [hfunc] at hratio
  simpa only [arithmeticAmplitude, relativeUnitMass, relativeMassDenominator_eq_classQuotient,
    torsionOrder, Nat.card_eq_fintype_card, relativeLogDomain_volumeReal, mul_assoc] using hratio

/-- Complete exponential normalization of the actual S-integer graph.
Only ordinary arithmetic data and the explicit concentration size enter. -/
theorem witnessSInteger_exponential_graph (hunr : FiniteUnramified F K)
    (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (hmultiplicity : ∀ a, (Fintype.card {s // v s = a}:ℝ)*
      ((ramification a:ℝ)*residueDegree a) = Module.finrank ℚ F)
    (hdisc : Real.log (rootDiscriminant F) ≤ logRD)
    {ε : ℝ} (hε : 0 < ε)
    (hlarge : 4*mixedEnergyVarianceConstant ≤ ε^2*(Module.finrank ℚ F:ℝ)) :
    ∃ U : Finset ℂ, 0 < U.card ∧
      Real.exp ((Module.finrank ℚ F:ℝ)*arithmeticRate F K finiteProfit ε)/(2:ℝ)^(3+increment) ≤
        unitPairs U/(U.card:ℝ)^exponent := by
  obtain ⟨U, hU0, _, hU⟩ := witnessSInteger_arithmetic_graph hι hb D v hQ hmultiplicity
    (by rwa [EuclideanIdeal.logarithmicRootDiscriminant_eq_base F K hunr]) hε hlarge
  refine ⟨U, hU0, ?_⟩
  rwa [witnessArithmeticAmplitude_eq_exp hunr ι hι hb v hmultiplicity] at hU

/-- The published positive rational rate for an actual finite S-integer graph.
The sole numerical input here is the stated actual pair-integral enclosure. -/
theorem witnessSInteger_uniform_graph (hunr : FiniteUnramified F K)
    (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (hmultiplicity : ∀ a, (Fintype.card {s // v s = a}:ℝ)*
      ((ramification a:ℝ)*residueDegree a) = Module.finrank ℚ F)
    (hpair : (1379635324335:ℝ)/10^12 ≤ JPair)
    (hdisc : Real.log (rootDiscriminant F) ≤ logRD)
    (hresidue : Real.log (relativeResidue K F)/(Module.finrank ℚ F:ℝ) ≤ ceiling)
    (hsignature : thetaMin ≤ signatureRatio F)
    (hlarge : 4*mixedEnergyVarianceConstant ≤ epsilon^2*(Module.finrank ℚ F:ℝ)) :
    ∃ U : Finset ℂ, 0 < U.card ∧
      Real.exp ((Module.finrank ℚ F:ℝ)*((533:ℝ)/10^8))/(2:ℝ)^(3+increment) ≤
        unitPairs U/(U.card:ℝ)^exponent := by
  obtain ⟨U, hU0, _, hU⟩ := witnessSInteger_arithmetic_graph hι hb D v hQ hmultiplicity
    (by rwa [EuclideanIdeal.logarithmicRootDiscriminant_eq_base F K hunr])
    (show 0 < epsilon by norm_num [epsilon]) hlarge
  exact ⟨U, hU0, (witnessArithmeticAmplitude_lower hunr ι hι hb v hmultiplicity
    hpair hdisc hresidue hsignature).trans hU⟩

end UnitDistance.SIntegerCRT
