module

public import UnitDistance.SIntegerMixedOverlap
public import UnitDistance.TensorMixedLabelConcentration

@[expose] public section
set_option backward.privateInPublic true


/-! # Concentration of the actual field S-integer window -/

noncomputable section
set_option synthInstance.maxSize 512
open Set MeasureTheory NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped Classical BigOperators ENNReal nonZeroDivisors
namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeUnits Local.ValuedHaar Witness

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

local instance concentrationLocalMeasurableSpace (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance concentrationLocalBorelSpace (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

def witnessOverlapMean (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s)) : ℝ :=
  mixedCanonicalMean v (witnessPairHaar D) (witnessPairBallSystem D v hQ)
    (witnessPairSteps D v hQ) (witnessUnitDirection D) (RealPlaceIndex F) (PairPlaceIndex F)

theorem witnessOverlapProfile_integral_finite (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (T : ℝ) (n : S → ℤ) : (∫⁻ u, witnessOverlapProfile D v hQ T n u) ≠ ∞ :=
  mixedCanonicalOverlap_integral_finite v (witnessPairHaar D) (witnessPairBallSystem D v hQ)
    (witnessPairSteps D v hQ) (fun s n => reciprocalSteps_measurable (WitnessLocalType D s) n)
    (witnessUnitDirection D) T n

theorem witnessOverlapProfile_concentration (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (hmultiplicity : ∀ a, (Fintype.card {s // v s = a}:ℝ)*
      ((ramification a:ℝ)*residueDegree a) = Module.finrank ℚ F)
    {ε : ℝ} (hε : 0 < ε)
    (hlarge : 4*mixedEnergyVarianceConstant ≤ ε^2*(Module.finrank ℚ F:ℝ)) :
    let d : ℝ := Module.finrank ℚ F
    let mean := witnessOverlapMean D v hQ
    (1/2:ℝ)*mixedOverlapMass v (RealPlaceIndex F) (PairPlaceIndex F)*Real.exp (2*(mean-ε*d)) ≤
      ∑ n : FiniteValuationIndex v,
        (∫⁻ u, witnessOverlapProfile D v hQ (mean+ε*d) n.val u).toReal := by
  have hdim : (Fintype.card (RealPlaceIndex F):ℝ)+2*Fintype.card (PairPlaceIndex F) =
      Module.finrank ℚ F := by exact_mod_cast card_add_two_mul_card_eq_rank F
  have hd : 0 < (Fintype.card (RealPlaceIndex F):ℝ)+2*Fintype.card (PairPlaceIndex F) := by
    rw [hdim]
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hcount : (Fintype.card S:ℝ) ≤
      (69/32:ℝ)*((Fintype.card (RealPlaceIndex F):ℝ)+2*Fintype.card (PairPlaceIndex F)) := by
    rw [hdim, card_primeTypes_of_multiplicities v (Module.finrank ℚ F) hmultiplicity]
  have h := mixedCanonicalOverlap_sum_concentration
    (β := RealPlaceIndex F) (γ := PairPlaceIndex F) v (witnessPairHaar D)
    (witnessPairBallSystem D v hQ) (witnessPairSteps D v hQ)
    (fun s n => reciprocalSteps_measurable (WitnessLocalType D s) n)
    (witnessUnitDirection D) hcount hε hd (hdim.symm ▸ hlarge)
  simpa only [hdim, witnessOverlapMean, witnessOverlapProfile] using h

/-- The actual zero-reference field window has exactly the mixed-coordinate volume. -/
theorem witnessSAdicWindow_volume_mixed (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s)) (T : ℝ) :
    semiLocalHaar D.prime (witnessSAdicWindow hι D v 0 T) =
      mixedPositionMeasure (β := RealPlaceIndex F) (γ := PairPlaceIndex F) (witnessPairHaar D)
        (supportedWindow (mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
          (mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T) := by
  rw [← witnessMixedCoordinates_window hι D v hQ T]
  exact (witnessMixedCoordinates_measurePreserving hι D).measure_preimage
    (measurableSet_supportedWindow
      (measurableSet_mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
      (measurable_mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T).nullMeasurableSet

theorem witnessSAdicWindow_volume_positive (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (hmultiplicity : ∀ a, (Fintype.card {s // v s = a}:ℝ)*
      ((ramification a:ℝ)*residueDegree a) = Module.finrank ℚ F)
    {ε : ℝ} (hε : 0 < ε)
    (hlarge : 4*mixedEnergyVarianceConstant ≤ ε^2*(Module.finrank ℚ F:ℝ)) :
    semiLocalHaar D.prime (witnessSAdicWindow hι D v 0
      (witnessOverlapMean D v hQ+ε*(Module.finrank ℚ F:ℝ))) ≠ 0 := by
  rw [witnessSAdicWindow_volume_mixed hι D v hQ]
  apply window_measure_ne_zero_of_overlap_pos
    (mixedDisplacementMeasure (γ := PairPlaceIndex F) (fun s => Measure.dirac (witnessUnitDirection D s)))
    _ _ (mixedStep v (witnessPairHaar D) (witnessPairBallSystem D v hQ) (witnessPairSteps D v hQ))
  change 0 < (supportedWindowOverlap _ _ _ _ _ _).toReal
  rw [mixed_dirac_supportedWindowOverlap_toReal_sum v (witnessPairHaar D)
    (witnessPairBallSystem D v hQ) (witnessPairSteps D v hQ)
    (fun s n => reciprocalSteps_measurable (WitnessLocalType D s) n) (witnessUnitDirection D)]
  have hZ := mixedOverlapMass_pos (β := RealPlaceIndex F) (γ := PairPlaceIndex F) v
  exact lt_of_lt_of_le (by positivity)
      (witnessOverlapProfile_concentration D v hQ hmultiplicity hε hlarge)

end UnitDistance.SIntegerCRT
