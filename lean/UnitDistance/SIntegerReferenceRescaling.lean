module

public import UnitDistance.LocalReciprocalRescaling
public import UnitDistance.SIntegerPairedCoordinates
public import UnitDistance.SIntegerWitnessWindow

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual reference-label reciprocal rescaling and unchanged common-window volume -/

noncomputable section
open Set MeasureTheory NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeCompletion Local.ValuedHaar

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

local instance referenceLocalMeasurableSpace (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance referenceLocalBorelSpace (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

def pairedReferenceRescaling (D : PrimePairFamily ι S) (n₀ : S → ℤ) :
    PairedLocalProduct D ≃+ PairedLocalProduct D :=
  AddEquiv.piCongrRight fun s => reciprocalRescaling ((D.prime (s, false)).adicCompletion K) (n₀ s)

theorem pairedReferenceRescaling_measurePreserving (D : PrimePairFamily ι S) (n₀ : S → ℤ) :
    MeasurePreserving (pairedReferenceRescaling D n₀) (pairedLocalHaar D) (pairedLocalHaar D) :=
  measurePreserving_pi _ _ (fun s => reciprocalRescaling_measurePreserving _ (n₀ s))

/-- The true reference rescaling in CRT's original completion coordinates. -/
def referenceRescaling (D : PrimePairFamily ι S) (n₀ : S → ℤ) :
    LocalProduct D.prime ≃+ LocalProduct D.prime :=
  ((pairedCoordinates D).trans (pairedReferenceRescaling D n₀)).trans (pairedCoordinates D).symm

theorem referenceRescaling_measurePreserving (D : PrimePairFamily ι S) (n₀ : S → ℤ) :
    MeasurePreserving (referenceRescaling D n₀) (localProductHaar D.prime) (localProductHaar D.prime) :=
  (pairedCoordinates_symm_measurePreserving D).comp
    ((pairedReferenceRescaling_measurePreserving D n₀).comp (pairedCoordinates_measurePreserving D))

theorem pairedCoordinates_referenceRescaling (D : PrimePairFamily ι S) (n₀ : S → ℤ)
    (x : LocalProduct D.prime) :
    pairedCoordinates D (referenceRescaling D n₀ x) =
      pairedReferenceRescaling D n₀ (pairedCoordinates D x) :=
  (pairedCoordinates D).apply_symm_apply _

/-- The reference shift is exactly the reciprocal local rescaling of the
published profile, including every shell beyond the hard period. -/
theorem witnessFiniteProfile_referenceRescaling (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ) (x : LocalProduct D.prime) :
    witnessFiniteProfile D v 0 (referenceRescaling D n₀ x) = witnessFiniteProfile D v n₀ x := by
  rw [← witnessFiniteProfile_pairedCoordinates D v hQ, pairedCoordinates_referenceRescaling]
  unfold Witness.tensorFiniteProfile witnessFiniteProfile
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro s hs
  rw [Witness.localShellProfile_eq_factors, Fintype.prod_bool]
  change (ballSystem ((D.prime (s, false)).adicCompletion K)).shellFactor 0
      (Finset.range 6) (Witness.shellWeightNat (v s))
        (uniformizerMul _ (n₀ s) (x (s, false))) *
    (ballSystem ((D.prime (s, false)).adicCompletion K)).shellFactor (Witness.periodPower (v s))
      (Finset.range 6) (Witness.shellWeightNat (v s))
        (uniformizerMul _ (-n₀ s)
          ((completionInvolution ι (D.prime (s, false)) (D.prime (s, true)) (D.partner s)).symm (x (s, true)))) = _
  rw [shellFactor_uniformizerMul, shellFactor_uniformizerMul, zero_add]
  change Witness.localShellFactor (v s) (witnessPairBallSystem D v hQ s) (n₀ s) (x (s, false)) *
    Witness.localShellFactor (v s) (witnessPairBallSystem D v hQ s) (Witness.periodPower (v s) + -n₀ s)
      ((completionInvolution ι (D.prime (s, false)) (D.prime (s, true)) (D.partner s)).symm (x (s, true))) = _
  rw [witnessPair_factor_partner]
  simp only [witnessLocalFactor, witnessRadius, Bool.false_eq_true, ↓reduceIte, sub_eq_add_neg]
  exact mul_comm _ _

theorem witnessFiniteEnergy_referenceRescaling (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ) (x : LocalProduct D.prime) :
    witnessFiniteEnergy D v 0 (referenceRescaling D n₀ x) = witnessFiniteEnergy D v n₀ x :=
  congrArg (fun r => -Real.log r) (witnessFiniteProfile_referenceRescaling D v hQ n₀ x)

variable [IsTotallyComplex K]

def semiLocalReferenceRescaling (D : PrimePairFamily ι S) (n₀ : S → ℤ) :
    (EuclideanIdeal.Space K × LocalProduct D.prime) ≃+ (EuclideanIdeal.Space K × LocalProduct D.prime) :=
  (AddEquiv.refl _).prodCongr (referenceRescaling D n₀)

theorem semiLocalReferenceRescaling_measurePreserving (D : PrimePairFamily ι S) (n₀ : S → ℤ) :
    MeasurePreserving (semiLocalReferenceRescaling D n₀) (semiLocalHaar D.prime) (semiLocalHaar D.prime) :=
  (MeasurePreserving.id volume).prod (referenceRescaling_measurePreserving D n₀)

theorem witnessSAdicWindow_referenceRescaling (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ) (T : ℝ) :
    semiLocalReferenceRescaling D n₀ ⁻¹' witnessSAdicWindow hι D v 0 T =
      witnessSAdicWindow hι D v n₀ T := by
  ext x
  change (True ∧ witnessFiniteProfile D v 0 (referenceRescaling D n₀ x.2) ≠ 0) ∧
      RelativeUnits.relativeEnergy ι hι x.1+witnessFiniteEnergy D v 0 (referenceRescaling D n₀ x.2) ≤ T ↔
    (True ∧ witnessFiniteProfile D v n₀ x.2 ≠ 0) ∧
      RelativeUnits.relativeEnergy ι hι x.1+witnessFiniteEnergy D v n₀ x.2 ≤ T
  rw [witnessFiniteProfile_referenceRescaling D v hQ, witnessFiniteEnergy_referenceRescaling D v hQ]

/-- The actual common window volume is independent of the chosen signed reference. -/
theorem witnessSAdicWindow_volume_reference (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ) (T : ℝ) :
    semiLocalHaar D.prime (witnessSAdicWindow hι D v n₀ T) =
      semiLocalHaar D.prime (witnessSAdicWindow hι D v 0 T) := by
  rw [← witnessSAdicWindow_referenceRescaling hι D v hQ n₀ T]
  exact (semiLocalReferenceRescaling_measurePreserving D n₀).measure_preimage
    (measurableSet_supportedWindow (witnessSAdicSupport_measurable D v 0)
      (witnessSAdicEnergy_continuous hι D v 0).measurable T).nullMeasurableSet

end UnitDistance.SIntegerCRT
