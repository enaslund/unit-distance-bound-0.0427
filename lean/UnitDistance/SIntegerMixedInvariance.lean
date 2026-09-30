module

public import UnitDistance.SIntegerMixedCoordinates
public import UnitDistance.TensorPhaseInvariance
public import UnitDistance.LocalUnitInvariance

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual phase and valuation-unit invariance of the common mixed window -/

noncomputable section
set_option synthInstance.maxSize 512
open Set MeasureTheory NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeUnits Local.ValuedHaar Witness

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

local instance invarianceLocalMeasurableSpace (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance invarianceLocalBorelSpace (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

variable (D : PrimePairFamily ι S) (x y : WitnessMixedPosition D)
  (hc : ∀ i, ‖x.1.1 i‖ = ‖y.1.1 i‖)
  (hp₁ : ∀ j, ‖(x.1.2 j).1‖ = ‖(y.1.2 j).1‖)
  (hp₂ : ∀ j, ‖(x.1.2 j).2‖ = ‖(y.1.2 j).2‖)
  (hf₁ : ∀ s, intValuation (WitnessLocalType D s) (x.2 s).1 =
    intValuation (WitnessLocalType D s) (y.2 s).1)
  (hf₂ : ∀ s, intValuation (WitnessLocalType D s) (x.2 s).2 =
    intValuation (WitnessLocalType D s) (y.2 s).2)

def witnessMixedRotation : WitnessMixedPosition D ≃+ WitnessMixedPosition D :=
  (tensorPhaseEquiv x.1 y.1 hc hp₁ hp₂).toAddEquiv.prodCongr
    (AddEquiv.piCongrRight fun s =>
      (valuationRotation (WitnessLocalType D s) (x.2 s).1 (y.2 s).1 (hf₁ s)).toAddEquiv.prodCongr
        (valuationRotation (WitnessLocalType D s) (x.2 s).2 (y.2 s).2 (hf₂ s)).toAddEquiv)

theorem witnessMixedRotation_apply : witnessMixedRotation D x y hc hp₁ hp₂ hf₁ hf₂ x = y := by
  refine Prod.ext (tensorPhaseEquiv_apply x.1 y.1 hc hp₁ hp₂) ?_
  funext s
  exact Prod.ext (valuationRotation_apply _ _ _ _) (valuationRotation_apply _ _ _ _)

theorem witnessMixedRotation_measurePreserving :
    MeasurePreserving (witnessMixedRotation D x y hc hp₁ hp₂ hf₁ hf₂)
      (mixedPositionMeasure (witnessPairHaar D)) (mixedPositionMeasure (witnessPairHaar D)) :=
  (tensorPhaseEquiv_measurePreserving x.1 y.1 hc hp₁ hp₂).prod
    (measurePreserving_pi _ _ (fun s =>
      (valuationRotation_measurePreserving _ _ _ (hf₁ s)).prod
        (valuationRotation_measurePreserving _ _ _ (hf₂ s))))

theorem witnessMixedRotation_localProfile (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (z : WitnessMixedPosition D) (s : S) :
    localShellProfile (v s) (witnessPairBallSystem D v hQ s)
        ((witnessMixedRotation D x y hc hp₁ hp₂ hf₁ hf₂ z).2 s) =
      localShellProfile (v s) (witnessPairBallSystem D v hQ s) (z.2 s) :=
  (witnessPairBallSystem D v hQ s).shellProfile_invariant
    (valuationRotation (WitnessLocalType D s) (x.2 s).1 (y.2 s).1 (hf₁ s))
    (valuationRotation (WitnessLocalType D s) (x.2 s).2 (y.2 s).2 (hf₂ s))
    (valuationRotation_preserves_ball _ _ _ (hf₁ s))
    (valuationRotation_preserves_ball _ _ _ (hf₂ s)) _ _ _ _

theorem witnessMixedRotation_profile (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (z : WitnessMixedPosition D) :
    tensorFiniteProfile v (witnessPairHaar D) (witnessPairBallSystem D v hQ)
        (witnessMixedRotation D x y hc hp₁ hp₂ hf₁ hf₂ z).2 =
      tensorFiniteProfile v (witnessPairHaar D) (witnessPairBallSystem D v hQ) z.2 := by
  exact Finset.prod_congr rfl (fun s _ =>
    witnessMixedRotation_localProfile D x y hc hp₁ hp₂ hf₁ hf₂ v hQ z s)

theorem witnessMixedRotation_energy (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (z : WitnessMixedPosition D) :
    mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)
        (witnessMixedRotation D x y hc hp₁ hp₂ hf₁ hf₂ z) =
      mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ) z := by
  unfold mixedPositionEnergy
  rw [show (witnessMixedRotation D x y hc hp₁ hp₂ hf₁ hf₂ z).1 =
    tensorPhaseEquiv x.1 y.1 hc hp₁ hp₂ z.1 from rfl,
    tensorPositionEnergy_phase]
  congr 1
  exact Finset.sum_congr rfl (fun s _ => congrArg (fun r => -Real.log r)
    (witnessMixedRotation_localProfile D x y hc hp₁ hp₂ hf₁ hf₂ v hQ z s))

theorem witnessMixedRotation_window (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (T : ℝ) (z : WitnessMixedPosition D) :
    witnessMixedRotation D x y hc hp₁ hp₂ hf₁ hf₂ z ∈
      supportedWindow (mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
        (mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T ↔
    z ∈ supportedWindow (mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
        (mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T := by
  change (_ ≠ 0 ∧ _ ≤ T) ↔ (_ ≠ 0 ∧ _ ≤ T)
  rw [witnessMixedRotation_profile D x y hc hp₁ hp₂ hf₁ hf₂ v hQ,
    witnessMixedRotation_energy D x y hc hp₁ hp₂ hf₁ hf₂ v hQ]

include hc hp₁ hp₂ hf₁ hf₂ in
/-- The full common sum-energy window, rather than separate local sublevel
sets, has overlap depending only on the individual norms and valuations. -/
theorem witnessMixed_overlap_eq_of_norm_valuation_eq (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (T : ℝ) :
    let W := supportedWindow
      (mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
      (mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T
    mixedPositionMeasure (witnessPairHaar D) (overlapSet W x) =
      mixedPositionMeasure (witnessPairHaar D) (overlapSet W y) := by
  intro W
  let e := witnessMixedRotation D x y hc hp₁ hp₂ hf₁ hf₂
  have hpre : e ⁻¹' overlapSet W y = overlapSet W x := by
    ext z
    change (e z ∈ W ∧ e z+y ∈ W) ↔ (z ∈ W ∧ z+x ∈ W)
    rw [← witnessMixedRotation_apply D x y hc hp₁ hp₂ hf₁ hf₂, ← map_add]
    exact and_congr (witnessMixedRotation_window D x y hc hp₁ hp₂ hf₁ hf₂ v hQ T z)
      (witnessMixedRotation_window D x y hc hp₁ hp₂ hf₁ hf₂ v hQ T (z+x))
  have hW : MeasurableSet W := measurableSet_supportedWindow
    (measurableSet_mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
    (measurable_mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T
  rw [← hpre]
  exact (witnessMixedRotation_measurePreserving D x y hc hp₁ hp₂ hf₁ hf₂).measure_preimage
    (hW.inter (hW.preimage (measurable_id.add_const _))).nullMeasurableSet

end UnitDistance.SIntegerCRT
