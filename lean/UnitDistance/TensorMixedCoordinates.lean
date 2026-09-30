module

public import UnitDistance.TensorMixedOverlap
public import UnitDistance.ProductMeasureCoordinates

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual position and displacement coordinates for the mixed witness

Regroup the archimedean and finite coordinates by places. The restriction
to both endpoints of the literal finite-profile support is exactly the
product of the local restricted overlap measures.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal

namespace UnitDistance.Witness

variable {β γ ι : Type*} [Fintype β] [Fintype γ] [Fintype ι] {G U : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, MeasurableSpace (G i)]
  [∀ i, MeasurableAdd₂ (G i)] [∀ i, MeasurableNeg (G i)]
  [∀ i, MeasurableSpace (U i)]
  (v : ι → Fin 11) (μ : (i : ι) → Measure (G i))
  [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsAddRightInvariant]
  [∀ i, (μ i).IsAddLeftInvariant] [∀ i, (μ i).IsNegInvariant]
  (B : (i : ι) → Local.BallSystem (G i) (μ i) (residueCard (v i)))
  (S : (i : ι) → (B i).ReciprocalSteps (U i))
  (ν : (i : ι) → Measure (U i)) [∀ i, IsProbabilityMeasure (ν i)]

abbrev MixedPositionCoordinates (β γ : Type*) (G : ι → Type*) :=
  TensorCoordinates β γ × ((i : ι) → G i × G i)

abbrev MixedDisplacementCoordinates (γ : Type*) (U : ι → Type*) :=
  (γ → ℝ) × ((i : ι) → ℤ × U i)

def mixedPositionEnergy (x : MixedPositionCoordinates β γ G) : ℝ :=
  tensorPositionEnergy x.1 + ∑ i, localShellEnergy (v i) (B i) (x.2 i)

def mixedPositionSupport : Set (MixedPositionCoordinates β γ G) :=
  {x | x.2 ∈ Function.support (tensorFiniteProfile v μ B)}

def mixedStep (d : MixedDisplacementCoordinates γ U) : MixedPositionCoordinates β γ G :=
  (tensorStep d.1, fun i => (S i).step (d.2 i).1 (d.2 i).2)

def mixedPositionMeasure : Measure (MixedPositionCoordinates β γ G) :=
  volume.prod (Measure.pi (fun i => (μ i).prod (μ i)))

def mixedDisplacementMeasure : Measure (MixedDisplacementCoordinates γ U) :=
  volume.prod (Measure.pi (fun i => Measure.count.prod (ν i)))

instance mixedPositionMeasure_sigmaFinite :
    SigmaFinite (mixedPositionMeasure (β := β) (γ := γ) μ) := by
  unfold mixedPositionMeasure
  infer_instance

instance mixedDisplacementMeasure_sigmaFinite :
    SigmaFinite (mixedDisplacementMeasure (γ := γ) ν) := by
  unfold mixedDisplacementMeasure
  infer_instance

def mixedOverlapCoordinates :
    (MixedDisplacementCoordinates γ U × MixedPositionCoordinates β γ G) ≃ᵐ
      MixedEndpointCoordinates β γ G U :=
  prodCrossCoordinates.trans
    (tensorOverlapCoordinates.prodCongr
      (piProdCoordinates (fun i => ℤ × U i) (fun i => G i × G i)).symm)

@[simp] theorem mixedOverlapCoordinates_apply
    (w : MixedDisplacementCoordinates γ U × MixedPositionCoordinates β γ G) :
    mixedOverlapCoordinates w =
      (tensorOverlapCoordinates (w.1.1, w.2.1), fun i => (w.1.2 i, w.2.2 i)) := rfl

@[simp] theorem mixedFirstEnergy_coordinates
    (w : MixedDisplacementCoordinates γ U × MixedPositionCoordinates β γ G) :
    mixedFirstEnergy v μ B (mixedOverlapCoordinates w) =
      firstEnergy (mixedPositionEnergy v μ B) w := rfl

@[simp] theorem mixedSecondEnergy_coordinates
    (w : MixedDisplacementCoordinates γ U × MixedPositionCoordinates β γ G) :
    mixedSecondEnergy v μ B S (mixedOverlapCoordinates w) =
      secondEnergy (mixedPositionEnergy v μ B) (mixedStep v μ B S) w := rfl

theorem measurable_mixedPositionEnergy :
    Measurable (mixedPositionEnergy (β := β) (γ := γ) v μ B) := by
  have harch := (continuous_tensorPositionEnergy (β := β) (γ := γ)).measurable
  have hlocal i := (B i).shellEnergy_measurable (periodPower (v i))
    (Finset.range 6 ×ˢ Finset.range 6)
    (fun ij => shellWeightNat (v i) ij.1 * shellWeightNat (v i) ij.2)
  exact (harch.comp measurable_fst).add (Finset.measurable_sum _ (fun i _ =>
    (hlocal i).comp ((measurable_pi_apply i).comp measurable_snd)))

theorem measurableSet_mixedPositionSupport :
    MeasurableSet (mixedPositionSupport (β := β) (γ := γ) v μ B) :=
  (measurableSet_support (tensorFiniteProfile_measurable v μ B)).preimage measurable_snd

theorem measurable_mixedStep (hs : ∀ i n, Measurable ((S i).step n)) :
    Measurable (mixedStep (β := β) (γ := γ) v μ B S) :=
  ((continuous_tensorStep (β := β) (γ := γ)).measurable.comp measurable_fst).prodMk
    (Measurable.of_eval (fun i =>
      ((B i).reciprocalSteps_measurable (S i) (hs i)).comp
        ((measurable_pi_apply i).comp measurable_snd)))

def mixedUnrestrictedBase : Measure (MixedEndpointCoordinates β γ G U) :=
  volume.prod (Measure.pi (fun i =>
    (Measure.count.prod (ν i)).prod ((μ i).prod (μ i))))

theorem mixedOverlapCoordinates_unrestricted :
    MeasurePreserving (mixedOverlapCoordinates (β := β) (γ := γ) (G := G) (U := U))
      ((mixedDisplacementMeasure (γ := γ) ν).prod (mixedPositionMeasure (β := β) (γ := γ) μ))
      (mixedUnrestrictedBase (β := β) (γ := γ) μ ν) := by
  have h₁ := prodCrossCoordinates_measurePreserving (volume : Measure (γ → ℝ))
    (Measure.pi (fun i => (Measure.count : Measure ℤ).prod (ν i)))
    (volume : Measure (TensorCoordinates β γ))
    (Measure.pi (fun i => (μ i).prod (μ i)))
  have h₂ := tensorOverlapCoordinates_measurePreserving (β := β) (γ := γ)
  have h₃ := (piProdCoordinates_measurePreserving (fun i => ℤ × U i)
    (fun i => G i × G i) (fun i => Measure.count.prod (ν i))
    (fun i => (μ i).prod (μ i))).symm
      (piProdCoordinates (fun i => ℤ × U i) (fun i => G i × G i))
  exact (h₂.prod h₃).comp h₁

def localOverlapSupport (i : ι) : Set ((ℤ × U i) × (G i × G i)) :=
  {z | z.2 ∈ Function.support (localShellProfile (v i) (B i)) ∧
    z.2+(S i).step z.1.1 z.1.2 ∈ Function.support (localShellProfile (v i) (B i))}

theorem mixedOverlapCoordinates_support :
    (mixedOverlapCoordinates (β := β) (γ := γ)) ⁻¹'
      (univ ×ˢ univ.pi (localOverlapSupport v μ B S)) =
      {z | z.2 ∈ mixedPositionSupport v μ B ∧
        z.2 + mixedStep v μ B S z.1 ∈ mixedPositionSupport v μ B} := by
  ext z
  simp only [Set.mem_preimage, mixedOverlapCoordinates_apply, Set.mem_prod,
    Set.mem_univ, Set.mem_pi, forall_const, true_and, localOverlapSupport,
    Set.mem_setOf_eq, mixedPositionSupport, Function.mem_support, tensorFiniteProfile,
    Finset.prod_ne_zero_iff, Finset.mem_univ, mixedStep, Prod.snd_add, Pi.add_apply]
  exact forall_and

theorem mixedOverlapBase_eq_restrict :
    mixedOverlapBase (β := β) (γ := γ) v μ B S ν =
      (mixedUnrestrictedBase (β := β) (γ := γ) μ ν).restrict
        (univ ×ˢ univ.pi (localOverlapSupport v μ B S)) := by
  rw [mixedUnrestrictedBase, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_pi_pi]
  rfl

/-- Exact measure preservation, including the actual support at both endpoints. -/
theorem mixedOverlapCoordinates_measurePreserving :
    MeasurePreserving (mixedOverlapCoordinates (β := β) (γ := γ) (G := G) (U := U))
      (supportedOverlapMeasure (mixedDisplacementMeasure ν) (mixedPositionMeasure μ)
        (mixedStep v μ B S) (mixedPositionSupport v μ B))
      (mixedOverlapBase v μ B S ν) := by
  rw [mixedOverlapBase_eq_restrict v μ B S ν]
  have h := (mixedOverlapCoordinates_unrestricted (β := β) (γ := γ) μ ν).restrict_preimage_emb
    (mixedOverlapCoordinates (β := β) (γ := γ)).measurableEmbedding
      (univ ×ˢ univ.pi (localOverlapSupport v μ B S))
  rw [mixedOverlapCoordinates_support v μ B S] at h
  exact h

/-- The position-space overlap equals the supported endpoint-event measure. -/
theorem mixed_supportedWindowOverlap_eq (hs : ∀ i n, Measurable ((S i).step n)) (T : ℝ) :
    supportedWindowOverlap (mixedDisplacementMeasure (γ := γ) ν)
      (mixedPositionMeasure (β := β) (γ := γ) μ) (mixedStep v μ B S)
      (mixedPositionSupport v μ B) (mixedPositionEnergy v μ B) T =
      (mixedOverlapBase (β := β) (γ := γ) v μ B S ν)
        {z | mixedFirstEnergy v μ B z ≤ T ∧ mixedSecondEnergy v μ B S z ≤ T} := by
  rw [supportedWindowOverlap_eq_pair_measure _ _ _ (measurable_mixedStep v μ B S hs)
    _ (measurableSet_mixedPositionSupport v μ B) _ (measurable_mixedPositionEnergy v μ B)]
  have h := (mixedOverlapCoordinates_measurePreserving (β := β) (γ := γ) v μ B S ν).measure_preimage_equiv
      {z | mixedFirstEnergy v μ B z ≤ T ∧ mixedSecondEnergy v μ B S z ≤ T}
  simpa only [Set.preimage_setOf_eq, mixedFirstEnergy_coordinates,
    mixedSecondEnergy_coordinates] using h

/-- Concentration for the actual common supported sum-energy window. -/
theorem mixed_concentrated_supportedWindowOverlap (hs : ∀ i n, Measurable ((S i).step n))
    (hcount : (Fintype.card ι:ℝ) ≤ (69/32:ℝ)*((Fintype.card β:ℝ)+2*Fintype.card γ))
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < (Fintype.card β:ℝ)+2*Fintype.card γ)
    (hlarge : 4*mixedEnergyVarianceConstant ≤ ε^2*((Fintype.card β:ℝ)+2*Fintype.card γ)) :
    let d : ℝ := (Fintype.card β:ℝ)+2*Fintype.card γ
    let mean := mixedEnergyMean v μ B S ν β γ
    (1/2:ℝ)*mixedOverlapMass v β γ*Real.exp (2*(mean-ε*d)) ≤
      (supportedWindowOverlap (mixedDisplacementMeasure (γ := γ) ν)
        (mixedPositionMeasure (β := β) (γ := γ) μ) (mixedStep v μ B S)
        (mixedPositionSupport v μ B) (mixedPositionEnergy v μ B) (mean+ε*d)).toReal := by
  dsimp only
  rw [mixed_supportedWindowOverlap_eq v μ B S ν hs]
  exact mixed_concentrated_energyEvent v μ B S ν hs hcount hε hd hlarge

end UnitDistance.Witness
