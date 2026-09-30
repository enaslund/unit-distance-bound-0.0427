module

public import UnitDistance.EndpointSymmetry
public import UnitDistance.SupportedProfile
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual endpoint exchange for even supported profiles

At a fixed displacement β, reflection followed by translation sends
`x` to `-x-β`. It interchanges the two endpoint energies of an even profile,
preserves additive Haar measure, and preserves the restriction requiring
both endpoints to lie in an even support. The displacement parameter and its
measure are unchanged; no inversion invariance of the displacement law is
needed.
-/

open MeasureTheory ProbabilityTheory

namespace UnitDistance

variable {D X : Type*} [MeasurableSpace D]
  [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X] [MeasurableNeg X]

/-- The actual reflection-translation involution on displacement/position pairs. -/
def endpointExchange (step : D → X) (hstep : Measurable step) : (D × X) ≃ᵐ (D × X) where
  toFun z := (z.1, -z.2 - step z.1)
  invFun z := (z.1, -z.2 - step z.1)
  left_inv := by intro z; ext <;> simp
  right_inv := by intro z; ext <;> simp
  measurable_toFun := measurable_fst.prodMk (measurable_snd.neg.sub (hstep.comp measurable_fst))
  measurable_invFun := measurable_fst.prodMk (measurable_snd.neg.sub (hstep.comp measurable_fst))

@[simp] theorem endpointExchange_apply (step : D → X) (hstep : Measurable step) (z : D × X) :
    endpointExchange step hstep z = (z.1, -z.2 - step z.1) := rfl

/-- The first energy after the involution is exactly the original second energy. -/
theorem endpointExchange_firstEnergy (step : D → X) (hstep : Measurable step)
    (E : X → ℝ) (hEven : ∀ x, E (-x) = E x) (z : D × X) :
    firstEnergy E (endpointExchange step hstep z) = secondEnergy E step z := by
  change E (-z.2 - step z.1) = E (z.2 + step z.1)
  rw [show -z.2 - step z.1 = -(z.2 + step z.1) by abel, hEven]

/-- The second energy after the involution is exactly the original first energy. -/
theorem endpointExchange_secondEnergy (step : D → X) (hstep : Measurable step)
    (E : X → ℝ) (hEven : ∀ x, E (-x) = E x) (z : D × X) :
    secondEnergy E step (endpointExchange step hstep z) = firstEnergy E z := by
  change E ((-z.2 - step z.1) + step z.1) = E z.2
  rw [sub_add_cancel, hEven]

/-- Evenness of support makes the two-endpoint support set invariant under
this same actual involution. -/
theorem endpointExchange_support (step : D → X) (hstep : Measurable step)
    (S : Set X) (hEven : ∀ x, -x ∈ S ↔ x ∈ S) :
    endpointExchange step hstep ⁻¹' {z | z.2 ∈ S ∧ z.2 + step z.1 ∈ S} =
      {z | z.2 ∈ S ∧ z.2 + step z.1 ∈ S} := by
  ext z
  simp only [Set.mem_preimage, endpointExchange_apply, Set.mem_setOf_eq, sub_add_cancel]
  rw [show -z.2 - step z.1 = -(z.2 + step z.1) by abel, hEven, hEven, and_comm]

/-- Product Haar measure is preserved fiberwise by the actual reflection
and translation, for an arbitrary displacement measure. -/
theorem endpointExchange_measurePreserving (σ : Measure D) [SFinite σ]
    (μ : Measure X) [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (step : D → X) (hstep : Measurable step) :
    MeasurePreserving (endpointExchange step hstep) (σ.prod μ) (σ.prod μ) := by
  apply (MeasurePreserving.id σ).skew_product
    (g := fun β x => -x - step β)
    (measurable_snd.neg.sub (hstep.comp measurable_fst))
  filter_upwards with β
  simpa only [Function.comp_def, sub_eq_add_neg] using
    ((measurePreserving_add_right μ (-step β)).comp
      (Measure.measurePreserving_neg μ)).map_eq

/-- Restricting the pair measure to two supported endpoints preserves the
same symmetry. Ambient Haar measure is never replaced by a restricted Haar
measure in the fiberwise change of variables. -/
theorem endpointExchange_supported_measurePreserving (σ : Measure D) [SFinite σ]
    (μ : Measure X) [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (step : D → X) (hstep : Measurable step)
    (S : Set X) (hS : MeasurableSet S) (hEven : ∀ x, -x ∈ S ↔ x ∈ S) :
    MeasurePreserving (endpointExchange step hstep)
      (supportedOverlapMeasure σ μ step S) (supportedOverlapMeasure σ μ step S) := by
  have hs : MeasurableSet {z : D × X | z.2 ∈ S ∧ z.2 + step z.1 ∈ S} :=
    (hS.preimage measurable_snd).inter
      (hS.preimage (measurable_snd.add (hstep.comp measurable_fst)))
  have h := (endpointExchange_measurePreserving σ μ step hstep).restrict_preimage hs
  rw [endpointExchange_support step hstep S hEven] at h
  exact h

/-- Even supported profiles have equal endpoint means and variances, and
finite second moment for one endpoint implies it for the other. All three
facts follow from the explicit reflection-translation map above. -/
theorem even_supported_endpoint_moments (σ : Measure D) [SFinite σ]
    (μ : Measure X) [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (step : D → X) (hstep : Measurable step)
    (S : Set X) (hS : MeasurableSet S) (hSEven : ∀ x, -x ∈ S ↔ x ∈ S)
    (E : X → ℝ) (hEEven : ∀ x, E (-x) = E x) (Z : ℝ)
    (hX : MemLp (firstEnergy (D := D) E) 2
      (overlapLaw (supportedOverlapMeasure σ μ step S)
        (firstEnergy E) (secondEnergy E step) Z)) :
    MemLp (secondEnergy E step) 2
      (overlapLaw (supportedOverlapMeasure σ μ step S)
        (firstEnergy E) (secondEnergy E step) Z) ∧
    (∫ z, secondEnergy E step z ∂overlapLaw (supportedOverlapMeasure σ μ step S)
      (firstEnergy E) (secondEnergy E step) Z) =
      (∫ z, firstEnergy E z ∂overlapLaw (supportedOverlapMeasure σ μ step S)
        (firstEnergy E) (secondEnergy E step) Z) ∧
    variance (secondEnergy E step) (overlapLaw (supportedOverlapMeasure σ μ step S)
      (firstEnergy E) (secondEnergy E step) Z) =
      variance (firstEnergy E) (overlapLaw (supportedOverlapMeasure σ μ step S)
        (firstEnergy E) (secondEnergy E step) Z) := by
  let m := supportedOverlapMeasure σ μ step S
  let τ := endpointExchange step hstep
  have hτ : MeasurePreserving τ m m :=
    endpointExchange_supported_measurePreserving σ μ step hstep S hS hSEven
  have hXY := endpointExchange_firstEnergy step hstep E hEEven
  have hYX := endpointExchange_secondEnergy step hstep E hEEven
  exact ⟨endpoint_memLp m (firstEnergy E) (secondEnergy E step) Z τ hτ hXY hYX hX,
    endpoint_means_equal m (firstEnergy E) (secondEnergy E step) Z τ hτ hXY hYX,
    endpoint_variances_equal m (firstEnergy E) (secondEnergy E step) Z τ hτ hXY hYX
      hX.aemeasurable⟩

end UnitDistance
