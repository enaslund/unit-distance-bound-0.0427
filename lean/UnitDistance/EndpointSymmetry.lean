module

public import UnitDistance.EnergyWindow
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section
set_option backward.privateInPublic true


/-! Endpoint exchange preserves the actual normalized overlap law. -/

open MeasureTheory ProbabilityTheory

namespace UnitDistance

/-- A measure-preserving change of variables which exchanges the two
endpoint energies preserves their normalized overlap law exactly. -/
theorem overlapLaw_symmetry {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) (Z : ℝ)
    (τ : Ω ≃ᵐ Ω) (hτ : MeasurePreserving τ m m)
    (hXY : ∀ ω, X (τ ω) = Y ω) (hYX : ∀ ω, Y (τ ω) = X ω) :
    MeasurePreserving τ (overlapLaw m X Y Z) (overlapLaw m X Y Z) := by
  refine ⟨τ.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply τ.measurable hs]
  simp only [overlapLaw, withDensity_apply _ (τ.measurable hs), withDensity_apply _ hs]
  have h := hτ.setLIntegral_comp_preimage_emb τ.measurableEmbedding
    (fun ω => ENNReal.ofReal (Real.exp (-(X ω + Y ω)) / Z)) s
  simpa only [hXY, hYX, add_comm] using h

theorem endpoint_means_equal {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) (Z : ℝ)
    (τ : Ω ≃ᵐ Ω) (hτ : MeasurePreserving τ m m)
    (hXY : ∀ ω, X (τ ω) = Y ω) (hYX : ∀ ω, Y (τ ω) = X ω) :
    (∫ ω, Y ω ∂overlapLaw m X Y Z) = ∫ ω, X ω ∂overlapLaw m X Y Z := by
  have h := (overlapLaw_symmetry m X Y Z τ hτ hXY hYX).integral_comp' X
  simpa only [hXY] using h

theorem endpoint_variances_equal {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) (Z : ℝ)
    (τ : Ω ≃ᵐ Ω) (hτ : MeasurePreserving τ m m)
    (hXY : ∀ ω, X (τ ω) = Y ω) (hYX : ∀ ω, Y (τ ω) = X ω)
    (hX : AEMeasurable X (overlapLaw m X Y Z)) :
    variance Y (overlapLaw m X Y Z) = variance X (overlapLaw m X Y Z) := by
  have h := (overlapLaw_symmetry m X Y Z τ hτ hXY hYX).variance_fun_comp hX
  simpa only [hXY] using h

theorem endpoint_memLp {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) (Z : ℝ)
    (τ : Ω ≃ᵐ Ω) (hτ : MeasurePreserving τ m m)
    (hXY : ∀ ω, X (τ ω) = Y ω) (hYX : ∀ ω, Y (τ ω) = X ω)
    (hX : MemLp X 2 (overlapLaw m X Y Z)) :
    MemLp Y 2 (overlapLaw m X Y Z) := by
  have h := hX.comp_measurePreserving (overlapLaw_symmetry m X Y Z τ hτ hXY hYX)
  simpa only [Function.comp_def, hXY] using h

end UnitDistance
