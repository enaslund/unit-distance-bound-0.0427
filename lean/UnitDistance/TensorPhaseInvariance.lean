module

public import UnitDistance.TensorEnergy
public import UnitDistance.GeometryTiling
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section
set_option backward.privateInPublic true


/-!
# Phase invariance of the actual common-window overlap

Equal individual complex moduli give an explicit product of rotations.
This map preserves ordinary volume and the summed energy, so the overlap
volume depends only on displacement moduli, including zero coordinates.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace UnitDistance.Witness

theorem exists_complex_rotation_of_norm_eq {x y : ℂ} (h : ‖x‖ = ‖y‖) :
    ∃ e : ℂ ≃ₗᵢ[ℝ] ℂ, e x = y := by
  by_cases hx : x = 0
  · have hy : y = 0 := norm_eq_zero.mp (by simpa only [hx, norm_zero] using h.symm)
    exact ⟨LinearIsometryEquiv.refl ℝ ℂ, by simp [hx, hy]⟩
  · let a : Circle := ⟨y/x, by
      simp [Submonoid.unitSphere, norm_div, ← h, norm_ne_zero_iff.mpr hx]⟩
    exact ⟨rotation a, by change y/x*x = y; exact div_mul_cancel₀ y hx⟩

def normRotation (x y : ℂ) (h : ‖x‖ = ‖y‖) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  (exists_complex_rotation_of_norm_eq h).choose

@[simp] theorem normRotation_apply (x y : ℂ) (h : ‖x‖ = ‖y‖) :
    normRotation x y h x = y := (exists_complex_rotation_of_norm_eq h).choose_spec

variable {β γ : Type*} [Fintype β] [Fintype γ]

def tensorPhaseEquiv (x y : TensorCoordinates β γ)
    (hc : ∀ i, ‖x.1 i‖ = ‖y.1 i‖)
    (hp₁ : ∀ j, ‖(x.2 j).1‖ = ‖(y.2 j).1‖)
    (hp₂ : ∀ j, ‖(x.2 j).2‖ = ‖(y.2 j).2‖) :
    TensorCoordinates β γ ≃L[ℝ] TensorCoordinates β γ :=
  (ContinuousLinearEquiv.piCongrRight
    (fun i => (normRotation (x.1 i) (y.1 i) (hc i)).toContinuousLinearEquiv)).prodCongr
      (ContinuousLinearEquiv.piCongrRight (fun j =>
        (normRotation (x.2 j).1 (y.2 j).1 (hp₁ j)).toContinuousLinearEquiv.prodCongr
          (normRotation (x.2 j).2 (y.2 j).2 (hp₂ j)).toContinuousLinearEquiv))

variable (x y : TensorCoordinates β γ)
  (hc : ∀ i, ‖x.1 i‖ = ‖y.1 i‖)
  (hp₁ : ∀ j, ‖(x.2 j).1‖ = ‖(y.2 j).1‖)
  (hp₂ : ∀ j, ‖(x.2 j).2‖ = ‖(y.2 j).2‖)

theorem tensorPhaseEquiv_apply : tensorPhaseEquiv x y hc hp₁ hp₂ x = y := by
  apply Prod.ext
  · funext i
    exact normRotation_apply _ _ _
  · funext j
    exact Prod.ext (normRotation_apply _ _ _) (normRotation_apply _ _ _)

theorem tensorPhaseEquiv_measurePreserving :
    MeasurePreserving (tensorPhaseEquiv x y hc hp₁ hp₂) volume volume := by
  exact (volume_preserving_pi (fun i =>
    (normRotation (x.1 i) (y.1 i) (hc i)).measurePreserving)).prod
      (volume_preserving_pi (fun j =>
        (normRotation (x.2 j).1 (y.2 j).1 (hp₁ j)).measurePreserving.prod
          (normRotation (x.2 j).2 (y.2 j).2 (hp₂ j)).measurePreserving))

theorem tensorPositionEnergy_phase (z : TensorCoordinates β γ) :
    tensorPositionEnergy (tensorPhaseEquiv x y hc hp₁ hp₂ z) = tensorPositionEnergy z := by
  apply tensorPositionEnergy_eq_of_norm_eq
  · intro i
    exact (normRotation (x.1 i) (y.1 i) (hc i)).norm_map _
  · intro j
    exact (normRotation (x.2 j).1 (y.2 j).1 (hp₁ j)).norm_map _
  · intro j
    exact (normRotation (x.2 j).2 (y.2 j).2 (hp₂ j)).norm_map _

include hc hp₁ hp₂ in
/-- Actual common-window overlap volumes are unchanged by arbitrary phases
of the complex displacement coordinates. -/
theorem tensor_energyWindow_overlap_eq_of_norm_eq (T : ℝ) :
    volume (overlapSet (energyWindow tensorPositionEnergy T) x) =
      volume (overlapSet (energyWindow tensorPositionEnergy T) y) := by
  let e := tensorPhaseEquiv x y hc hp₁ hp₂
  have hpre : e ⁻¹' overlapSet (energyWindow tensorPositionEnergy T) y =
      overlapSet (energyWindow tensorPositionEnergy T) x := by
    ext z
    change (tensorPositionEnergy (e z) ≤ T ∧ tensorPositionEnergy (e z+y) ≤ T) ↔
      (tensorPositionEnergy z ≤ T ∧ tensorPositionEnergy (z+x) ≤ T)
    rw [← tensorPhaseEquiv_apply x y hc hp₁ hp₂, ← map_add]
    simp only [e, tensorPositionEnergy_phase]
  rw [← hpre]
  exact (tensorPhaseEquiv_measurePreserving x y hc hp₁ hp₂).measure_preimage
    ((isClosed_le continuous_tensorPositionEnergy continuous_const).inter
      ((isClosed_le continuous_tensorPositionEnergy continuous_const).preimage
        (continuous_id.add continuous_const))).measurableSet.nullMeasurableSet

end UnitDistance.Witness
