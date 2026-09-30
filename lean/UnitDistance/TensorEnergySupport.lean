module

public import UnitDistance.TensorEnergy
public import UnitDistance.GeometryReciprocalSupport

@[expose] public section
set_option backward.privateInPublic true


/-!
# Compact pair-log support of the actual common-window overlap

Compactness of the actual common energy window bounds every individual
complex coordinate. The literal reciprocal displacement then bounds each
pair log in both directions, so the original overlap profile has compact
support in the pair-log space.
-/

noncomputable section
open MeasureTheory

namespace UnitDistance.Witness

variable {β γ : Type*} [Fintype β] [Fintype γ]

/-- The original tensor common-window overlap is supported on a compact
pair-log box. This holds for every position measure, including actual volume. -/
theorem tensor_energyWindow_overlap_compactSupport
    (μ : Measure (TensorCoordinates β γ)) (T : ℝ) :
    HasCompactSupport (fun u : γ → ℝ =>
      μ (overlapSet (energyWindow tensorPositionEnergy T) (tensorStep u))) := by
  let plus : γ → TensorCoordinates β γ →+ ℂ := fun j =>
    { toFun := fun x => (x.2 j).1
      map_zero' := rfl
      map_add' := by intros; rfl }
  let minus : γ → TensorCoordinates β γ →+ ℂ := fun j =>
    { toFun := fun x => (x.2 j).2
      map_zero' := rfl
      map_add' := by intros; rfl }
  obtain ⟨R, hR, hbound⟩ :=
    (isCompact_tensorPositionEnergy_window (β := β) (γ := γ) T).isBounded.exists_pos_norm_le
  apply reciprocal_overlap_compactSupport μ _ plus minus tensorStep hR
  · intro x hx j
    change ‖(x.2 j).1‖ ≤ R
    exact (norm_fst_le (x.2 j)).trans
      ((norm_le_pi_norm x.2 j).trans ((norm_snd_le x).trans (hbound x hx)))
  · intro x hx j
    change ‖(x.2 j).2‖ ≤ R
    exact (norm_snd_le (x.2 j)).trans
      ((norm_le_pi_norm x.2 j).trans ((norm_snd_le x).trans (hbound x hx)))
  · intro u j
    change ‖(Real.exp (u j) : ℂ)‖ = Real.exp (u j)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · intro u j
    change ‖(Real.exp (-u j) : ℂ)‖ = Real.exp (-u j)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

end UnitDistance.Witness
