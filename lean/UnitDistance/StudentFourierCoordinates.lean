module

public import UnitDistance.StudentComplexTubeSegments
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section
set_option backward.privateInPublic true


/-! Ordinary four real coordinates for the actual Student Fourier integral. -/

open MeasureTheory

namespace UnitDistance.Witness

/-- Real coordinates in the order `Re z₁, Im z₁, Re z₂, Im z₂`. -/
noncomputable def studentFourCoordinates : (Fin 4 → ℝ) ≃ᵐ (ℂ × ℂ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ))).trans
      (Complex.measurableEquivPi.symm.prodCongr Complex.measurableEquivPi.symm)

theorem studentFourCoordinates_measurePreserving :
    MeasurePreserving studentFourCoordinates volume volume := by
  have h₁ := (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ)
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm _
  have h₂ := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)
  have h₃ := (Complex.volume_preserving_equiv_pi.symm _).prod
    (Complex.volume_preserving_equiv_pi.symm _)
  rw [← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at h₃
  exact h₃.comp (h₂.comp h₁)

@[simp] theorem studentFourCoordinates_apply (x : Fin 4 → ℝ) :
    studentFourCoordinates x =
      ((x 0:ℂ)+(x 1:ℂ)*Complex.I, (x 2:ℂ)+(x 3:ℂ)*Complex.I) := by
  rfl

theorem continuous_studentFourCoordinates : Continuous studentFourCoordinates := by
  simp only [show (studentFourCoordinates : (Fin 4 → ℝ) → ℂ × ℂ) =
    (fun x => ((x 0:ℂ)+(x 1:ℂ)*Complex.I, (x 2:ℂ)+(x 3:ℂ)*Complex.I)) from funext studentFourCoordinates_apply]
  fun_prop

end UnitDistance.Witness
