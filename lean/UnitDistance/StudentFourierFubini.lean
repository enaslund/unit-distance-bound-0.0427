module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! Fubini transfer of a scalar coordinate integral identity. -/

open MeasureTheory

namespace UnitDistance.FourierContour

theorem integral_eq_const_mul_of_coordinate {n : ℕ}
    {f g : (Fin (n+1) → ℝ) → ℂ} (hf : Integrable f) (hg : Integrable g)
    (i : Fin (n+1)) (c : ℂ)
    (h : ∀ x, (∫ t : ℝ, f (Function.update x i t)) =
      c*(∫ t : ℝ, g (Function.update x i t))) :
    (∫ x, f x) = c*(∫ x, g x) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have he : MeasurePreserving e.symm volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm _
  have hf' : Integrable (fun p => f (e.symm p)) := he.integrable_comp_of_integrable hf
  have hg' : Integrable (fun p => g (e.symm p)) := he.integrable_comp_of_integrable hg
  rw [← he.integral_comp' f, ← he.integral_comp' g, Measure.volume_eq_prod,
    integral_prod_symm _ hf', integral_prod_symm _ hg', ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hx := h (i.insertNth 0 x)
  simpa [Fin.update_insertNth, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv] using hx

end UnitDistance.FourierContour
