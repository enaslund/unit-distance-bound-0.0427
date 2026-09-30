module

public import UnitDistance.StudentFourierContour

@[expose] public section
set_option backward.privateInPublic true


/-! Polynomial Student decay suffices for the actual infinite contour shift. -/

open MeasureTheory Filter Set
open scoped Topology

namespace UnitDistance.FourierContour

theorem integrable_real_student_decay {r : ℝ} (hr : 1/2 < r) :
    Integrable (fun x : ℝ => (1+x^2)^(-r)) := by
  have h : Integrable (fun x : ℝ => (1+‖x‖^2)^(-(2*r)/2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simp only [Module.finrank_self, Nat.cast_one]; linarith)
  convert! h using 1
  funext x
  rw [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

theorem tendsto_real_student_decay {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => (1+x^2)^(-r)) atTop (𝓝 0) := by
  exact (tendsto_rpow_neg_atTop hr).comp
    (tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)))

theorem tendsto_real_student_decay_atBot {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => (1+x^2)^(-r)) atBot (𝓝 0) := by
  simpa only [Function.comp_def, neg_sq] using
    (tendsto_real_student_decay hr).comp tendsto_neg_atBot_atTop

/-- A holomorphic strip function satisfying a genuine polynomial Student
majorant admits a shift of its Lebesgue integral. Integrability and all boundary
limits are proved here, rather than being supplied as separate inputs. -/
theorem integral_horizontal_shift_eq_of_student_decay (f : ℂ → ℂ) (a b C r : ℝ)
    (hr : 1/2 < r)
    (hf : ∀ z : ℂ, z.im ∈ Set.uIcc a b → DifferentiableAt ℂ f z)
    (hbound : ∀ x y : ℝ, y ∈ Set.uIcc a b →
      ‖f ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤ C*(1+x^2)^(-r)) :
    (∫ x : ℝ, f ((x:ℂ)+(a:ℂ)*Complex.I)) =
      ∫ x : ℝ, f ((x:ℂ)+(b:ℂ)*Complex.I) := by
  have hc (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      Continuous (fun x : ℝ => f ((x:ℂ)+(y:ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hz : ((x:ℂ)+(y:ℂ)*Complex.I).im ∈ Set.uIcc a b := by simpa using hy
    exact ContinuousAt.comp (f := fun t : ℝ => (t:ℂ)+(y:ℂ)*Complex.I)
      (hf _ hz).continuousAt (by fun_prop)
  have hi (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      Integrable (fun x : ℝ => f ((x:ℂ)+(y:ℂ)*Complex.I)) :=
    ((integrable_real_student_decay hr).const_mul C).mono'
      (hc y hy).aestronglyMeasurable (Eventually.of_forall (fun x => hbound x y hy))
  apply integral_horizontal_shift_eq f a b (fun x => C*(1+x^2)^(-r)) hf
    (hi a left_mem_uIcc) (hi b right_mem_uIcc) hbound
  · simpa using (tendsto_real_student_decay (by linarith : 0<r)).const_mul C
  · simpa using (tendsto_real_student_decay_atBot (by linarith : 0<r)).const_mul C

end UnitDistance.FourierContour
