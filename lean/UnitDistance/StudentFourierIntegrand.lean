module

public import UnitDistance.StudentFourierCoordinates
public import UnitDistance.StudentFourierScaling

@[expose] public section
set_option backward.privateInPublic true


/-! Integrable four-coordinate Fourier integrands on the actual complex tube. -/

open MeasureTheory

namespace UnitDistance.Witness

noncomputable def studentFourPlanes (x : Fin 4 → ℝ) : StudentRealPlane × StudentRealPlane :=
  (WithLp.toLp 2 ![x 0, x 1], WithLp.toLp 2 ![x 2, x 3])

@[simp] theorem studentFourPlanes_zero : studentFourPlanes 0 = 0 := by
  apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

def studentFourTube (y : Fin 4 → ℝ) : Prop :=
  ‖(studentFourPlanes y).1‖ ≤ 1/1000 ∧ ‖(studentFourPlanes y).2‖ ≤ 1/1000

theorem studentFourPlanes_fst_norm_sq (y : Fin 4 → ℝ) :
    ‖(studentFourPlanes y).1‖^2 = (y 0)^2+(y 1)^2 := by
  simp [EuclideanSpace.real_norm_sq_eq, studentFourPlanes, Fin.sum_univ_two]

theorem studentFourPlanes_snd_norm_sq (y : Fin 4 → ℝ) :
    ‖(studentFourPlanes y).2‖^2 = (y 2)^2+(y 3)^2 := by
  simp [EuclideanSpace.real_norm_sq_eq, studentFourPlanes, Fin.sum_univ_two]

theorem studentFourTube_of_abs_le {y z : Fin 4 → ℝ}
    (h : ∀ i, |y i| ≤ |z i|) (hz : studentFourTube z) : studentFourTube y := by
  have hs (i : Fin 4) : (y i)^2 ≤ (z i)^2 := by
    nlinarith [h i, sq_abs (y i), sq_abs (z i), abs_nonneg (y i), abs_nonneg (z i)]
  constructor
  · have hnorm : ‖(studentFourPlanes y).1‖ ≤ ‖(studentFourPlanes z).1‖ := by
      nlinarith [studentFourPlanes_fst_norm_sq y, studentFourPlanes_fst_norm_sq z,
        hs 0, hs 1, norm_nonneg (studentFourPlanes y).1, norm_nonneg (studentFourPlanes z).1]
    exact hnorm.trans hz.1
  · have hnorm : ‖(studentFourPlanes y).2‖ ≤ ‖(studentFourPlanes z).2‖ := by
      nlinarith [studentFourPlanes_snd_norm_sq y, studentFourPlanes_snd_norm_sq z,
        hs 2, hs 3, norm_nonneg (studentFourPlanes y).2, norm_nonneg (studentFourPlanes z).2]
    exact hnorm.trans hz.2

theorem studentFourTube_update_zero {y : Fin 4 → ℝ} (hy : studentFourTube y) (i : Fin 4) :
    studentFourTube (Function.update y i 0) := by
  apply studentFourTube_of_abs_le (z := y) _ hy
  intro j
  by_cases hji : j=i <;> simp [Function.update, hji]

noncomputable def studentFourWeight (y x : Fin 4 → ℝ) : ℂ :=
  complexPairWeight (pairComplexShift (normalizedStudentPair (studentFourCoordinates x))
    (studentFourPlanes y))

theorem continuous_studentFourWeight (y : Fin 4 → ℝ) (hy : studentFourTube y) :
    Continuous (studentFourWeight y) :=
  (continuous_complexPairWeight_shift (studentFourPlanes y) hy.1 hy.2).comp
    continuous_studentFourCoordinates

theorem integrable_studentFourWeight (y : Fin 4 → ℝ) (hy : studentFourTube y) :
    Integrable (studentFourWeight y) :=
  studentFourCoordinates_measurePreserving.integrable_comp_of_integrable
    (integrable_complexPairWeight_shift (studentFourPlanes y) hy.1 hy.2)

theorem integral_norm_studentFourWeight_le (y : Fin 4 → ℝ) (hy : studentFourTube y) :
    (∫ x, ‖studentFourWeight y x‖) ≤ fourierTubeConstant*pairMass := by
  unfold studentFourWeight
  rw [studentFourCoordinates_measurePreserving.integral_comp'
    (fun z => ‖complexPairWeight (pairComplexShift (normalizedStudentPair z) (studentFourPlanes y))‖)]
  exact integral_norm_complexPairWeight_shift_le _ hy.1 hy.2

noncomputable def studentFourKernel (ξ x : Fin 4 → ℝ) : ℂ :=
  ∏ i, FourierContour.fourierKernel (ξ i) (x i:ℂ)

@[simp] theorem norm_studentFourKernel (ξ x : Fin 4 → ℝ) : ‖studentFourKernel ξ x‖ = 1 := by
  simp only [studentFourKernel, norm_prod]
  have h (i : Fin 4) : ‖FourierContour.fourierKernel (ξ i) (x i:ℂ)‖ = 1 := by
    simpa using FourierContour.norm_fourierKernel (ξ i) (x i) 0
  simp only [h, Finset.prod_const_one]

theorem continuous_studentFourKernel (ξ : Fin 4 → ℝ) : Continuous (studentFourKernel ξ) := by
  unfold studentFourKernel FourierContour.fourierKernel
  fun_prop

theorem studentFourKernel_update (ξ x : Fin 4 → ℝ) (i : Fin 4) (t : ℝ) :
    studentFourKernel ξ (Function.update x i t) =
      studentFourKernel ξ (Function.update x i 0)*FourierContour.fourierKernel (ξ i) (t:ℂ) := by
  have hid (u : ℝ) : (fun j => FourierContour.fourierKernel (ξ j) (Function.update x i u j:ℂ)) =
      Function.update (fun j => FourierContour.fourierKernel (ξ j) (x j:ℂ)) i
        (FourierContour.fourierKernel (ξ i) (u:ℂ)) := by
    funext j
    by_cases hji : j=i <;> simp [Function.update, hji]
  simp only [studentFourKernel, hid, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [FourierContour.fourierKernel, mul_comm]

noncomputable def studentFourIntegrand (y ξ x : Fin 4 → ℝ) : ℂ :=
  studentFourWeight y x * studentFourKernel ξ x

@[simp] theorem norm_studentFourIntegrand (y ξ x : Fin 4 → ℝ) :
    ‖studentFourIntegrand y ξ x‖ = ‖studentFourWeight y x‖ := by
  simp [studentFourIntegrand]

theorem integrable_studentFourIntegrand (y ξ : Fin 4 → ℝ) (hy : studentFourTube y) :
    Integrable (studentFourIntegrand y ξ) :=
  (integrable_studentFourWeight y hy).norm.mono'
    ((continuous_studentFourWeight y hy).mul
      (continuous_studentFourKernel ξ)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => (norm_studentFourIntegrand _ _ _).le))

end UnitDistance.Witness
