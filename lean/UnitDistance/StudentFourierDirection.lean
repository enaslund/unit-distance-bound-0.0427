module

public import UnitDistance.StudentFourierIntegrand

@[expose] public section
set_option backward.privateInPublic true


/-! The extremal direction in the product of the two actual Euclidean tube balls. -/

namespace UnitDistance.Witness

noncomputable def studentFourFrequency (ξ : ℂ × ℂ) : Fin 4 → ℝ :=
  ![ξ.1.re, ξ.1.im, ξ.2.re, ξ.2.im]

noncomputable def studentTubeDirectionScale (z : ℂ) : ℝ := -(1/1000)/‖z‖

noncomputable def studentFourDirection (ξ : ℂ × ℂ) : Fin 4 → ℝ :=
  ![studentTubeDirectionScale ξ.1*ξ.1.re, studentTubeDirectionScale ξ.1*ξ.1.im,
    studentTubeDirectionScale ξ.2*ξ.2.re, studentTubeDirectionScale ξ.2*ξ.2.im]

theorem complexToStudentRealPlane_norm (z : ℂ) : ‖complexToStudentRealPlane z‖ = ‖z‖ := by
  nlinarith [complexToStudentRealPlane_norm_sq z, norm_nonneg (complexToStudentRealPlane z), norm_nonneg z]

theorem studentFourPlanes_direction (ξ : ℂ × ℂ) :
    studentFourPlanes (studentFourDirection ξ) =
      (studentTubeDirectionScale ξ.1 • complexToStudentRealPlane ξ.1,
       studentTubeDirectionScale ξ.2 • complexToStudentRealPlane ξ.2) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [studentFourPlanes, studentFourDirection, complexToStudentRealPlane]

theorem studentTubeDirection_norm_le (z : ℂ) :
    ‖studentTubeDirectionScale z • complexToStudentRealPlane z‖ ≤ 1/1000 := by
  rw [norm_smul, complexToStudentRealPlane_norm, Real.norm_eq_abs]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · simp [studentTubeDirectionScale, abs_div, abs_of_nonneg (norm_nonneg z),
      div_mul_cancel₀ _ hz]

theorem studentFourDirection_mem_tube (ξ : ℂ × ℂ) : studentFourTube (studentFourDirection ξ) := by
  unfold studentFourTube
  rw [studentFourPlanes_direction]
  exact ⟨studentTubeDirection_norm_le ξ.1, studentTubeDirection_norm_le ξ.2⟩

theorem studentTubeDirectionScale_dot (z : ℂ) :
    studentTubeDirectionScale z * (z.re^2+z.im^2) = -(1/1000)*‖z‖ := by
  have hsq : z.re^2+z.im^2 = ‖z‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hsq]
  unfold studentTubeDirectionScale
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · field_simp

theorem studentFourDirection_dot (ξ : ℂ × ℂ) :
    (∑ i, studentFourFrequency ξ i*studentFourDirection ξ i) =
      -(1/1000)*(‖ξ.1‖+‖ξ.2‖) := by
  have h₁ := studentTubeDirectionScale_dot ξ.1
  have h₂ := studentTubeDirectionScale_dot ξ.2
  simp [studentFourFrequency, studentFourDirection, Fin.sum_univ_succ]
  linear_combination h₁+h₂

/-- The exact positive Fourier exponent supplied by the certified radius and
the original normalization `sqrt(a)`. -/
noncomputable def studentFourierSigma : ℝ := 2*Real.pi*(1/1000)/Real.sqrt a

theorem studentFourierSigma_pos : 0 < studentFourierSigma := by
  unfold studentFourierSigma
  have ha : 0 < Real.sqrt a := Real.sqrt_pos.mpr witness_basic.2.1
  positivity

theorem studentFourDirection_phase (ξ : ℂ × ℂ) :
    (2*Real.pi/Real.sqrt a)*
      (∑ i, studentFourFrequency ξ i*studentFourDirection ξ i) =
        -studentFourierSigma*(‖ξ.1‖+‖ξ.2‖) := by
  rw [studentFourDirection_dot]
  unfold studentFourierSigma
  ring

end UnitDistance.Witness
