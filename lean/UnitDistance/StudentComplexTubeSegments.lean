module

public import UnitDistance.StudentComplexSlices

@[expose] public section
set_option backward.privateInPublic true


/-! Endpoint membership suffices for the actual coordinate contour tube. -/

open MeasureTheory Set

namespace UnitDistance.Witness

theorem studentRealPlaneUpdate_norm_sq (x : StudentRealPlane) (i : Fin 2) (t : ℝ) :
    ‖studentRealPlaneUpdate x i t‖^2 = t^2+(x i.rev)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  fin_cases i
  · change ∑ j : Fin 2, (studentRealPlaneUpdate x 0 t j)^2 = t^2+(x 1)^2
    simp [studentRealPlaneUpdate, Fin.sum_univ_two]
  · change ∑ j : Fin 2, (studentRealPlaneUpdate x 1 t j)^2 = t^2+(x 0)^2
    simp [studentRealPlaneUpdate, Fin.sum_univ_two, add_comm]

theorem studentRealPlaneUpdate_norm_le_of_abs_le (x : StudentRealPlane) (i : Fin 2)
    {t u : ℝ} (h : |t| ≤ |u|) :
    ‖studentRealPlaneUpdate x i t‖ ≤ ‖studentRealPlaneUpdate x i u‖ := by
  have ht := studentRealPlaneUpdate_norm_sq x i t
  have hu := studentRealPlaneUpdate_norm_sq x i u
  nlinarith [sq_abs t, sq_abs u, abs_nonneg t, abs_nonneg u,
    norm_nonneg (studentRealPlaneUpdate x i t), norm_nonneg (studentRealPlaneUpdate x i u)]

/-- The interval condition used by a coordinate shift follows just from its
two endpoint Euclidean bounds. -/
theorem studentRealPlaneUpdate_norm_le_of_mem_uIcc (x : StudentRealPlane) (i : Fin 2)
    {a₀ b₀ t ρ : ℝ} (ha : ‖studentRealPlaneUpdate x i a₀‖ ≤ ρ)
    (hb : ‖studentRealPlaneUpdate x i b₀‖ ≤ ρ) (ht : t ∈ Set.uIcc a₀ b₀) :
    ‖studentRealPlaneUpdate x i t‖ ≤ ρ := by
  have htAbs : |t| ≤ max |a₀| |b₀| := by
    rcases le_total a₀ b₀ with hab | hba
    · rw [Set.uIcc_of_le hab] at ht
      exact abs_le_max_abs_abs ht.1 ht.2
    · rw [Set.uIcc_of_ge hba] at ht
      simpa only [max_comm] using abs_le_max_abs_abs ht.1 ht.2
  rcases le_total |a₀| |b₀| with hab | hba
  · rw [max_eq_right hab] at htAbs
    exact (studentRealPlaneUpdate_norm_le_of_abs_le x i htAbs).trans hb
  · rw [max_eq_left hba] at htAbs
    exact (studentRealPlaneUpdate_norm_le_of_abs_le x i htAbs).trans ha

/-- The actual first-plane Fourier contour needs only endpoint membership in
the specified Euclidean tube; all intermediate membership is proved. -/
theorem complexPairWeightFstSlice_fourier_shift_of_endpoints
    (z : StudentComplexPlane × StudentComplexPlane) (i : Fin 2) (a₀ b₀ ξ : ℝ)
    (ha : ‖studentRealPlaneUpdate (studentComplexPlaneImag z.1) i a₀‖ ≤ 1/1000)
    (hb : ‖studentRealPlaneUpdate (studentComplexPlaneImag z.1) i b₀‖ ≤ 1/1000)
    (hz2 : ‖studentComplexPlaneImag z.2‖ ≤ 1/1000) :
    (Real.exp (2*Real.pi*ξ*a₀):ℂ) *
      (∫ x : ℝ, complexPairWeightFstSlice z i ((x:ℂ)+(a₀:ℂ)*Complex.I)*
        FourierContour.fourierKernel ξ (x:ℂ)) =
    (Real.exp (2*Real.pi*ξ*b₀):ℂ) *
      (∫ x : ℝ, complexPairWeightFstSlice z i ((x:ℂ)+(b₀:ℂ)*Complex.I)*
        FourierContour.fourierKernel ξ (x:ℂ)) :=
  complexPairWeightFstSlice_fourier_shift z i a₀ b₀ ξ
    (fun _ ht => studentRealPlaneUpdate_norm_le_of_mem_uIcc _ i ha hb ht) hz2

theorem complexPairWeightSndSlice_fourier_shift_of_endpoints
    (z : StudentComplexPlane × StudentComplexPlane) (i : Fin 2) (a₀ b₀ ξ : ℝ)
    (hz1 : ‖studentComplexPlaneImag z.1‖ ≤ 1/1000)
    (ha : ‖studentRealPlaneUpdate (studentComplexPlaneImag z.2) i a₀‖ ≤ 1/1000)
    (hb : ‖studentRealPlaneUpdate (studentComplexPlaneImag z.2) i b₀‖ ≤ 1/1000) :
    (Real.exp (2*Real.pi*ξ*a₀):ℂ) *
      (∫ x : ℝ, complexPairWeightSndSlice z i ((x:ℂ)+(a₀:ℂ)*Complex.I)*
        FourierContour.fourierKernel ξ (x:ℂ)) =
    (Real.exp (2*Real.pi*ξ*b₀):ℂ) *
      (∫ x : ℝ, complexPairWeightSndSlice z i ((x:ℂ)+(b₀:ℂ)*Complex.I)*
        FourierContour.fourierKernel ξ (x:ℂ)) :=
  complexPairWeightSndSlice_fourier_shift z i a₀ b₀ ξ hz1
    (fun _ ht => studentRealPlaneUpdate_norm_le_of_mem_uIcc _ i ha hb ht)

end UnitDistance.Witness
