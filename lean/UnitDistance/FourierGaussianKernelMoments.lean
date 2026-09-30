module

public import UnitDistance.FourierGaussianKernel

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exponential moments of the actual Fourier Gaussian

A scalar change of variables connects the Fourier Gaussian's literal
exponential norm moment to `gaussianExponentialMoment`. Its normalization is
proved from Fourier inversion, avoiding any hidden angular constants.
-/

open MeasureTheory Filter
open scoped Topology

namespace UnitDistance

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def fourierGaussianScale (ε : ℝ) : ℝ := Real.sqrt ε / Real.pi

theorem fourierGaussianScale_pos {ε : ℝ} (hε : 0 < ε) : 0 < fourierGaussianScale ε :=
  div_pos (Real.sqrt_pos.mpr hε) Real.pi_pos

private theorem integral_rescale (f : V → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x, f x) = r^(Module.finrank ℝ V) * ∫ x, f (r • x) := by
  have h := volume.integral_comp_inv_smul_of_nonneg (fun x => f (r • x)) hr.le
  simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, smul_eq_mul] using h

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem fourierGaussianKernel_scale {ε : ℝ} (hε : 0 < ε) (x : V) :
    fourierGaussianKernel ε (fourierGaussianScale ε • x) =
      (Real.pi/ε)^((Module.finrank ℝ V : ℝ)/2) * Real.exp (-‖x‖^2) := by
  unfold fourierGaussianKernel
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (fourierGaussianScale_pos hε)]
  congr 2
  unfold fourierGaussianScale
  rw [mul_pow, div_pow, Real.sq_sqrt hε.le]
  field_simp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem kernel_moment_scale {ε : ℝ} (hε : 0 < ε) (σ : ℝ) (x : V) :
    fourierGaussianKernel ε (fourierGaussianScale ε • x) *
      Real.exp (σ*‖fourierGaussianScale ε • x‖) =
      (Real.pi/ε)^((Module.finrank ℝ V : ℝ)/2) *
        Real.exp (-‖x‖^2+(σ*fourierGaussianScale ε)*‖x‖) := by
  rw [fourierGaussianKernel_scale hε, norm_smul, Real.norm_eq_abs,
    abs_of_pos (fourierGaussianScale_pos hε), mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem integrable_fourierGaussianKernel_moment {ε : ℝ} (hε : 0 < ε) (σ : ℝ) :
    Integrable (fun y : V => fourierGaussianKernel ε y * Real.exp (σ*‖y‖)) := by
  have hc : Integrable (fun x : V => fourierGaussianKernel ε (fourierGaussianScale ε • x) *
      Real.exp (σ*‖fourierGaussianScale ε • x‖)) := by
    simp_rw [kernel_moment_scale hε]
    exact (integrable_gaussian_linear (σ*fourierGaussianScale ε)).const_mul _
  have h := hc.comp_smul (inv_ne_zero (fourierGaussianScale_pos hε).ne')
  simpa only [smul_smul, mul_inv_cancel₀ (fourierGaussianScale_pos hε).ne', one_smul] using h

/-- Exact normalization of the literal Fourier-kernel exponential moment. -/
theorem integral_fourierGaussianKernel_moment {ε : ℝ} (hε : 0 < ε) (σ : ℝ) :
    (∫ y : V, fourierGaussianKernel ε y * Real.exp (σ*‖y‖)) =
      gaussianExponentialMoment V (σ*fourierGaussianScale ε) := by
  have h0 := integral_rescale (fourierGaussianKernel (V := V) ε) (fourierGaussianScale_pos hε)
  rw [integral_fourierGaussianKernel hε] at h0
  simp_rw [fourierGaussianKernel_scale hε, integral_const_mul, integral_standardGaussian] at h0
  rw [integral_rescale _ (fourierGaussianScale_pos hε)]
  simp_rw [kernel_moment_scale hε, integral_const_mul]
  unfold gaussianExponentialMoment
  apply (eq_div_iff gaussianMass_pos.ne').mpr
  calc
    _ = ((fourierGaussianScale ε)^(Module.finrank ℝ V) *
        (Real.pi/ε)^((Module.finrank ℝ V : ℝ)/2) * gaussianMass V) *
        (∫ x : V, Real.exp (-‖x‖^2+(σ*fourierGaussianScale ε)*‖x‖)) := by ring
    _ = _ := by rw [← mul_assoc] at h0; rw [← h0, one_mul]

/-- The precise Fourier-envelope loss for the sequence used in
`gaussianRegularization` tends to one in each fixed dimension. -/
theorem fourierGaussianKernel_moment_tendsto (σ : ℝ) :
    Tendsto (fun n : ℕ => ∫ y : V, fourierGaussianKernel (1/((n:ℝ)+1)) y *
      Real.exp (σ*‖y‖)) atTop (𝓝 1) := by
  have hformula (n : ℕ) := integral_fourierGaussianKernel_moment (V := V)
    (ε := 1/((n:ℝ)+1)) (by positivity) σ
  simp_rw [hformula]
  apply gaussianExponentialMoment_tendsto (B := |σ|/Real.pi)
  · intro n
    rw [abs_mul, abs_of_pos (fourierGaussianScale_pos (by positivity))]
    unfold fourierGaussianScale
    have hs : Real.sqrt (1/((n:ℝ)+1)) ≤ 1 :=
      Real.sqrt_le_one.mpr ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    calc
      |σ| *(Real.sqrt (1/((n:ℝ)+1))/Real.pi) ≤ |σ| *(1/Real.pi) := by
        gcongr
      _ = _ := by ring
  · have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [fourierGaussianScale] using (h.div_const Real.pi).const_mul σ

end UnitDistance
