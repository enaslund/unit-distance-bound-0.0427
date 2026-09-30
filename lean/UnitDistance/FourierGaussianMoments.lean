module

public import UnitDistance.StudentSchwartzGaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exponential moments of a normalized Fourier Gaussian

The rescaled moment appearing when a Gaussian Fourier kernel is convolved
with an exponential envelope has an explicit integral definition. A proved
Gaussian majorant makes that moment finite and shows it tends to one for
vanishing scale, in each fixed finite dimension.
-/

open MeasureTheory Filter
open scoped Topology

namespace UnitDistance

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The independently defined standard Gaussian mass. -/
noncomputable def gaussianMass (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ := Real.pi ^ ((Module.finrank ℝ V : ℝ)/2)

omit [MeasurableSpace V] [BorelSpace V] in
theorem gaussianMass_pos : 0 < gaussianMass V := Real.rpow_pos_of_pos Real.pi_pos _

theorem integral_standardGaussian :
    (∫ x : V, Real.exp (-‖x‖^2)) = gaussianMass V := by
  simpa [gaussianMass] using GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) (by norm_num : (0:ℝ)<1)

/-- The exponential norm moment after rescaling the normalized Gaussian to
unit quadratic scale. The Fourier-envelope loss uses `b = σ*sqrt(ε)/π`. -/
noncomputable def gaussianExponentialMoment (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (b : ℝ) : ℝ :=
  (∫ x : V, Real.exp (-‖x‖^2+b*‖x‖)) / gaussianMass V

/-- Completing the square gives an integrable Gaussian majorant, uniform
when the linear coefficient is bounded in absolute value. -/
theorem gaussian_linear_majorant {b B t : ℝ} (ht : 0 ≤ t) (hb : |b| ≤ B) :
    Real.exp (-t^2+b*t) ≤ Real.exp (B^2/2) * Real.exp (-(1/2:ℝ)*t^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb' : b ≤ B := (le_abs_self b).trans hb
  nlinarith [sq_nonneg (t-B), mul_le_mul_of_nonneg_right hb' ht]

theorem integrable_gaussian_linear (b : ℝ) :
    Integrable (fun x : V => Real.exp (-‖x‖^2+b*‖x‖)) := by
  have hgi := (gaussianSchwartz (V := V) (1/2) (by norm_num)).integrable (μ := volume)
  apply (hgi.const_mul (Real.exp (|b|^2/2))).mono'
    (by fun_prop : AEStronglyMeasurable (fun x : V => Real.exp (-‖x‖^2+b*‖x‖)) volume)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact gaussian_linear_majorant (norm_nonneg x) le_rfl

/-- A concrete upper bound for the normalized exponential norm moment. -/
theorem gaussianExponentialMoment_le (b : ℝ) :
    gaussianExponentialMoment V b ≤
      Real.exp (b^2/2) * (2:ℝ)^((Module.finrank ℝ V : ℝ)/2) := by
  unfold gaussianExponentialMoment
  have hi := integral_mono (integrable_gaussian_linear (V := V) b)
    ((gaussianSchwartz (V := V) (1/2) (by norm_num)).integrable.const_mul (Real.exp (|b|^2/2)))
    (fun x => gaussian_linear_majorant (norm_nonneg x) le_rfl)
  simp only [gaussianSchwartz_apply, integral_const_mul, sq_abs] at hi
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num : (0:ℝ)<1/2)] at hi
  apply (div_le_iff₀ (gaussianMass_pos (V := V))).mpr
  calc
    _ ≤ Real.exp (b^2/2) * (Real.pi/(1/2))^((Module.finrank ℝ V : ℝ)/2) := hi
    _ = _ := by
      unfold gaussianMass
      rw [show Real.pi/(1/2) = Real.pi*2 by ring, Real.mul_rpow Real.pi_pos.le (by norm_num : (0:ℝ)≤2)]
      ring

@[simp] theorem gaussianExponentialMoment_zero : gaussianExponentialMoment V 0 = 1 := by
  simp only [gaussianExponentialMoment, zero_mul, add_zero, integral_standardGaussian,
    div_self gaussianMass_pos.ne']

/-- Dominated convergence for the actual moment. The dimension is fixed
throughout the limiting argument. -/
theorem gaussianExponentialMoment_tendsto {b : ℕ → ℝ} {B : ℝ}
    (hB : ∀ n, |b n| ≤ B) (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => gaussianExponentialMoment V (b n)) atTop (𝓝 1) := by
  have hdom : Integrable (fun x : V => Real.exp (B^2/2) * Real.exp (-(1/2:ℝ)*‖x‖^2)) :=
    (gaussianSchwartz (V := V) (1/2) (by norm_num)).integrable.const_mul _
  have hlim : Tendsto (fun n => ∫ x : V, Real.exp (-‖x‖^2+b n*‖x‖))
      atTop (𝓝 (∫ x : V, Real.exp (-‖x‖^2))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x : V => Real.exp (B^2/2)*Real.exp (-(1/2:ℝ)*‖x‖^2))
    · intro n; fun_prop
    · exact hdom
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact gaussian_linear_majorant (norm_nonneg x) (hB n)
    · filter_upwards with x
      simpa only [Function.comp_def, zero_mul, add_zero] using! Real.continuous_exp.continuousAt.tendsto.comp
        ((hb.mul_const ‖x‖).const_add (-‖x‖^2))
  have h := hlim.div_const (gaussianMass V)
  simpa [gaussianExponentialMoment, integral_standardGaussian, gaussianMass_pos.ne'] using h

end UnitDistance
