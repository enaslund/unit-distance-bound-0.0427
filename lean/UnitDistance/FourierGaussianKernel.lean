module

public import UnitDistance.FourierGaussianMoments
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual positive Fourier Gaussian kernel

The Fourier convention is Mathlib's ordinary `exp(-2π i inner(x,ξ))`.
The kernel below is identified with the Fourier transform of the actual
Gaussian damping; its parameters are not chosen by a success predicate.
-/

open MeasureTheory Filter FourierTransform
open scoped Topology

namespace UnitDistance

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def complexGaussianSchwartz (ε : ℝ) (hε : 0 < ε) : SchwartzMap V ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (gaussianSchwartz ε hε)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem complexGaussianSchwartz_apply (ε : ℝ) (hε : 0 < ε) (x : V) :
    complexGaussianSchwartz ε hε x = ((Real.exp (-ε*‖x‖^2)) : ℝ) := rfl

/-- The ordinary positive Fourier kernel of `exp(-ε*norm(x)^2)`. -/
noncomputable def fourierGaussianKernel (ε : ℝ) (y : V) : ℝ :=
  (Real.pi/ε)^((Module.finrank ℝ V : ℝ)/2) * Real.exp (-Real.pi^2*‖y‖^2/ε)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem fourierGaussianKernel_pos {ε : ℝ} (hε : 0 < ε) (y : V) :
    0 < fourierGaussianKernel ε y := by
  unfold fourierGaussianKernel
  exact mul_pos (Real.rpow_pos_of_pos (div_pos Real.pi_pos hε) _) (Real.exp_pos _)

theorem fourier_complexGaussianSchwartz {ε : ℝ} (hε : 0 < ε) (y : V) :
    𝓕 (complexGaussianSchwartz (V := V) ε hε) y = ((fourierGaussianKernel ε y) : ℝ) := by
  rw [SchwartzMap.fourier_coe]
  have h := fourier_gaussian_innerProductSpace (V := V) (b := (ε : ℂ)) hε y
  convert! h using 1
  · apply congrArg (fun f : V → ℂ => 𝓕 f y)
    funext x
    simp only [complexGaussianSchwartz_apply, Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_pow]
  · unfold fourierGaussianKernel
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (div_pos Real.pi_pos hε).le]
    simp only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow]

/-- The Fourier kernel is integrable because it is the real part of a
Schwartz transform; no moment or tail estimate is assumed. -/
theorem integrable_fourierGaussianKernel {ε : ℝ} (hε : 0 < ε) :
    Integrable (fourierGaussianKernel (V := V) ε) := by
  have hi := (𝓕 (complexGaussianSchwartz (V := V) ε hε)).integrable (μ := volume)
  have hreal := hi.re
  change Integrable (fun x => ((𝓕 (complexGaussianSchwartz (V := V) ε hε)) x).re) at hreal
  simpa only [fourier_complexGaussianSchwartz hε, Complex.ofReal_re] using hreal

/-- Fourier inversion at zero normalizes this exact positive kernel to one. -/
theorem integral_fourierGaussianKernel {ε : ℝ} (hε : 0 < ε) :
    (∫ y : V, fourierGaussianKernel ε y) = 1 := by
  have h := congrArg (fun g : SchwartzMap V ℂ => g (0 : V))
    (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap V ℂ) (complexGaussianSchwartz (V := V) ε hε))
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at h
  simp [fourier_complexGaussianSchwartz hε, complexGaussianSchwartz_apply,
    integral_complex_ofReal] at h
  exact_mod_cast h

end UnitDistance
