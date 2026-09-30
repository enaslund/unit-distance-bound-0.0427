module

public import UnitDistance.FourierGaussianConvolution
public import UnitDistance.FourierGaussianKernelMoments
public import UnitDistance.StudentSchwartzCoordinates

@[expose] public section
set_option backward.privateInPublic true


/-!
# Preservation of exponential Fourier envelopes under Gaussian regularization

The original Fourier envelope is an independently stated analytic inequality.
Its preservation is proved for the genuine Schwartz sequence, with the
literal positive Fourier-Gaussian moment as loss. This loss tends to one,
uniformly in frequency, before dimension grows.
-/

open MeasureTheory Filter FourierTransform
open scoped Topology

namespace UnitDistance

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Fourier multiplication by the actual damping is convolution with its
proved positive normalized Fourier Gaussian. -/
theorem fourier_gaussianRegularization_eq {f : V → ℝ} (hf : f.HasTemperateGrowth)
    (hfi : Integrable f) (n : ℕ) (ξ : V) :
    𝓕 (gaussianRegularization f n) ξ =
      ∫ y, 𝓕 (fun x : V => (f x : ℂ)) (ξ-y) *
        (fourierGaussianKernel (1/((n:ℝ)+1)) y : ℂ) := by
  have hg := fourier_mul_schwartz_eq_integral hfi.ofReal
    (complexGaussianSchwartz (V := V) (1/((n:ℝ)+1)) (by positivity)) ξ
  rw [SchwartzMap.fourier_coe]
  calc
    _ = 𝓕 (fun x : V => (f x : ℂ)*
        complexGaussianSchwartz (V := V) (1/((n:ℝ)+1)) (by positivity) x) ξ := by
      apply congrArg (fun g : V → ℂ => 𝓕 g ξ)
      funext x
      rw [gaussianRegularization_apply hf, complexGaussianSchwartz_apply, Complex.ofReal_mul]
    _ = _ := by
      simpa only [fourier_complexGaussianSchwartz
        (by positivity : (0:ℝ)<1/((n:ℝ)+1))] using! hg

/-- Quantitative preservation of an established exponential Fourier bound.
The explicit multiplicative loss is the actual Gaussian norm moment. -/
theorem gaussianRegularization_fourier_envelope {f : V → ℝ} (hf : f.HasTemperateGrowth)
    (hfi : Integrable f) {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hbound : ∀ ξ, ‖𝓕 (fun x : V => (f x : ℂ)) ξ‖ ≤ C*Real.exp (-σ*‖ξ‖))
    (n : ℕ) (ξ : V) :
    ‖𝓕 (gaussianRegularization f n) ξ‖ ≤
      C*Real.exp (-σ*‖ξ‖) *
        gaussianExponentialMoment V (σ*fourierGaussianScale (1/((n:ℝ)+1))) := by
  rw [fourier_gaussianRegularization_eq hf hfi]
  have hF : AEStronglyMeasurable (𝓕 (fun x : V => (f x : ℂ))) volume :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hfi.ofReal).aestronglyMeasurable
  have hK : AEStronglyMeasurable (fourierGaussianKernel (V := V) (1/((n:ℝ)+1))) volume := by
    unfold fourierGaussianKernel
    fun_prop
  have h := convolution_exponential_envelope hC hσ hF hK
    (fun y => (fourierGaussianKernel_pos (by positivity : (0:ℝ)<1/((n:ℝ)+1)) y).le)
    hbound (integrable_fourierGaussianKernel_moment (by positivity) σ) ξ
  rwa [integral_fourierGaussianKernel_moment (by positivity)] at h

/-- Every fixed loss greater than one holds uniformly over all frequencies
for sufficiently weak damping. No original Fourier tail is smuggled into
the approximation hypotheses. -/
theorem gaussianRegularization_fourier_envelope_eventually {f : V → ℝ}
    (hf : f.HasTemperateGrowth) (hfi : Integrable f) {C σ : ℝ}
    (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hbound : ∀ ξ, ‖𝓕 (fun x : V => (f x : ℂ)) ξ‖ ≤ C*Real.exp (-σ*‖ξ‖))
    {η : ℝ} (hη : 1 < η) :
    ∀ᶠ n in atTop, ∀ ξ : V,
      ‖𝓕 (gaussianRegularization f n) ξ‖ ≤ η*C*Real.exp (-σ*‖ξ‖) := by
  have hlim := fourierGaussianKernel_moment_tendsto (V := V) σ
  have hm := hlim.eventually (gt_mem_nhds hη)
  filter_upwards [hm] with n hn
  intro ξ
  have hb := gaussianRegularization_fourier_envelope hf hfi hC hσ hbound n ξ
  rw [← integral_fourierGaussianKernel_moment (by positivity)] at hb
  calc
    _ ≤ _ := hb
    _ ≤ (C*Real.exp (-σ*‖ξ‖))*η :=
      mul_le_mul_of_nonneg_left hn.le (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by ring

/-- The same quantitative bound for any specified seminorm with a proved
Euclidean upper bound; the seminorm in the original envelope is preserved. -/
theorem gaussianRegularization_seminorm_fourier_envelope
    (q : Seminorm ℝ V) {B : ℝ} (hq : ∀ y, q y ≤ B*‖y‖)
    {f : V → ℝ} (hf : f.HasTemperateGrowth) (hfi : Integrable f)
    {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hbound : ∀ ξ, ‖𝓕 (fun x : V => (f x : ℂ)) ξ‖ ≤ C*Real.exp (-σ*q ξ))
    (n : ℕ) (ξ : V) :
    ‖𝓕 (gaussianRegularization f n) ξ‖ ≤ C*Real.exp (-σ*q ξ) *
      gaussianExponentialMoment V ((σ*B)*fourierGaussianScale (1/((n:ℝ)+1))) := by
  rw [fourier_gaussianRegularization_eq hf hfi]
  have hF : AEStronglyMeasurable (𝓕 (fun x : V => (f x : ℂ))) volume :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hfi.ofReal).aestronglyMeasurable
  have hK : AEStronglyMeasurable (fourierGaussianKernel (V := V) (1/((n:ℝ)+1))) volume := by
    unfold fourierGaussianKernel
    fun_prop
  have h := convolution_seminorm_exponential_envelope q hq hC hσ hF hK
    (fun y => (fourierGaussianKernel_pos (by positivity : (0:ℝ)<1/((n:ℝ)+1)) y).le)
    hbound (integrable_fourierGaussianKernel_moment (by positivity) (σ*B)) ξ
  rwa [integral_fourierGaussianKernel_moment (by positivity)] at h

theorem gaussianRegularization_seminorm_fourier_envelope_eventually
    (q : Seminorm ℝ V) {B : ℝ} (hq : ∀ y, q y ≤ B*‖y‖)
    {f : V → ℝ} (hf : f.HasTemperateGrowth) (hfi : Integrable f)
    {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hbound : ∀ ξ, ‖𝓕 (fun x : V => (f x : ℂ)) ξ‖ ≤ C*Real.exp (-σ*q ξ))
    {η : ℝ} (hη : 1 < η) :
    ∀ᶠ n in atTop, ∀ ξ : V,
      ‖𝓕 (gaussianRegularization f n) ξ‖ ≤ η*C*Real.exp (-σ*q ξ) := by
  have hm := (fourierGaussianKernel_moment_tendsto (V := V) (σ*B)).eventually (gt_mem_nhds hη)
  filter_upwards [hm] with n hn
  intro ξ
  have hb := gaussianRegularization_seminorm_fourier_envelope q hq hf hfi hC hσ hbound n ξ
  rw [← integral_fourierGaussianKernel_moment (by positivity)] at hb
  calc
    _ ≤ _ := hb
    _ ≤ (C*Real.exp (-σ*q ξ))*η :=
      mul_le_mul_of_nonneg_left hn.le (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by ring

namespace Witness

/-- The exact published Student block satisfies the proved regularization
contract in ordinary Euclidean four-space. The remaining analytic input is
the explicitly displayed Fourier envelope of its original weight. -/
theorem pairSchwartzApprox_fourier_envelope_eventually {C σ : ℝ}
    (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hbound : ∀ ξ : StudentEuclideanPair,
      ‖𝓕 (fun x : StudentEuclideanPair => ((pairProfile (WithLp.ofLp x)^p : ℝ) : ℂ)) ξ‖ ≤
        C*Real.exp (-σ*‖ξ‖)) {η : ℝ} (hη : 1 < η) :
    ∀ᶠ n in atTop, ∀ ξ : StudentEuclideanPair,
      ‖𝓕 (pairSchwartzApprox n) ξ‖ ≤ η*C*Real.exp (-σ*‖ξ‖) := by
  have hfi : Integrable (fun x : StudentEuclideanPair => pairProfile (WithLp.ofLp x)^p) :=
    (studentPairCoordinates_measurePreserving.integrable_comp
      integrable_pairMass.aestronglyMeasurable).mpr integrable_pairMass
  exact gaussianRegularization_fourier_envelope_eventually
    (temperateGrowth_pairWeight_coordinates studentPairCoordinates.toContinuousLinearMap)
    hfi hC hσ hbound hη

/-- The manuscript's sum of the two ordinary complex frequency norms. -/
noncomputable def pairFrequencySeminorm : Seminorm ℝ StudentEuclideanPair :=
  (normSeminorm ℝ ℂ).comp ((LinearMap.fst ℝ ℂ ℂ).comp studentPairCoordinates.toLinearMap) +
  (normSeminorm ℝ ℂ).comp ((LinearMap.snd ℝ ℂ ℂ).comp studentPairCoordinates.toLinearMap)

@[simp] theorem pairFrequencySeminorm_apply (x : StudentEuclideanPair) :
    pairFrequencySeminorm x = ‖(WithLp.ofLp x).1‖ + ‖(WithLp.ofLp x).2‖ := rfl

theorem pairFrequencySeminorm_le (x : StudentEuclideanPair) :
    pairFrequencySeminorm x ≤ 2*‖x‖ := by
  rw [pairFrequencySeminorm_apply]
  have hf : ‖(WithLp.ofLp x).1‖ ≤ ‖x‖ := WithLp.norm_fst_le ℂ x
  have hs : ‖(WithLp.ofLp x).2‖ ≤ ‖x‖ := WithLp.norm_snd_le ℂ x
  linarith

/-- Regularization preserves exactly the sum-of-coordinate-norms envelope
used by the manuscript, uniformly in both complex frequency coordinates. -/
theorem pairSchwartzApprox_coordinate_fourier_envelope_eventually {C σ : ℝ}
    (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hbound : ∀ ξ : StudentEuclideanPair,
      ‖𝓕 (fun x : StudentEuclideanPair => ((pairProfile (WithLp.ofLp x)^p : ℝ) : ℂ)) ξ‖ ≤
        C*Real.exp (-σ*(‖(WithLp.ofLp ξ).1‖+‖(WithLp.ofLp ξ).2‖)))
    {η : ℝ} (hη : 1 < η) :
    ∀ᶠ n in atTop, ∀ ξ : StudentEuclideanPair,
      ‖𝓕 (pairSchwartzApprox n) ξ‖ ≤
        η*C*Real.exp (-σ*(‖(WithLp.ofLp ξ).1‖+‖(WithLp.ofLp ξ).2‖)) := by
  have hfi : Integrable (fun x : StudentEuclideanPair => pairProfile (WithLp.ofLp x)^p) :=
    (studentPairCoordinates_measurePreserving.integrable_comp
      integrable_pairMass.aestronglyMeasurable).mpr integrable_pairMass
  exact gaussianRegularization_seminorm_fourier_envelope_eventually pairFrequencySeminorm
    pairFrequencySeminorm_le
    (temperateGrowth_pairWeight_coordinates studentPairCoordinates.toContinuousLinearMap)
    hfi hC hσ hbound hη

end Witness
end UnitDistance
