module

public import UnitDistance.PairOverlapTonelli

@[expose] public section
set_option backward.privateInPublic true


/-!
# Removing the spatial variable from the Laplace representation

For positive Laplace parameters, the remaining complex integral is exactly
the unequal-coefficient Gaussian evaluated in `PairOverlapGaussian`.  This
leaves a positive two-dimensional integral in the Laplace parameters.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnitDistance.Witness

def pairOverlapReducedLaplaceKernel
    (α β : ℝ) (h : ℂ) (r t : ℝ) : ℝ :=
  r ^ (α - 1) * t ^ (β - 1) * Real.exp (-(r + t)) *
    Real.exp (-(a * (r * t / (r + t))) * ‖h‖ ^ 2) *
      (Real.pi / (a * (r + t)))

theorem pairOverlapLaplaceAt_mul_eq (α β : ℝ) (h z : ℂ) (r t : ℝ) :
    pairOverlapLaplaceAt α z r * pairOverlapLaplaceAt β (z + h) t =
      (r ^ (α - 1) * t ^ (β - 1) * Real.exp (-(r + t))) *
        Real.exp (-(r * (a * ‖z‖ ^ 2) + t * (a * ‖z + h‖ ^ 2))) := by
  unfold pairOverlapLaplaceAt pairOverlapLaplaceKernel
  rw [show -(r * (1 + a * ‖z‖ ^ 2)) = -r + -(r * (a * ‖z‖ ^ 2)) by ring,
    show -(t * (1 + a * ‖z + h‖ ^ 2)) = -t + -(t * (a * ‖z + h‖ ^ 2)) by ring,
    show -(r + t) = -r + -t by ring,
    show -(r * (a * ‖z‖ ^ 2) + t * (a * ‖z + h‖ ^ 2)) =
      -(r * (a * ‖z‖ ^ 2)) + -(t * (a * ‖z + h‖ ^ 2)) by ring,
    Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
  ring

theorem integrable_pairOverlapLaplaceAt_mul {α β : ℝ} {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (h : ℂ) :
    Integrable (fun z : ℂ =>
      pairOverlapLaplaceAt α z r * pairOverlapLaplaceAt β (z + h) t) := by
  simp_rw [pairOverlapLaplaceAt_mul_eq]
  exact (pairOverlap_scaled_gaussian_integrable witness_basic.2.1 hr ht h).const_mul _

theorem integral_pairOverlapLaplaceAt_mul {α β : ℝ} {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (h : ℂ) :
    (∫ z : ℂ,
      pairOverlapLaplaceAt α z r * pairOverlapLaplaceAt β (z + h) t) =
        pairOverlapReducedLaplaceKernel α β h r t := by
  simp_rw [pairOverlapLaplaceAt_mul_eq]
  rw [integral_const_mul,
    pairOverlap_scaled_gaussian_integral witness_basic.2.1 hr ht h]
  unfold pairOverlapReducedLaplaceKernel
  ring

theorem lintegral_pairOverlapLaplaceAt_mul {α β : ℝ} {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (h : ℂ) :
    (∫⁻ z : ℂ, ENNReal.ofReal
      (pairOverlapLaplaceAt α z r * pairOverlapLaplaceAt β (z + h) t)) =
        ENNReal.ofReal (pairOverlapReducedLaplaceKernel α β h r t) := by
  have hI := integrable_pairOverlapLaplaceAt_mul (α := α) (β := β) hr ht h
  have hn : 0 ≤ᵐ[volume] (fun z : ℂ =>
      pairOverlapLaplaceAt α z r * pairOverlapLaplaceAt β (z + h) t) := by
    filter_upwards with z
    exact mul_nonneg (pairOverlapLaplaceAt_nonneg hr.le)
      (pairOverlapLaplaceAt_nonneg ht.le)
  rw [← ofReal_integral_eq_lintegral_ofReal hI hn,
    integral_pairOverlapLaplaceAt_mul hr ht h]

/-- Exact one-coordinate Student convolution after both Tonelli and Gaussian
reduction. -/
theorem studentConvolution_laplace_reduction {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (h : ℂ) :
    ENNReal.ofReal (Real.Gamma α) * ENNReal.ofReal (Real.Gamma β) *
        (∫⁻ z : ℂ, ENNReal.ofReal
          (studentCoordinate z ^ α * studentCoordinate (z + h) ^ β)) =
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (pairOverlapReducedLaplaceKernel α β h r t) := by
  rw [studentConvolution_laplace_tonelli hα hβ h]
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact lintegral_pairOverlapLaplaceAt_mul hr ht h

end UnitDistance.Witness
