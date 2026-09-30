module

public import UnitDistance.PairOverlapGaussian
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

@[expose] public section
set_option backward.privateInPublic true


/-!
# Laplace representation for the Student overlap

The lemmas here are the first exact change of variables in the published
overlap certificate.  They turn a Student denominator into a positive
Laplace integral and record the Gaussian integral obtained after two such
representations.
-/

noncomputable section

open MeasureTheory Set

namespace UnitDistance

/-- Positive Laplace kernel for `(1+x)⁻ᵅ`. -/
def pairOverlapLaplaceKernel (α x r : ℝ) : ℝ :=
  r ^ (α - 1) * Real.exp (-(r * (1 + x)))

theorem pairOverlapLaplaceKernel_nonneg {α x r : ℝ} (hr : 0 ≤ r) :
    0 ≤ pairOverlapLaplaceKernel α x r := by
  unfold pairOverlapLaplaceKernel
  positivity

theorem pairOverlap_laplace_integral {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) :
    (∫ r in Ioi (0 : ℝ), pairOverlapLaplaceKernel α x r) =
      (1 + x) ^ (-α) * Real.Gamma α := by
  have hbase : 0 < 1 + x := by linarith
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hα hbase
  calc
    (∫ r in Ioi (0 : ℝ), pairOverlapLaplaceKernel α x r) =
        ∫ r in Ioi (0 : ℝ), r ^ (α - 1) *
          Real.exp (-((1 + x) * r)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      unfold pairOverlapLaplaceKernel
      rw [mul_comm r (1 + x)]
    _ = (1 / (1 + x)) ^ α * Real.Gamma α := h
    _ = (1 + x) ^ (-α) * Real.Gamma α := by
      rw [show (1 / (1 + x)) ^ α = (1 + x) ^ (-α) by
        rw [one_div, Real.inv_rpow hbase.le, ← Real.rpow_neg hbase.le]]

/-- Pointwise Laplace representation, normalized by the positive Gamma
factor. -/
theorem pairOverlap_student_laplace {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) :
    (1 + x) ^ (-α) =
      (Real.Gamma α)⁻¹ *
        ∫ r in Ioi (0 : ℝ), pairOverlapLaplaceKernel α x r := by
  rw [pairOverlap_laplace_integral hα hx]
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα)]

/-- The spatial integral of the two Gaussian factors produced by Laplace
parameters `r,t`, including the common Student scale `a`. -/
theorem pairOverlap_scaled_gaussian_integral {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : 0 < t) (h : ℂ) :
    (∫ z : ℂ, Real.exp (-(r * (a * ‖z‖ ^ 2) +
        t * (a * ‖z + h‖ ^ 2)))) =
      Real.exp (-(a * (r * t / (r + t))) * ‖h‖ ^ 2) *
        (Real.pi / (a * (r + t))) := by
  have har : 0 < a * r := mul_pos ha hr
  have hat : 0 < a * t := mul_pos ha ht
  have hg := pairOverlap_gaussian_integral har hat h
  have hcoef : (a * r) * (a * t) / (a * r + a * t) =
      a * (r * t / (r + t)) := by
    have ha0 := ha.ne'
    have hrt0 : r + t ≠ 0 := (add_pos hr ht).ne'
    field_simp [ha0, hrt0]
  have hden : a * r + a * t = a * (r + t) := by ring
  calc
    (∫ z : ℂ, Real.exp (-(r * (a * ‖z‖ ^ 2) +
        t * (a * ‖z + h‖ ^ 2)))) =
        ∫ z : ℂ, Real.exp (-((a * r) * ‖z‖ ^ 2 +
          (a * t) * ‖z + h‖ ^ 2)) := by
      apply integral_congr_ae
      filter_upwards with z
      congr 1
      ring
    _ = Real.exp (-((a * r) * (a * t) / (a * r + a * t)) * ‖h‖ ^ 2) *
        (Real.pi / (a * r + a * t)) := hg
    _ = _ := by rw [hcoef, hden]

theorem pairOverlap_scaled_gaussian_integrable {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : 0 < t) (h : ℂ) :
    Integrable (fun z : ℂ => Real.exp (-(r * (a * ‖z‖ ^ 2) +
      t * (a * ‖z + h‖ ^ 2)))) := by
  have hg := pairOverlap_gaussian_integrable (mul_pos ha hr) (mul_pos ha ht) h
  apply hg.congr
  filter_upwards with z
  congr 1
  ring

end UnitDistance
