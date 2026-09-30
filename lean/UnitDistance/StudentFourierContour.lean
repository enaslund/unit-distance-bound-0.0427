module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
set_option backward.privateInPublic true


/-!
# Horizontal contour shifts justified by actual boundary decay

A Cauchy rectangle identity, vanishing vertical sides, and improper integral
limits justify an infinite horizontal contour shift. The hypotheses describe
ordinary holomorphy, integrability and a pointwise bound; the conclusion is the
actual equality of Lebesgue integrals, not an assumed contour-shift rule.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace UnitDistance.FourierContour

/-- A strip shift with a common pointwise majorant tending to zero at both
real ends. Both horizontal integrals are ordinary Lebesgue integrals. -/
theorem integral_horizontal_shift_eq (f : ℂ → ℂ) (a b : ℝ) (g : ℝ → ℝ)
    (hf : ∀ z : ℂ, z.im ∈ Set.uIcc a b → DifferentiableAt ℂ f z)
    (hfa : Integrable (fun x : ℝ => f ((x:ℂ)+(a:ℂ)*Complex.I)))
    (hfb : Integrable (fun x : ℝ => f ((x:ℂ)+(b:ℂ)*Complex.I)))
    (hbound : ∀ x y : ℝ, y ∈ Set.uIcc a b →
      ‖f ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤ g x)
    (hgp : Tendsto g atTop (𝓝 0)) (hgm : Tendsto g atBot (𝓝 0)) :
    (∫ x : ℝ, f ((x:ℂ)+(a:ℂ)*Complex.I)) =
      ∫ x : ℝ, f ((x:ℂ)+(b:ℂ)*Complex.I) := by
  let V (x : ℝ) : ℂ := ∫ y : ℝ in a..b, f ((x:ℂ)+(y:ℂ)*Complex.I)
  have hV (x : ℝ) : ‖V x‖ ≤ g x*|b-a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy =>
      hbound x y (Set.uIoc_subset_uIcc hy))
  have hVp : Tendsto V atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun x => hV x)
    simpa using hgp.mul_const |b-a|
  have hVm : Tendsto V atBot (𝓝 0) := by
    apply squeeze_zero_norm (fun x => hV x)
    simpa using hgm.mul_const |b-a|
  have hrect (R : ℝ) :
      (∫ x : ℝ in -R..R, f ((x:ℂ)+(a:ℂ)*Complex.I)) -
      (∫ x : ℝ in -R..R, f ((x:ℂ)+(b:ℂ)*Complex.I)) +
        Complex.I*V R - Complex.I*V (-R) = 0 := by
    have hdiff : DifferentiableOn ℂ f
        (Set.uIcc (-R) R ×ℂ Set.uIcc a b) := by
      intro z hz
      exact (hf z hz.2).differentiableWithinAt
    simpa only [smul_eq_mul, V] using
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
        (⟨-R,a⟩:ℂ) (⟨R,b⟩:ℂ) hdiff
  have ha := intervalIntegral_tendsto_integral hfa tendsto_neg_atTop_atBot tendsto_id
  have hb := intervalIntegral_tendsto_integral hfb tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((ha.sub hb).add (hVp.const_mul Complex.I)).sub
    ((hVm.comp tendsto_neg_atTop_atBot).const_mul Complex.I)
  have heq := tendsto_nhds_unique hlim (show Tendsto
      (fun R : ℝ =>
        (∫ x : ℝ in -R..R, f ((x:ℂ)+(a:ℂ)*Complex.I)) -
        (∫ x : ℝ in -R..R, f ((x:ℂ)+(b:ℂ)*Complex.I)) +
          Complex.I*V R - Complex.I*V (-R)) atTop (𝓝 0) by
    simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0)))
  simpa only [mul_zero, add_zero, sub_zero, sub_eq_zero] using heq

end UnitDistance.FourierContour
