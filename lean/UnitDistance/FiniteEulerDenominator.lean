module

public import UnitDistance.EntireReflectionGlue

@[expose] public section
set_option backward.privateInPublic true


/-! A finite unitary Euler denominator has zeros only on the imaginary axis;
reflection therefore removes it from an actual imprimitive relative completion. -/
noncomputable section
open Filter Set Complex NumberField DedekindResidue
open scoped Topology BigOperators
namespace UnitDistance.HeckeAnalysis

def finiteEulerDenominator {ι : Type*} (S : Finset ι) (q : ι → ℝ) (chi : ι → ℂ)
    (s : ℂ) : ℂ := ∏ i ∈ S, (1-chi i*Complex.exp (-s*(Real.log (q i):ℂ)))

theorem finiteEulerDenominator_differentiable {ι : Type*}
    (S : Finset ι) (q : ι → ℝ) (chi : ι → ℂ) :
    Differentiable ℂ (finiteEulerDenominator S q chi) := by
  unfold finiteEulerDenominator
  fun_prop

theorem finiteEulerDenominator_ne_zero {ι : Type*}
    (S : Finset ι) (q : ι → ℝ) (chi : ι → ℂ)
    (hq : ∀ i ∈ S, 1 < q i) (hchi : ∀ i ∈ S, ‖chi i‖ = 1)
    {s : ℂ} (hs : s.re ≠ 0) : finiteEulerDenominator S q chi s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi hzero
  have hmul : chi i*Complex.exp (-s*(Real.log (q i):ℂ)) = 1 := sub_eq_zero.mp hzero |>.symm
  have hn := congrArg norm hmul
  rw [norm_mul, hchi i hi, one_mul, norm_one, Complex.norm_exp] at hn
  have he : (-s*(Real.log (q i):ℂ)).re = 0 := Real.exp_injective (by simpa only [Real.exp_zero] using hn)
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at he
  have hlog : Real.log (q i) ≠ 0 := (Real.log_pos (hq i hi)).ne'
  exact hs (neg_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hlog))

end UnitDistance.HeckeAnalysis

namespace UnitDistance.NumberFieldAnalysis
open UnitDistance.HeckeAnalysis
variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

/-- A checked imprimitive completion with finitely many unitary Euler factors
removed supplies the actual entire relative continuation. -/
theorem exists_entire_relative_factor_of_finite_euler_denominator
    {ι : Type*} (S : Finset ι) (q : ι → ℝ) (chi : ι → ℂ)
    (hq : ∀ i ∈ S, 1 < q i) (hchi : ∀ i ∈ S, ‖chi i‖ = 1)
    {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hidentity : ∀ s : ℂ, 1 < s.re →
      completedDedekindZetaEntire K s*finiteEulerDenominator S q chi s =
        completedDedekindZetaEntire F s*E s) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s := by
  exact exists_entire_factor_of_imprimitive
    (differentiable_completedDedekindZetaEntire K) (differentiable_completedDedekindZetaEntire F)
    hE (finiteEulerDenominator_differentiable S q chi)
    (completedDedekindEntire_one_sub K) (completedDedekindEntire_one_sub F)
    (completedDedekindEntire_one_ne_zero F)
    (fun _ hs => finiteEulerDenominator_ne_zero S q chi hq hchi hs) hidentity

end UnitDistance.NumberFieldAnalysis
