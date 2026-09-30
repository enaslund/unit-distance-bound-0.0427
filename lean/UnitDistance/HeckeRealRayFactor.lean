module

public import UnitDistance.EntireRealRayIdentity
public import UnitDistance.FiniteEulerDenominator

@[expose] public section
set_option backward.privateInPublic true


/-! An actual imprimitive completed identity on the real ray suffices:
identity of entire products removes any need for a separate complex
analytic continuation theorem for the character Dirichlet series. -/
noncomputable section
open NumberField DedekindResidue
namespace UnitDistance.NumberFieldAnalysis
open UnitDistance.HeckeAnalysis
variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

/-- Real-ray agreement of the completed products supplies the entire relative factor. -/
theorem exists_entire_relative_factor_of_finite_euler_denominator_real
    {ι : Type*} (S : Finset ι) (q : ι → ℝ) (chi : ι → ℂ)
    (hq : ∀ i ∈ S, 1 < q i) (hchi : ∀ i ∈ S, ‖chi i‖ = 1)
    {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hidentity : ∀ x : ℝ, 1 < x →
      completedDedekindZetaEntire K (x:ℂ)*finiteEulerDenominator S q chi (x:ℂ) =
        completedDedekindZetaEntire F (x:ℂ)*E (x:ℂ)) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s := by
  have heq := entire_eq_of_real_gt_one
    ((differentiable_completedDedekindZetaEntire K).mul (finiteEulerDenominator_differentiable S q chi))
    ((differentiable_completedDedekindZetaEntire F).mul hE) hidentity
  exact exists_entire_relative_factor_of_finite_euler_denominator K F S q chi hq hchi hE
    (fun s _ => congrFun heq s)

end UnitDistance.NumberFieldAnalysis
