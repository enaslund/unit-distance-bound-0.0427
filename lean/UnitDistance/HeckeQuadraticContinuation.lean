module

public import UnitDistance.HeckeSignedEntire
public import UnitDistance.HeckeSignedPrefactorProduct
public import UnitDistance.HeckeRealRayFactor
public import UnitDistance.RelativeHeckeRightHalfPlane

@[expose] public section
set_option backward.privateInPublic true


/-! The actual signed theta construction supplies quadratic relative entire
continuation once the ordinary zeta Euler identity with its finite dyadic
correction is established. All analytic continuation and growth inputs have
been discharged; the remaining input here is the displayed ordinary Euler
identity in the region of absolute convergence. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue
open scoped Real Classical
namespace UnitDistance.NumberFieldAnalysis
open UnitDistance.HeckeAnalysis
variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]

/-- Convert an ordinary real-ray Euler identity to the identity of the actual
entire completions and the actual signed theta Mellin completion. -/
theorem completedSignedIdentity_of_zetaIdentity
    (r : F) (hr : r^2=7)
    (hreal : nrRealPlaces K = 0)
    (hdegree : Module.finrank ℚ K = 2 * Module.finrank ℚ F)
    (hdiscr : (|discr K| : ℝ) = (|discr F| : ℝ)^2)
    {D : ℂ → ℂ}
    (hidentity : ∀ x : ℝ, 1 < x →
      dedekindZeta K (x:ℂ)*D (x:ℂ) = dedekindZeta F (x:ℂ)*chiFourIdealSeries F (x:ℂ))
    {x : ℝ} (hx : 1 < x) :
    completedDedekindZetaEntire K (x:ℂ)*D (x:ℂ) =
      completedDedekindZetaEntire F (x:ℂ)*heckeSignedCompletion F (x:ℂ) := by
  have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith)
  have hx1 : (x:ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hx)
  rw [completedDedekindZetaEntire_eq K hx0 hx1,
    completedDedekindZetaEntire_eq F hx0 hx1,
    completedDedekindZeta_eq_of_one_lt_re K hx,
    completedDedekindZeta_eq_of_one_lt_re F hx,
    completedZetaPrefactor_eq_mul_signedHeckePrefactor F K hreal hdegree hdiscr,
    heckeSignedCompletion_real F r hr hx]
  calc
    _ = (x:ℂ)*((x:ℂ)-1)*completedZetaPrefactor F (x:ℂ)*signedHeckePrefactor F (x:ℂ)*
        (dedekindZeta K (x:ℂ)*D (x:ℂ)) := by ring
    _ = _ := by rw [hidentity x hx]; ring

/-- The actual signed completion and finite-Euler reflection glue give an entire
relative factor. Only ordinary zeta agreement on the real ray is supplied. -/
theorem exists_entire_relative_factor_of_signed_zetaIdentity
    (r : F) (hr : r^2=7) (hFreal : 0 < nrRealPlaces F)
    (hreal : nrRealPlaces K = 0)
    (hdegree : Module.finrank ℚ K = 2 * Module.finrank ℚ F)
    (hdiscr : (|discr K| : ℝ) = (|discr F| : ℝ)^2)
    {ι : Type*} (S : Finset ι) (q : ι → ℝ) (chi : ι → ℂ)
    (hq : ∀ i ∈ S, 1 < q i) (hchi : ∀ i ∈ S, ‖chi i‖ = 1)
    (hidentity : ∀ x : ℝ, 1 < x →
      dedekindZeta K (x:ℂ)*finiteEulerDenominator S q chi (x:ℂ) =
        dedekindZeta F (x:ℂ)*chiFourIdealSeries F (x:ℂ)) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s := by
  exact exists_entire_relative_factor_of_finite_euler_denominator_real K F S q chi hq hchi
    (differentiable_heckeSignedCompletion F r hr hFreal)
    (fun _ hx => completedSignedIdentity_of_zetaIdentity F K r hr hreal hdegree hdiscr hidentity hx)

/-- Actual finite unramifiedness and relative degree two supply the complete
signature and discriminant normalization for the signed continuation. -/
theorem exists_entire_relative_factor_of_unramified_signed_zetaIdentity
    [Algebra F K] [IsTotallyComplex K]
    (r : F) (hr : r^2=7) (hFreal : 0 < nrRealPlaces F)
    (hquad : Module.finrank F K = 2) (hunr : FiniteUnramified F K)
    {ι : Type*} (S : Finset ι) (q : ι → ℝ) (chi : ι → ℂ)
    (hq : ∀ i ∈ S, 1 < q i) (hchi : ∀ i ∈ S, ‖chi i‖ = 1)
    (hidentity : ∀ x : ℝ, 1 < x →
      dedekindZeta K (x:ℂ)*finiteEulerDenominator S q chi (x:ℂ) =
        dedekindZeta F (x:ℂ)*chiFourIdealSeries F (x:ℂ)) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s := by
  apply exists_entire_relative_factor_of_signed_zetaIdentity F K r hr hFreal
    (IsTotallyComplex.nrRealPlaces_eq_zero K) _ _ S q chi hq hchi hidentity
  · have hd := Module.finrank_mul_finrank ℚ F K
    rw [hquad] at hd
    omega
  · have hd := absoluteDiscriminant_eq_pow_of_finiteUnramified F K hunr
    simpa [hquad, absoluteDiscriminant_eq_abs] using hd

/-- An actual entire completed factor also gives the explicit right-half-plane
factorization used by the public arithmetic-to-geometric target interface. -/
theorem rightHalfPlaneFactor_of_entireFactor {L : ℂ → ℂ}
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    {s : ℂ} (hs : 1 < s.re) : completedZetaRight K s = completedZetaRight F s*L s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have he := hfactor s
  rw [completedDedekindZetaEntire_eq K hs0 hs1,
    completedDedekindZetaEntire_eq F hs0 hs1,
    completedDedekindZeta_eq_of_one_lt_re K hs,
    completedDedekindZeta_eq_of_one_lt_re F hs] at he
  have h := mul_left_cancel₀ (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
    (show s*(s-1)*(completedZetaPrefactor K s*dedekindZeta K s) =
      s*(s-1)*(completedZetaPrefactor F s*dedekindZeta F s*L s) by
      linear_combination he)
  exact h

end UnitDistance.NumberFieldAnalysis
