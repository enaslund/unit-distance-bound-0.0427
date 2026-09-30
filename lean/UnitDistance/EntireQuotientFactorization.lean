module

public import UnitDistance.Upstream.Hadamard.ComplexAnalysis.EntireQuotient
public import UnitDistance.Upstream.Hadamard.ComplexAnalysis.ProximityGrowth

@[expose] public section
set_option backward.privateInPublic true


/-! Affine exponential factorization from equal actual divisors and growth. -/
noncomputable section
open Filter Set
namespace UnitDistance.HeckeAnalysis
open OverflowResidueRH

theorem exists_exp_affine_mul_of_same_divisor
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (horder : ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt g z)
    (hfinite : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤)
    (hfgrowth : HasSubquadraticLogNormGrowthAtInfinity f)
    (hggrowth : HasSubquadraticLogNormGrowthAtInfinity g) :
    ∃ a b : ℂ, ∀ z : ℂ, f z = Complex.exp (a+b*z)*g z := by
  obtain ⟨h, hh, hexp⟩ := exists_differentiable_log_entireQuotientCompletion hf hg horder hfinite
  have hgne : ∃ z : ℂ, g z ≠ 0 := by
    by_contra! hall
    have hgzero : g = 0 := funext hall
    have htop : analyticOrderAt f 0 = ⊤ := by
      rw [horder 0, hgzero, analyticOrderAt_eq_top]
      exact Filter.EventuallyEq.rfl
    exact hfinite 0 htop
  obtain ⟨z₀, hz₀⟩ := hgne
  have hG : AnalyticOnNhd ℂ g univ := fun z _ => hg.analyticAt z
  have hgcodi : g ⁻¹' {0}ᶜ ∈ codiscrete ℂ := hG.preimage_zero_mem_codiscrete hz₀
  have hquot : entireQuotientCompletion f g =ᶠ[codiscrete ℂ] f*g⁻¹ := by
    filter_upwards [hgcodi] with z hz
    exact entireQuotientCompletion_eq_div hf hg (show g z ≠ 0 from hz)
  have hprox := hasSubquadraticProximityGrowthAtInfinity_of_proximity_and_characteristic
    (fun z => (hf.analyticAt z).meromorphicAt) (fun z => (hg.analyticAt z).meromorphicAt)
    hquot (hfgrowth.toProximityGrowthAtInfinity hf.continuous)
    ((hggrowth.toProximityGrowthAtInfinity hg.continuous).toCharacteristicGrowthAtInfinity_of_analytic hG)
  have hqgrowth := hprox.toLogNormGrowthAtInfinity hh hexp
  obtain ⟨a,b,hab⟩ := eq_exp_affine_of_subquadraticLogNormGrowthAtInfinity hqgrowth hh hexp
  refine ⟨a,b,fun z => ?_⟩
  by_cases hgz : g z = 0
  · have hfz : f z = 0 := (hf.analyticAt z).analyticOrderAt_ne_zero.mp (by
      rw [horder z]
      exact (hg.analyticAt z).analyticOrderAt_ne_zero.mpr hgz)
    simp [hfz,hgz]
  · rw [← hab z, entireQuotientCompletion_eq_div hf hg hgz, div_mul_cancel₀ _ hgz]

end UnitDistance.HeckeAnalysis
