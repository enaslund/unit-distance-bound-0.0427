module

public import UnitDistance.RelativeEuler
public import UnitDistance.ImaginaryQuadraticPrimeFactors

@[expose] public section
set_option backward.privateInPublic true


/-! Actual prime fibers and normalized factors of the extended ideal. -/
noncomputable section
namespace UnitDistance.NumberFieldAnalysis
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical BigOperators
variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

def primeFiberFactorsEquiv (p : HeightOneSpectrum (𝓞 F)) :
    PrimeFiber F K p ≃
      ↥(normalizedFactors (p.asIdeal.map (algebraMap (𝓞 F) (𝓞 K)))).toFinset := by
  letI := p.isMaximal
  refine (primeFiberEquiv F K p).trans (Equiv.subtypeEquivRight (fun Q => ?_))
  exact (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 K)).trans
    ((Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 K) p.ne_bot).trans
      Multiset.mem_toFinset.symm)

@[simp] theorem primeFiberFactorsEquiv_val (p : HeightOneSpectrum (𝓞 F))
    (Q : PrimeFiber F K p) : (primeFiberFactorsEquiv F K p Q).val = Q.val.asIdeal := rfl

theorem prod_primeFiber_eq_factors (p : HeightOneSpectrum (𝓞 F)) (f : Ideal (𝓞 K) → ℂ) :
    (∏ Q : PrimeFiber F K p, f Q.val.asIdeal) =
      ∏ Q ∈ (normalizedFactors (p.asIdeal.map (algebraMap (𝓞 F) (𝓞 K)))).toFinset, f Q := by
  calc
    _ = ∏ Q : ↥(normalizedFactors (p.asIdeal.map (algebraMap (𝓞 F) (𝓞 K)))).toFinset,
        f Q.val := (primeFiberFactorsEquiv F K p).prod_comp (fun Q => f Q.val)
    _ = _ := Finset.prod_coe_sort _ f

theorem oddPrimeFiber_factor_product [Fact (KummerInvariant.Nonsquare (-1:F))]
    (i : K) (hi : i^2=(-1:K)) (hdegree : Module.finrank F K=2)
    (p : HeightOneSpectrum (𝓞 F)) (h2 : (2:𝓞 F) ∉ p.asIdeal) (s : ℂ) :
    (∏ Q : PrimeFiber F K p, (1-(Ideal.absNorm Q.val.asIdeal:ℂ)^(-s))) =
      (1-(Ideal.absNorm p.asIdeal:ℂ)^(-s)) *
        (1-chiFourComplex (Ideal.absNorm p.asIdeal)*(Ideal.absNorm p.asIdeal:ℂ)^(-s)) := by
  letI := p.isMaximal
  rw [prod_primeFiber_eq_factors F K p (fun Q => 1-(Ideal.absNorm Q:ℂ)^(-s))]
  exact ImaginaryQuadraticEuler.oddPrime_factor_product F K i hi hdegree p.asIdeal p.ne_bot h2 s

end UnitDistance.NumberFieldAnalysis
