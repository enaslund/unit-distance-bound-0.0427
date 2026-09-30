module

public import UnitDistance.ImprimitiveEulerProduct
public import UnitDistance.DyadicPrimeSet
public import UnitDistance.QuadraticUnramifiedEuler
public import UnitDistance.HeckeQuadraticContinuation

@[expose] public section
set_option backward.privateInPublic true


/-! Actual relative entire continuation for the imaginary quadratic extension
of a number field containing sqrt(7), with finite unramifiedness. -/
noncomputable section
namespace UnitDistance.NumberFieldAnalysis
open NumberField NumberField.InfinitePlace IsDedekindDomain
open UnitDistance.HeckeAnalysis UnitDistance.OddNormDyadic
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]

theorem nonsquare_neg_one_of_nrRealPlaces_pos (hFreal : 0 < nrRealPlaces F) :
    KummerInvariant.Nonsquare (-1:F) := by
  haveI : Nonempty {w : InfinitePlace F // IsReal w} := Fintype.card_pos_iff.mp hFreal
  let w := Classical.choice (inferInstance : Nonempty {w : InfinitePlace F // IsReal w})
  let ψ := embedding_of_isReal w.prop
  intro x hx
  have hh := congrArg ψ hx
  simp only [map_pow,map_neg,map_one] at hh
  nlinarith [sq_nonneg (ψ x)]

variable [Algebra F K]

/-- The actual raw zeta identity with only the actual dyadic Euler factors removed. -/
theorem imaginaryQuadratic_zeta_identity [Fact (KummerInvariant.Nonsquare (-1:F))]
    (i : K) (hi : i^2=(-1:K)) (hquad : Module.finrank F K=2) (hunr : FiniteUnramified F K)
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s * finiteEulerDenominator (dyadicPrimes F)
      (fun p => (Ideal.absNorm p.asIdeal:ℝ)) (quadraticPrimeSign F K) s =
      dedekindZeta F s * chiFourIdealSeries F s := by
  apply dedekindZeta_mul_finiteEuler_of_factors F K (dyadicPrimes F) (quadraticPrimeSign F K)
    (fun p _ => norm_quadraticPrimeSign F K p)
    (fun p hp => chiFourComplex_eq_zero_of_mem_dyadicPrimes F p hp) hs
  intro p
  by_cases hp : p ∈ dyadicPrimes F
  · rw [if_pos hp]
    exact quadratic_unramified_primeFiber_factor_product F K hquad hunr p s
  · rw [if_neg hp]
    exact oddPrimeFiber_factor_product F K i hi hquad p
      (fun h => hp ((mem_dyadicPrimes F p).mpr h)) s

/-- Actual entire relative factor, derived from the signed theta construction,
actual prime factorization and finite-Euler reflection. No analytic continuation,
zero distribution, growth, or ideal Euler identity is assumed. -/
theorem exists_entire_relative_factor_of_imaginary_quadratic [IsTotallyComplex K]
    (r : F) (hr : r^2=7) (hFreal : 0 < nrRealPlaces F)
    (i : K) (hi : i^2=(-1:K)) (hquad : Module.finrank F K=2) (hunr : FiniteUnramified F K) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ s, DedekindResidue.completedDedekindZetaEntire K s =
        DedekindResidue.completedDedekindZetaEntire F s*L s := by
  letI : Fact (KummerInvariant.Nonsquare (-1:F)) :=
    ⟨nonsquare_neg_one_of_nrRealPlaces_pos F hFreal⟩
  exact exists_entire_relative_factor_of_unramified_signed_zetaIdentity F K r hr hFreal hquad hunr
    (dyadicPrimes F) (fun p => (Ideal.absNorm p.asIdeal:ℝ)) (quadraticPrimeSign F K)
    (fun p _ => by exact_mod_cast primeIdeal_absNorm_gt_one F p)
    (fun p _ => norm_quadraticPrimeSign F K p)
    (fun x hx => imaginaryQuadratic_zeta_identity F K i hi hquad hunr hx)

end UnitDistance.NumberFieldAnalysis
