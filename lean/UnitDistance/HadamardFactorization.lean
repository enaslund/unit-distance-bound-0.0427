module

public import UnitDistance.EntireQuotientFactorization
public import UnitDistance.HadamardPairing
public import UnitDistance.Upstream.Hadamard.HadamardProduct.CanonicalProductDivisor
public import UnitDistance.Upstream.Hadamard.HadamardProduct.CanonicalProductGrowth

@[expose] public section
set_option backward.privateInPublic true


/-! Canonical genus-one factorization from actual divisor and growth data. -/
noncomputable section
open Filter Set
namespace UnitDistance.HeckeAnalysis
open OverflowResidueRH

def canonicalEntireProduct {ι : Type*} (zeros : ι → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  z^m*infiniteHadamardProduct zeros z

theorem canonicalEntireProduct_differentiable {ι : Type*} {zeros : ι → ℂ}
    (hinv : HadamardZeroInvSqSummability zeros) (hproper : HadamardZeroNormProper zeros) (m : ℕ) :
    Differentiable ℂ (canonicalEntireProduct zeros m) := by
  exact (differentiable_id.pow m).mul
    (infiniteHadamardProduct_differentiable_of_invSq_normProper hinv hproper)

theorem canonicalEntireProduct_analyticOrderAt {ι : Type*} {zeros : ι → ℂ}
    (hinv : HadamardZeroInvSqSummability zeros) (hproper : HadamardZeroNormProper zeros)
    (m : ℕ) (z : ℂ) :
    analyticOrderAt (canonicalEntireProduct zeros m) z =
      (if z = 0 then (m : ENat) else 0)+(Nat.card {i : ι // zeros i = z} : ENat) := by
  have hp := infiniteHadamardProduct_differentiable_of_invSq_normProper hinv hproper
  rw [show canonicalEntireProduct zeros m =
      (fun z : ℂ => z^m)*infiniteHadamardProduct zeros from rfl,
    analyticOrderAt_mul (by fun_prop) (hp.analyticAt z),
    infiniteHadamardProduct_analyticOrderAt_eq_fiber_natCard hinv hproper z]
  congr 1
  by_cases hz : z = 0
  · subst z
    simp only [if_pos rfl]
    rw [show (fun z : ℂ => z^m) = (id : ℂ → ℂ)^m from rfl,
      analyticOrderAt_pow (by fun_prop)]
    simp
  · rw [if_neg hz]
    exact (show AnalyticAt ℂ (fun z : ℂ => z^m) z by fun_prop).analyticOrderAt_eq_zero.mpr
      (pow_ne_zero m hz)

theorem canonicalEntireProduct_growth {ι : Type*} {zeros : ι → ℂ}
    (hinv : HadamardZeroInvSqSummability zeros) (m : ℕ) :
    HasSubquadraticLogNormGrowthAtInfinity (canonicalEntireProduct zeros m) :=
  (monomial_hasSubquadraticLogNormGrowthAtInfinity m).mul
    (infiniteHadamardProduct_hasSubquadraticLogNormGrowthAtInfinity hinv)

theorem exists_exp_affine_canonical_product {F : ℂ → ℂ} {ι : Type*} {zeros : ι → ℂ}
    (hF : Differentiable ℂ F) (hinv : HadamardZeroInvSqSummability zeros)
    (hproper : HadamardZeroNormProper zeros) (m : ℕ)
    (hdivisor : ∀ z : ℂ, analyticOrderAt F z =
      (if z = 0 then (m : ENat) else 0)+(Nat.card {i : ι // zeros i = z} : ENat))
    (hgrowth : HasSubquadraticLogNormGrowthAtInfinity F) :
    ∃ a b : ℂ, ∀ z : ℂ, F z = Complex.exp (a+b*z)*canonicalEntireProduct zeros m z := by
  apply exists_exp_affine_mul_of_same_divisor hF
    (canonicalEntireProduct_differentiable hinv hproper m)
  · intro z
    rw [hdivisor, canonicalEntireProduct_analyticOrderAt hinv hproper]
  · intro z
    rw [hdivisor]
    split_ifs <;> simp
  · exact hgrowth
  · exact canonicalEntireProduct_growth hinv m

end UnitDistance.HeckeAnalysis
