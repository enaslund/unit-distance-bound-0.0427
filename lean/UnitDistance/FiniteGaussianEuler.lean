module

public import Mathlib.Data.Complex.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
namespace UnitDistance.FiniteGaussianEuler
open Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators
variable (k : Type*) [Field k] [Fintype k]

/-- The actual quadratic polynomial factor product over an odd residue field. -/
theorem factor_product (hchar : ringChar k ≠ 2) (z : ℂ) :
    (∏ g ∈ (normalizedFactors (X^2-C (-1:k))).toFinset,
      (1-z^g.natDegree)) =
      (1-z)*(1-(ZMod.χ₄ (Fintype.card k) : ℂ)*z) := by
  by_cases hs : IsSquare (-1:k)
  · obtain ⟨r,hr⟩ := hs
    have hr2 : r^2=(-1:k) := by simpa only [pow_two] using hr.symm
    have hr0 : r ≠ 0 := by intro h; simp [h] at hr2
    have hne : r ≠ -r := by
      intro h
      have htwo : (2:k)*r=0 := by linear_combination h
      exact (mul_ne_zero (Ring.two_ne_zero hchar) hr0) htwo
    have hp : (X^2-C (-1:k)) = (X-C r)*(X-C (-r)) := by
      calc
        _ = X^2-(C r)^2 := by rw [← map_pow, hr2]
        _ = _ := by rw [C_neg]; ring
    have hlin : (X-C r:k[X]) ≠ X-C (-r) := by
      intro he
      have hh := congrArg (fun p : k[X] => p.coeff 0) he
      simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_neg] at hh
      exact hne (neg_eq_iff_eq_neg.mp hh)
    have hχ : ZMod.χ₄ (Fintype.card k) = (1:ℤ) := by
      rw [← quadraticChar_neg_one hchar]
      exact (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr ⟨r,hr⟩
    rw [hp, normalizedFactors_mul (X_sub_C_ne_zero r) (X_sub_C_ne_zero (-r)),
      normalizedFactors_irreducible (irreducible_X_sub_C r),
      normalizedFactors_irreducible (irreducible_X_sub_C (-r))]
    rw [Polynomial.Monic.normalize_eq_self (monic_X_sub_C r),
      Polynomial.Monic.normalize_eq_self (monic_X_sub_C (-r))]
    simp only [Multiset.toFinset_add, Multiset.toFinset_singleton, Finset.singleton_union]
    rw [Finset.prod_pair hlin]
    simp only [natDegree_X_sub_C, pow_one, hχ, Int.cast_one, one_mul]
  · have hi : Irreducible (X^2-C (-1:k)) :=
      (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr (by
        intro r hr
        exact hs ⟨r,by simpa only [pow_two] using hr.symm⟩)
    have hχ : ZMod.χ₄ (Fintype.card k) = (-1:ℤ) := by
      rw [← quadraticChar_neg_one hchar]
      exact quadraticChar_neg_one_iff_not_isSquare.mpr hs
    rw [normalizedFactors_irreducible hi,
      Polynomial.Monic.normalize_eq_self (monic_X_pow_sub_C (-1:k) (by decide))]
    simp only [Multiset.toFinset_singleton, Finset.prod_singleton,
      natDegree_X_pow_sub_C, hχ, Int.cast_neg, Int.cast_one]
    ring

end UnitDistance.FiniteGaussianEuler
