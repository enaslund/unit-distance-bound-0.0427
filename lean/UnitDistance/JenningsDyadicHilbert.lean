module

public import UnitDistance.GroupAugmentationHilbert
public import UnitDistance.JenningsDyadicInduction

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual dyadic Hilbert shift quotient

The independently defined ambient augmentation Hilbert polynomial factors
by the independently certified local polynomial. Consequently the actual
complementary shift polynomial is their quotient at every nonnegative real
parameter. No global group or retained field is supplied by this identity.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace UnitDistance.GroupAugmentation
open Dyadic

theorem finrank_dyadic_power (n : ℕ) :
    Module.finrank F (power F D n) = Module.finrank F (AlgebraD.augmentationPower n) :=
  congrArg (fun S : Submodule F AlgebraD => Module.finrank F S) (dyadic_power n)

/-- The general quotient-dimension definition agrees with the original
certified dyadic polynomial, despite its larger nilpotence cutoff. -/
theorem dyadic_hilbertPolynomial : hilbertPolynomial D = AlgebraD.hilbertPolynomial := by
  rw [hilbertPolynomial,Nat.card_eq_fintype_card,D.card]
  simp only [finrank_powerLayer,finrank_dyadic_power,AlgebraD.hilbertPolynomial]
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_range] at hn ⊢
    omega
  · intro n _ hn
    have hn8 : 8 ≤ n := by simpa only [Finset.mem_range,not_lt] using hn
    rw [AlgebraD.augmentation_nilpotent n hn8,
      AlgebraD.augmentation_nilpotent (n+1) (by omega),finrank_bot]
    simp

theorem dyadic_hilbertPolynomial_eq :
    hilbertPolynomial D = (1+X)^3*(1+X^2)^2 := by
  rw [dyadic_hilbertPolynomial,AlgebraD.hilbert_polynomial]

variable (P : Type*) [Group P] [Finite P] (hP : IsPGroup 2 P)
variable (f : D →* P)
variable (hfirst : Function.Injective (layerMap F D f 1))
variable (hsecond : Function.Injective (layerMap F D f 2))

/-- The actual complementary shift polynomial gives the certified dyadic
factor of the actual ambient Hilbert polynomial. -/
theorem dyadic_hilbertPolynomial_induction :
    hilbertPolynomial P =
      shiftPolynomial D P f (dyadic_layer_injections P f hfirst hsecond) hP *
        ((1+X)^3*(1+X^2)^2) := by
  rw [← dyadic_hilbertPolynomial_eq]
  exact hilbertPolynomial_induction D P f (dyadic_layer_injections P f hfirst hsecond)
    dyadic_isTwoGroup hP

/-- The shift quotient uses the actual ambient Hilbert polynomial and the
actual local polynomial; its denominator is positive on the relevant range. -/
theorem dyadic_shiftPolynomial_eval (t : ℝ) (ht : 0 ≤ t) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) t
      (shiftPolynomial D P f (dyadic_layer_injections P f hfirst hsecond) hP) =
      Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial P) /
        ((1+t)^3*(1+t^2)^2) := by
  have he := congrArg (Polynomial.eval₂ (Nat.castRingHom ℝ) t)
    (dyadic_hilbertPolynomial_induction P hP f hfirst hsecond)
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_add,
    Polynomial.eval₂_one,Polynomial.eval₂_X] at he
  apply (eq_div_iff (by positivity : (1+t)^3*(1+t^2)^2 ≠ 0)).mpr
  exact he.symm

end UnitDistance.GroupAugmentation
