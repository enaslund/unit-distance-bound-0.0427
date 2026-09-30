module

public import UnitDistance.RelativeIdealCosetsSIntegers
public import UnitDistance.LocalAdicResidue
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual denominators supported on a finite set of number-field primes

Finite class number proves that a power of any actual nonzero ideal is
principal. Applied to the selected-prime product, this gives a denominator
with no prime factors outside the selected set. No principality assumption
is imposed on the selected primes or on the period ideal.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain

namespace UnitDistance.SIntegerCRT

open RelativeIdealCosets

variable {K : Type} [Field K] [NumberField K]

/-- The actual class number annihilates every ordinary ideal class, so the
corresponding power of an actual nonzero integral ideal is principal. -/
theorem classNumber_power_isPrincipal (I : NonzeroIdeal K) :
    (I.val ^ classNumber K).IsPrincipal := by
  have h : ClassGroup.mk0 (I ^ classNumber K) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one
  exact (ClassGroup.mk0_eq_one_iff (I ^ classNumber K).prop).mp h

theorem exists_classNumber_power_generator (I : NonzeroIdeal K) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ Ideal.span {a} = I.val ^ classNumber K := by
  have hi := classNumber_power_isPrincipal I
  rw [Submodule.isPrincipal_iff] at hi
  obtain ⟨a, ha⟩ := hi
  refine ⟨a, ?_, ha.symm⟩
  intro h
  have hi : I.val ^ classNumber K ≠ 0 :=
    pow_ne_zero _ (mem_nonZeroDivisors_iff_ne_zero.mp I.prop)
  apply hi
  simpa [h] using ha

variable {T : Type*} [Fintype T]

/-- The ordinary product ideal of the actual selected primes. -/
def supportIdeal (P : T → HeightOneSpectrum (𝓞 K)) : NonzeroIdeal K :=
  ⟨∏ t, (P t).asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun t _ ↦ (P t).ne_bot)⟩

/-- An actual algebraic integer whose principal ideal is the class-number
power of the selected-prime product. -/
def supportDenominator (P : T → HeightOneSpectrum (𝓞 K)) : 𝓞 K :=
  (exists_classNumber_power_generator (supportIdeal P)).choose

theorem supportDenominator_ne_zero (P : T → HeightOneSpectrum (𝓞 K)) :
    supportDenominator P ≠ 0 :=
  (exists_classNumber_power_generator (supportIdeal P)).choose_spec.1

theorem supportDenominator_span (P : T → HeightOneSpectrum (𝓞 K)) :
    Ideal.span {supportDenominator P} = (∏ t, (P t).asIdeal) ^ classNumber K :=
  (exists_classNumber_power_generator (supportIdeal P)).choose_spec.2

/-- The actual principal ideal of this denominator has the asserted global
prime support, also as a fractional ideal in the specified number field. -/
theorem supportDenominator_principal (P : T → HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (supportDenominator P : K) =
      (∏ t, ((P t).asIdeal : FractionalIdeal (𝓞 K)⁰ K)) ^ classNumber K := by
  rw [← FractionalIdeal.coeIdeal_span_singleton, supportDenominator_span,
    FractionalIdeal.coeIdeal_pow]
  congr 1
  exact map_prod (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) (fun t ↦ (P t).asIdeal) Finset.univ

theorem supportDenominator_count (P : T → HeightOneSpectrum (𝓞 K))
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (supportDenominator P : K)) =
      (classNumber K : ℤ) * ∑ t, if P t = v then 1 else 0 := by
  rw [supportDenominator_principal, FractionalIdeal.count_pow,
    FractionalIdeal.count_prod _ _ _ _ (fun t _ ↦
      FractionalIdeal.coeIdeal_ne_zero.mpr (P t).ne_bot)]
  simp only [FractionalIdeal.count_maximal]

/-- The denominator has strictly positive multiplicity at every selected
prime, with the exact class-number value for a list without repetitions. -/
theorem supportDenominator_valuation_selected (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (t : T) :
    (P t).valuation K (supportDenominator P : K) = WithZero.exp (-(classNumber K : ℤ)) := by
  have h := valuation_eq_exp_neg_principal_count (P t)
    (integerFieldUnit (supportDenominator P) (supportDenominator_ne_zero P))
  simp only [integerFieldUnit_coe, supportDenominator_count, hP.eq_iff] at h
  simpa using h

/-- Outside the selected primes this denominator is a local unit. -/
theorem supportDenominator_valuation_outside (P : T → HeightOneSpectrum (𝓞 K))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Set.range P) :
    v.valuation K (supportDenominator P : K) = 1 := by
  have hn (t : T) : P t ≠ v := fun h ↦ hv ⟨t, h⟩
  apply valuation_eq_one_of_principal_count_zero v
    (integerFieldUnit (supportDenominator P) (supportDenominator_ne_zero P))
  simp only [integerFieldUnit_coe, supportDenominator_count, hn, if_false,
    Finset.sum_const_zero, mul_zero]

end UnitDistance.SIntegerCRT
