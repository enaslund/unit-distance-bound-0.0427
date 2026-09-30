module

public import UnitDistance.RelativeIdealCosetsSigned

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual S-integrality of the signed-label principal generators -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain

namespace UnitDistance.RelativeIdealCosets

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
  {S : Type*} [Fintype S]

/-- The ordinary local valuation is exactly the exponential of the negative
multiplicity of the actual principal fractional ideal. -/
theorem valuation_eq_exp_neg_principal_count (P : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    P.valuation K (x : K) = WithZero.exp
      (-FractionalIdeal.count K P (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
  have hb₀ : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha₀ : a ≠ 0 := by
    intro h
    apply x.ne_zero
    rw [← hab, h, map_zero, zero_div]
  have hrepr : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b)⁻¹ *
        (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← hab, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined K P
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero) hrepr]
  rw [← hab, map_div₀, P.valuation_of_algebraMap, P.valuation_of_algebraMap,
    P.intValuation_if_neg ha₀, P.intValuation_if_neg hb₀, ← WithZero.exp_sub]
  congr 1
  ring

/-- Outside multiplicity zero is actual local valuation one. -/
theorem valuation_eq_one_of_principal_count_zero (P : HeightOneSpectrum (𝓞 K)) (x : Kˣ)
    (hc : FractionalIdeal.count K P (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0) :
    P.valuation K (x : K) = 1 := by
  rw [valuation_eq_exp_neg_principal_count, hc]
  simp

/-- The selected first local valuation of an actual signed-ideal generator. -/
theorem signedStep_generator_first_valuation {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (n : S → ℤ) (x : Kˣ) (hx : signedStepIdeal D n = toPrincipalIdeal (𝓞 K) K x) (s : S) :
    (D.prime (s, false)).valuation K (x : K) = WithZero.exp (-n s) := by
  rw [valuation_eq_exp_neg_principal_count]
  have hh := congrArg Units.val hx
  rw [coe_toPrincipalIdeal] at hh
  rw [← hh, signedStepIdeal_first_count]

/-- The selected conjugate local valuation is the reciprocal first valuation. -/
theorem signedStep_generator_second_valuation {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (n : S → ℤ) (x : Kˣ) (hx : signedStepIdeal D n = toPrincipalIdeal (𝓞 K) K x) (s : S) :
    (D.prime (s, true)).valuation K (x : K) = WithZero.exp (n s) := by
  rw [valuation_eq_exp_neg_principal_count]
  have hh := congrArg Units.val hx
  rw [coe_toPrincipalIdeal] at hh
  rw [← hh, signedStepIdeal_second_count, neg_neg]

/-- An actual generator of a signed step ideal is an actual S-unit at the
selected prime pairs, hence an element of Mathlib's ring of S-integers. -/
theorem signedStep_generator_mem_sIntegers {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (n : S → ℤ) (x : Kˣ)
    (hx : signedStepIdeal D n = toPrincipalIdeal (𝓞 K) K x) :
    (x : K) ∈ (Set.range D.prime).integer K := by
  intro P hP
  apply le_of_eq
  apply valuation_eq_one_of_principal_count_zero P x
  have hh := congrArg Units.val hx
  rw [coe_toPrincipalIdeal] at hh
  rw [← hh]
  exact signedStepIdeal_count_outside D n P hP

theorem signedStep_generator_mem_sUnits {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (n : S → ℤ) (x : Kˣ)
    (hx : signedStepIdeal D n = toPrincipalIdeal (𝓞 K) K x) :
    x ∈ (Set.range D.prime).unit K := by
  intro P hP
  apply valuation_eq_one_of_principal_count_zero P x
  have hh := congrArg Units.val hx
  rw [coe_toPrincipalIdeal] at hh
  rw [← hh]
  exact signedStepIdeal_count_outside D n P hP

end UnitDistance.RelativeIdealCosets
