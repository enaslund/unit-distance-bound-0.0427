module

public import UnitDistance.RelativeUnramifiedIndices
public import UnitDistance.GaloisPrimeNormCounts
public import UnitDistance.SigmaRamification
public import Mathlib.RingTheory.Ideal.Int

@[expose] public section
set_option backward.privateInPublic true


/-! Equality at the six allowed rational primes, together with actual
ramification support, proves unramifiedness over the retained base field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain
namespace UnitDistance.NumberFieldAnalysis
open QuadraticRamification ArithmeticProP
variable (M K : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
  [Field K] [NumberField K] [IsGalois ℚ K] [Algebra M K]

/-- Actual ramification is unchanged everywhere once it is unchanged at the
six permitted rational primes. -/
theorem finiteUnramified_of_sigma_ramificationIdxIn_eq
    (hM : UnramifiedAway M 30030) (hK : UnramifiedAway K 30030)
    (he : ∀ p∈sigmaRationalPrimes,
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K)=
        (rationalPrimeIdeal p).ramificationIdxIn (𝓞 M)) : FiniteUnramified M K := by
  apply finiteUnramified_of_absolute_ramificationIdx_eq M K
  intro P
  let V := P.under (𝓞 M)
  letI : P.asIdeal.IsPrime := P.isPrime
  letI : V.asIdeal.IsPrime := V.isPrime
  by_cases hN : (30030:𝓞 K)∈P.asIdeal
  · let p := (P.asIdeal.under ℤ).absNorm
    letI : NeZero P.asIdeal := ⟨P.ne_bot⟩
    have hp : p.Prime := Nat.absNorm_under_prime P.asIdeal
    have hspan : rationalPrimeIdeal p=P.asIdeal.under ℤ := Int.ideal_span_absNorm_eq_self _
    have hd : p∣30030 := by
      have hn : (30030:ℤ)∈P.asIdeal.under ℤ := by
        change algebraMap ℤ (𝓞 K) 30030∈P.asIdeal
        simpa only [map_ofNat] using hN
      rw [←hspan,Ideal.mem_span_singleton] at hn
      exact_mod_cast hn
    have hs : p∈sigmaRationalPrimes := (prime_dvd_sigma_product_iff hp).mp hd
    letI : Fact p.Prime := ⟨hp⟩
    letI : P.asIdeal.LiesOver (rationalPrimeIdeal p) := hspan ▸ inferInstance
    letI : P.asIdeal.LiesOver V.asIdeal := ⟨rfl⟩
    letI : V.asIdeal.LiesOver (rationalPrimeIdeal p) := by
      constructor
      change rationalPrimeIdeal p=(P.asIdeal.under (𝓞 M)).under ℤ
      rw [Ideal.under_under]
      exact hspan
    rw [←Ideal.ramificationIdxIn_eq_ramificationIdx (rationalPrimeIdeal p) P.asIdeal Gal(K/ℚ),
      ←Ideal.ramificationIdxIn_eq_ramificationIdx (rationalPrimeIdeal p) V.asIdeal Gal(M/ℚ)]
    exact he p hs
  · have hNM : (30030:𝓞 M)∉V.asIdeal := by
      intro h
      apply hN
      change algebraMap (𝓞 M) (𝓞 K) 30030∈P.asIdeal at h
      simpa only [map_ofNat] using h
    have hKone : P.asIdeal.ramificationIdx ℤ=1 :=
      Ideal.ramificationIdx_eq_one_iff.mpr (hK P.asIdeal (by simpa only [Int.cast_ofNat] using hN))
    have hMone : V.asIdeal.ramificationIdx ℤ=1 :=
      Ideal.ramificationIdx_eq_one_iff.mpr (hM V.asIdeal (by simpa only [Int.cast_ofNat] using hNM))
    exact hKone.trans hMone.symm

end UnitDistance.NumberFieldAnalysis
