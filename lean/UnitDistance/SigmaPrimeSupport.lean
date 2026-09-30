module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! The manuscript's six finite rational primes as actual height-one primes
of the ring of integers of Q. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
namespace UnitDistance.ArithmeticProP

/-- The finite rational primes allowed to ramify in the target ambient extension. -/
def sigmaRationalPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13}

/-- The corresponding actual finite places of Q. -/
def sigmaPrimeSupport : Set (HeightOneSpectrum (𝓞 ℚ)) :=
  {v | (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ∈ sigmaRationalPrimes}

theorem prime_dvd_sigma_product_iff {p : ℕ} (hp : p.Prime) :
    p ∣ 30030 ↔ p ∈ sigmaRationalPrimes := by
  have he : (30030:ℕ) = 2*3*5*7*11*13 := by norm_num
  rw [he]
  simp only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13),
    sigmaRationalPrimes, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The six-prime support is exactly the primes containing the integer30030. -/
theorem mem_sigmaPrimeSupport_iff (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ sigmaPrimeSupport ↔ (30030:𝓞 ℚ) ∈ v.asIdeal := by
  change Rat.HeightOneSpectrum.natGenerator v ∈ sigmaRationalPrimes ↔ _
  rw [← prime_dvd_sigma_product_iff (Rat.HeightOneSpectrum.prime_natGenerator v),
    Rat.HeightOneSpectrum.natGenerator_dvd_iff]
  simpa only [map_ofNat, Nat.cast_ofNat] using
    (Ideal.apply_mem_of_equiv_iff (I := v.asIdeal)
      (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) (x := (30030:𝓞 ℚ)))

end UnitDistance.ArithmeticProP
