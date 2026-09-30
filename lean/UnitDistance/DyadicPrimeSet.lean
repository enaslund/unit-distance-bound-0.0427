module

public import UnitDistance.OddNormDyadicIdeals
public import UnitDistance.HeckeNormCharacter

@[expose] public section
set_option backward.privateInPublic true


/-! The finite set of actual height-one primes above two. -/
noncomputable section
namespace UnitDistance.OddNormDyadic
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical BigOperators nonZeroDivisors
variable (F : Type*) [Field F] [NumberField F]

def dyadicHeightPrime (P : DyadicPrime F) : HeightOneSpectrum (𝓞 F) :=
  ⟨P.val, Ideal.isPrime_of_prime (dyadicPrime_prime F P), (dyadicPrime_prime F P).ne_zero⟩

theorem dyadicHeightPrime_injective : Function.Injective (dyadicHeightPrime F) := by
  intro P Q h
  exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)

def dyadicPrimes : Finset (HeightOneSpectrum (𝓞 F)) :=
  Finset.univ.image (dyadicHeightPrime F)

@[simp] theorem mem_dyadicPrimes (p : HeightOneSpectrum (𝓞 F)) :
    p ∈ dyadicPrimes F ↔ (2:𝓞 F) ∈ p.asIdeal := by
  constructor
  · intro h
    obtain ⟨P,_,rfl⟩ := Finset.mem_image.mp h
    exact dyadicPrime_contains_two F P
  · intro h
    have hm : p.asIdeal ∈ normalizedFactors (Ideal.span {(2:𝓞 F)}) :=
      (Ideal.mem_normalizedFactors_iff (twoIdeal_ne_zero F)).mpr
        ⟨p.isPrime,(Ideal.span_singleton_le_iff_mem _).mpr h⟩
    let P : DyadicPrime F := ⟨p.asIdeal,Multiset.mem_toFinset.mpr hm⟩
    exact Finset.mem_image.mpr ⟨P,Finset.mem_univ _,HeightOneSpectrum.ext rfl⟩

theorem even_absNorm_of_mem_dyadicPrimes (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∈ dyadicPrimes F) : Even (Ideal.absNorm p.asIdeal) := by
  apply Nat.not_odd_iff_even.mp
  intro hodd
  let I : (Ideal (𝓞 F))⁰ := ⟨p.asIdeal,mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩
  have hc := Ideal.isCoprime_iff_sup_eq.mp ((odd_absNorm_iff_coprime_two F I).mp hodd)
  have hle : Ideal.span {(2:𝓞 F)} ≤ p.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr ((mem_dyadicPrimes F p).mp hp)
  exact p.isPrime.ne_top (by simpa only [I, sup_eq_left.mpr hle] using hc)

theorem chiFourComplex_eq_zero_of_mem_dyadicPrimes (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∈ dyadicPrimes F) : NumberFieldAnalysis.chiFourComplex (Ideal.absNorm p.asIdeal) = 0 := by
  rw [NumberFieldAnalysis.chiFourComplex_eq_ofReal,
    NumberFieldAnalysis.chiFourReal_zero_of_even (even_absNorm_of_mem_dyadicPrimes F p hp),
    Complex.ofReal_zero]

end UnitDistance.OddNormDyadic
