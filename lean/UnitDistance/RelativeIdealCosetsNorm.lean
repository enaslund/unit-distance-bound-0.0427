module

public import UnitDistance.RelativeIdealCosets
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

@[expose] public section
set_option backward.privateInPublic true


/-! # Exact ideal norms for actual split-prime reference ideals -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain

namespace UnitDistance.RelativeIdealCosets

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- The actual extension and factorization of each chosen base prime are
visible data. The norm equality is proved from this factorization. -/
structure SplitPrimeFamily (ι : K ≃ₐ[F] K) (S : Type*) extends PrimePairFamily ι S where
  basePrime : S → HeightOneSpectrum (𝓞 F)
  split : ∀ s, Ideal.map (algebraMap (𝓞 F) (𝓞 K)) (basePrime s).asIdeal =
    (prime (s, false)).asIdeal * (prime (s, true)).asIdeal

/-- Extending an actual ideal through the quadratic extension squares its
absolute norm. -/
theorem absNorm_extendedIdeal (A : Ideal (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 K)) A) = Ideal.absNorm A ^ 2 := by
  rw [Ideal.absNorm_algebraMap,
    ← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K,
    Algebra.IsQuadraticExtension.finrank_eq_two F K]

variable {S : Type*} [Fintype S]

/-- Each of the two actual split primes has the norm of the actual base prime. -/
theorem splitPrime_absNorm {ι : K ≃ₐ[F] K} (D : SplitPrimeFamily ι S) (s : S) :
    Ideal.absNorm (D.prime (s, false)).asIdeal = Ideal.absNorm (D.basePrime s).asIdeal := by
  have h := congrArg Ideal.absNorm (D.split s)
  rw [absNorm_extendedIdeal, map_mul, D.partner, conjugateIdeal_absNorm] at h
  nlinarith

theorem splitPartner_absNorm {ι : K ≃ₐ[F] K} (D : SplitPrimeFamily ι S) (s : S) :
    Ideal.absNorm (D.prime (s, true)).asIdeal = Ideal.absNorm (D.basePrime s).asIdeal := by
  rw [D.partner, conjugateIdeal_absNorm, splitPrime_absNorm]

/-- Every balanced ideal has the same exact norm, the product of the base
prime norms to the full prescribed exponents. -/
theorem balancedIdeal_absNorm {ι : K ≃ₐ[F] K} (D : SplitPrimeFamily ι S)
    (k : S → ℕ) (j : ChoiceIndex k) :
    Ideal.absNorm (balancedIdeal D.toPrimePairFamily k j) =
      ∏ s, Ideal.absNorm (D.basePrime s).asIdeal ^ k s := by
  simp only [balancedIdeal, map_prod, map_mul, map_pow, splitPrime_absNorm,
    splitPartner_absNorm]
  apply Finset.prod_congr rfl
  intro s _
  rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (j s).isLt)]

/-- The actual inverse reference ideal has the manuscript's exact rational
norm product. -/
theorem referenceInverseIdeal_absNorm {ι : K ≃ₐ[F] K} (D : SplitPrimeFamily ι S)
    (k : S → ℕ) (j₀ : ChoiceIndex k) :
    FractionalIdeal.absNorm (referenceInverseIdeal D.toPrimePairFamily k j₀) =
      (∏ s, (Ideal.absNorm (D.basePrime s).asIdeal : ℚ) ^ k s)⁻¹ := by
  rw [referenceInverseIdeal, map_inv₀, FractionalIdeal.coeIdeal_absNorm, balancedIdeal_absNorm]
  simp only [Nat.cast_prod, Nat.cast_pow]

end UnitDistance.RelativeIdealCosets
