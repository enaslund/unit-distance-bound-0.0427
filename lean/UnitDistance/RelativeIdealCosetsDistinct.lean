module

public import UnitDistance.RelativeIdealCosetsFamily

@[expose] public section
set_option backward.privateInPublic true


/-! # Distinct multi-indices give distinct actual balanced integral ideals -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace UnitDistance.RelativeIdealCosets

private theorem factorization_finset_prod {A T : Type*} [CommMonoidWithZero A] [Nontrivial A]
    [UniqueFactorizationMonoid A] [NormalizationMonoid A] [DecidableEq A]
    (s : Finset T) (f : T → A) (h : ∀ t ∈ s, f t ≠ 0) :
    factorization (∏ t ∈ s, f t) = ∑ t ∈ s, factorization (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert t s ht ih =>
    rw [Finset.prod_insert ht, Finset.sum_insert ht,
      factorization_mul (h t (Finset.mem_insert_self t s))
        (Finset.prod_ne_zero_iff.mpr fun a ha ↦ h a (Finset.mem_insert_of_mem ha)),
      ih (fun a ha ↦ h a (Finset.mem_insert_of_mem ha))]

private theorem primeIdeal_factorization {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 K)) :
    factorization P.asIdeal Q = if Q = P.asIdeal then 1 else 0 := by
  rw [factorization_eq_count, normalizedFactors_irreducible P.irreducible,
    normalize_eq]
  exact Multiset.count_singleton _ _

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
  {S : Type*} [Fintype S]

/-- The valuation of the actual balanced ideal at its chosen first prime is
exactly the corresponding chosen exponent. -/
theorem balancedIdeal_first_factorization {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (k : S → ℕ) (j : ChoiceIndex k) (s : S) :
    factorization (balancedIdeal D k j) (D.prime (s, false)).asIdeal = (j s).val := by
  have he (t : S) : (D.prime (s, false)).asIdeal = (D.prime (t, false)).asIdeal ↔ t = s := by
    constructor
    · intro h
      exact (congrArg Prod.fst (D.distinct h)).symm
    · rintro rfl
      rfl
  have hn (t : S) : (D.prime (s, false)).asIdeal ≠ (D.prime (t, true)).asIdeal := by
    intro h
    have hb := congrArg Prod.snd (D.distinct h)
    cases hb
  unfold balancedIdeal
  rw [factorization_finset_prod _ _ (fun t _ ↦
    mul_ne_zero (pow_ne_zero _ (D.prime (t, false)).ne_bot)
      (pow_ne_zero _ (D.prime (t, true)).ne_bot))]
  simp only [Finsupp.sum_apply, factorization_mul
      (pow_ne_zero _ (D.prime (_, false)).ne_bot) (pow_ne_zero _ (D.prime (_, true)).ne_bot),
    Finsupp.add_apply, factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    primeIdeal_factorization, he, hn, if_false, mul_zero, add_zero]
  simp [primeIdeal_factorization, he, hn]

/-- Unique prime factorization proves that every actual balanced ideal is
different, independently of the subsequent choice of a class fiber. -/
theorem balancedIdeal_injective {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ) :
    Function.Injective (balancedIdeal D k) := by
  intro j l h
  funext s
  apply Fin.ext
  have hh := congrArg (fun I ↦ factorization I (D.prime (s, false)).asIdeal) h
  simpa only [balancedIdeal_first_factorization] using hh

end UnitDistance.RelativeIdealCosets
