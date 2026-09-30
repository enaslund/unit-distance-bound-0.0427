module

public import UnitDistance.ArithmeticCatalogOddRamification
public import UnitDistance.CanonicalRetainedEquiv
public import Mathlib.Data.Nat.Factors

@[expose] public section
set_option backward.privateInPublic true


/-!
# Discriminant reduction for the actual retained field

The proved relative unramifiedness at every odd prime forces the norm of the
relative different of the twelve-radical extension to be a power of two.
Consequently, the absolute discriminant of the actual retained field is its
genus-field discriminant to the relative degree, times one dyadic factor.

This does not compute the remaining dyadic exponent or the genus-field
discriminant.  It isolates those two computations without introducing a
numerical discriminant assumption.
-/

noncomputable section
open NumberField

namespace UnitDistance
open QuadraticRamification

namespace QuadraticRamification

variable (F K : Type*) [Field F] [NumberField F]
  [Field K] [NumberField K] [Algebra F K]

/-- If `K/F` is unramified at every prime away from two, no odd rational
prime divides the norm of its relative different. -/
theorem UnramifiedAtOddPrimes.not_dvd_absNorm_differentIdeal
    (h : UnramifiedAtOddPrimes F K) {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ¬ p ∣ Ideal.absNorm (differentIdeal (RingOfIntegers F) (RingOfIntegers K)) := by
  intro hdiv
  obtain ⟨P, hP, hunder, hPdiff⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp
      (differentIdeal (RingOfIntegers F) (RingOfIntegers K)) hdiv
  letI : P.IsPrime := hP.isPrime
  have htwo : (2 : RingOfIntegers K) ∉ P := by
    intro htwoP
    have htwoUnder : (2 : ℤ) ∈ P.under ℤ := by
      change algebraMap ℤ (RingOfIntegers K) (2 : ℤ) ∈ P
      simpa only [map_ofNat] using htwoP
    rw [hunder] at htwoUnder
    have hpdvd : p ∣ 2 := by
      exact_mod_cast Ideal.mem_span_singleton.mp htwoUnder
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdvd with hpone | hptwo
    · exact hp.ne_one hpone
    · subst p
      norm_num at hodd
  exact (not_dvd_differentIdeal_iff.mpr (h P htwo)) hPdiff

/-- The relative different norm of an extension unramified away from two is
an actual power of two. -/
theorem UnramifiedAtOddPrimes.absNorm_differentIdeal_eq_two_pow
    (h : UnramifiedAtOddPrimes F K) :
    ∃ k : ℕ, Ideal.absNorm
      (differentIdeal (RingOfIntegers F) (RingOfIntegers K)) = 2 ^ k := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd
      (Ideal.absNorm (differentIdeal (RingOfIntegers F) (RingOfIntegers K))) with
      hpow | ⟨p, hp, hdiv, hodd⟩
  · exact hpow
  · exact (h.not_dvd_absNorm_differentIdeal F K hp hodd hdiv).elim

end QuadraticRamification

namespace ArithmeticRetained

open ArithmeticChosenGenus

/-- The absolute discriminant tower formula for the actual twelve-radical
retained extension, with its proved relative degree substituted. -/
theorem retainedField_natAbs_discr_eq_relativeDifferent :
    (discr RetainedField).natAbs =
      Ideal.absNorm (differentIdeal (RingOfIntegers GenusField)
        (RingOfIntegers RetainedField)) *
        (discr GenusField).natAbs ^ 4096 := by
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    GenusField (RingOfIntegers GenusField) RetainedField
      (RingOfIntegers RetainedField),
    retainedField_relative_degree]

/-- All relative discriminant growth from the actual genus field to the
actual retained field is dyadic. -/
theorem exists_retainedField_natAbs_discr_eq_two_pow_mul :
    ∃ k : ℕ, (discr RetainedField).natAbs =
      2 ^ k * (discr GenusField).natAbs ^ 4096 := by
  obtain ⟨k, hk⟩ :=
    retainedField_unramifiedAtOddPrimes.absNorm_differentIdeal_eq_two_pow
      GenusField RetainedField
  refine ⟨k, ?_⟩
  rw [retainedField_natAbs_discr_eq_relativeDifferent, hk]

/-- At every odd rational prime, the retained-field discriminant valuation is
exactly the genus-field valuation multiplied by the relative degree.  Thus no
odd discriminant exponent remains to be computed in the twelve-radical step. -/
theorem retainedField_factorization_eq_genus_of_odd
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    (discr RetainedField).natAbs.factorization p =
      4096 * (discr GenusField).natAbs.factorization p := by
  obtain ⟨k, hk⟩ := exists_retainedField_natAbs_discr_eq_two_pow_mul
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    norm_num at hodd
  rw [hk, Nat.factorization_mul (pow_ne_zero _ (by decide))
    (pow_ne_zero _ (Int.natAbs_ne_zero.mpr (discr_ne_zero GenusField)))]
  simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_pow, hp2]

/-- The two remaining exact arithmetic computations, stated at their natural
levels, imply the target absolute discriminant of the retained field.  The
first premise is the seven-radical genus discriminant; the second is the
dyadic relative-different norm. -/
theorem retainedField_natAbs_discr_eq_target
    (hgenus : (discr GenusField).natAbs = 2 ^ 256 * 15015 ^ 64)
    (hdyadic : Ideal.absNorm (differentIdeal (RingOfIntegers GenusField)
      (RingOfIntegers RetainedField)) = 2 ^ 131072) :
    (discr RetainedField).natAbs = 2 ^ 1179648 * 15015 ^ 262144 := by
  rw [retainedField_natAbs_discr_eq_relativeDifferent, hdyadic, hgenus, mul_pow,
    ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]

/-- Upper bounds for the genus discriminant and dyadic relative different are
already sufficient for the retained-field discriminant bound used by `hdisc`. -/
theorem retainedField_natAbs_discr_le_target
    (hgenus : (discr GenusField).natAbs ≤ 2 ^ 256 * 15015 ^ 64)
    (hdyadic : Ideal.absNorm (differentIdeal (RingOfIntegers GenusField)
      (RingOfIntegers RetainedField)) ≤ 2 ^ 131072) :
    (discr RetainedField).natAbs ≤ 2 ^ 1179648 * 15015 ^ 262144 := by
  rw [retainedField_natAbs_discr_eq_relativeDifferent]
  calc
    _ ≤ 2 ^ 131072 * (2 ^ 256 * 15015 ^ 64) ^ 4096 :=
      Nat.mul_le_mul hdyadic (Nat.pow_le_pow_left hgenus _)
    _ = _ := by
      rw [mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]

end ArithmeticRetained

namespace CanonicalRetained

/-- The independent nineteen-radical field has the same dyadically reduced
absolute-discriminant factorization as the actual retained field. -/
theorem exists_natAbs_discr_eq_two_pow_mul_genus :
    ∃ k : ℕ, (discr Carrier).natAbs =
      2 ^ k * (discr ArithmeticChosenGenus.GenusField).natAbs ^ 4096 := by
  obtain ⟨k, hk⟩ :=
    ArithmeticRetained.exists_retainedField_natAbs_discr_eq_two_pow_mul
  refine ⟨k, ?_⟩
  rw [NumberField.discr_eq_discr_of_algEquiv Carrier equiv]
  exact hk

/-- The odd prime valuations of the canonical nineteen-radical field
discriminant are already reduced exactly to those of the genus field. -/
theorem factorization_eq_genus_of_odd {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    (discr Carrier).natAbs.factorization p =
      4096 * (discr ArithmeticChosenGenus.GenusField).natAbs.factorization p := by
  rw [NumberField.discr_eq_discr_of_algEquiv Carrier equiv]
  exact ArithmeticRetained.retainedField_factorization_eq_genus_of_odd hp hodd

/-- Exact genus and dyadic relative-different computations feed the canonical
nineteen-radical field discriminant expected by the final numerical bridge. -/
theorem natAbs_discr_eq_target
    (hgenus : (discr ArithmeticChosenGenus.GenusField).natAbs =
      2 ^ 256 * 15015 ^ 64)
    (hdyadic : Ideal.absNorm
      (differentIdeal (RingOfIntegers ArithmeticChosenGenus.GenusField)
        (RingOfIntegers ArithmeticRetained.RetainedField)) = 2 ^ 131072) :
    (discr Carrier).natAbs = 2 ^ 1179648 * 15015 ^ 262144 := by
  rw [NumberField.discr_eq_discr_of_algEquiv Carrier equiv]
  exact ArithmeticRetained.retainedField_natAbs_discr_eq_target hgenus hdyadic

/-- The inequality form of the two residual arithmetic obligations, transported
to the independent canonical field. -/
theorem natAbs_discr_le_target
    (hgenus : (discr ArithmeticChosenGenus.GenusField).natAbs ≤
      2 ^ 256 * 15015 ^ 64)
    (hdyadic : Ideal.absNorm
      (differentIdeal (RingOfIntegers ArithmeticChosenGenus.GenusField)
        (RingOfIntegers ArithmeticRetained.RetainedField)) ≤ 2 ^ 131072) :
    (discr Carrier).natAbs ≤ 2 ^ 1179648 * 15015 ^ 262144 := by
  rw [NumberField.discr_eq_discr_of_algEquiv Carrier equiv]
  exact ArithmeticRetained.retainedField_natAbs_discr_le_target hgenus hdyadic

end CanonicalRetained
end UnitDistance
