module

public import UnitDistance.FullResultReduced

@[expose] public section
set_option backward.privateInPublic true


/-!
# The residual dyadic different exponent

For an extension unramified at every prime away from two, the norm of the
relative different is a power of two.  This file records the exponent
canonically as the factorization multiplicity at the rational prime two.
Consequently, a bound on that exponent is exactly equivalent to the norm
bound used by the retained-field discriminant bridge.

The actual retained dyadic modules determine its local degree, residue degree,
and inertia order.  Those invariants alone do not determine the different in
the wildly ramified case, so no numerical exponent is asserted here.
-/

noncomputable section
open NumberField

namespace UnitDistance
open QuadraticRamification

namespace QuadraticRamification

variable (F K : Type*) [Field F] [NumberField F]
  [Field K] [NumberField K] [Algebra F K]

/-- The rational `2`-adic exponent of the norm of the relative different. -/
def relativeDifferentTwoExponent : ℕ :=
  (Ideal.absNorm
    (differentIdeal (RingOfIntegers F) (RingOfIntegers K))).factorization 2

/-- Away-from-two unramifiedness identifies the relative different norm with
two raised to its canonical factorization exponent. -/
theorem UnramifiedAtOddPrimes.absNorm_differentIdeal_eq_two_pow_factorization
    (h : UnramifiedAtOddPrimes F K) :
    Ideal.absNorm (differentIdeal (RingOfIntegers F) (RingOfIntegers K)) =
      2 ^ relativeDifferentTwoExponent F K := by
  obtain ⟨k, hk⟩ := h.absNorm_differentIdeal_eq_two_pow F K
  unfold relativeDifferentTwoExponent
  rw [hk]
  simp [Nat.Prime.factorization_pow Nat.prime_two]

/-- Once odd ramification is eliminated, bounding the different norm is
equivalent to bounding its exponent at two. -/
theorem UnramifiedAtOddPrimes.absNorm_differentIdeal_le_two_pow_iff
    (h : UnramifiedAtOddPrimes F K) (N : ℕ) :
    Ideal.absNorm (differentIdeal (RingOfIntegers F) (RingOfIntegers K)) ≤ 2 ^ N ↔
      relativeDifferentTwoExponent F K ≤ N := by
  rw [h.absNorm_differentIdeal_eq_two_pow_factorization F K,
    Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)]

end QuadraticRamification

namespace ArithmeticRetained

open ArithmeticChosenGenus

/-- The sole remaining rational-prime exponent in the relative different of
the actual retained field over its genus field. -/
def retainedRelativeDifferentTwoExponent : ℕ :=
  relativeDifferentTwoExponent GenusField RetainedField

theorem retainedField_absNorm_differentIdeal_eq_two_pow_factorization :
    Ideal.absNorm (differentIdeal (RingOfIntegers GenusField)
      (RingOfIntegers RetainedField)) =
        2 ^ retainedRelativeDifferentTwoExponent := by
  simpa only [retainedRelativeDifferentTwoExponent] using
    retainedField_unramifiedAtOddPrimes.absNorm_differentIdeal_eq_two_pow_factorization
      GenusField RetainedField

theorem retainedField_absNorm_differentIdeal_le_two_pow_iff (N : ℕ) :
    Ideal.absNorm (differentIdeal (RingOfIntegers GenusField)
      (RingOfIntegers RetainedField)) ≤ 2 ^ N ↔
        retainedRelativeDifferentTwoExponent ≤ N := by
  simpa only [retainedRelativeDifferentTwoExponent] using
    retainedField_unramifiedAtOddPrimes.absNorm_differentIdeal_le_two_pow_iff
      GenusField RetainedField N

/-- The exact residual premise needed for the relative-different norm bound in
the reduced full result. -/
theorem retainedField_absNorm_differentIdeal_le_target_of_twoExponent
    (h : retainedRelativeDifferentTwoExponent ≤ 131072) :
    Ideal.absNorm (differentIdeal (RingOfIntegers GenusField)
      (RingOfIntegers RetainedField)) ≤ 2 ^ 131072 :=
  (retainedField_absNorm_differentIdeal_le_two_pow_iff 131072).2 h

/-- Direct factorization form, suitable for a local-to-global different
calculation that produces the rational `2`-adic exponent. -/
theorem retainedField_absNorm_differentIdeal_le_target_of_factorization
    (h : (Ideal.absNorm (differentIdeal (RingOfIntegers GenusField)
      (RingOfIntegers RetainedField))).factorization 2 ≤ 131072) :
    Ideal.absNorm (differentIdeal (RingOfIntegers GenusField)
      (RingOfIntegers RetainedField)) ≤ 2 ^ 131072 := by
  apply retainedField_absNorm_differentIdeal_le_target_of_twoExponent
  exact h

/-- The precise local-to-global interface for a dyadic local different
exponent `d₂`.  The factor `16384` is the expected number of primes of the
retained field above two (`524288 / 32`), and `4` is their absolute residue
degree.  Establishing this predicate from the chosen completion is a separate
localization theorem; no instance is asserted here. -/
def HasDyadicLocalDifferentExponent (d₂ : ℕ) : Prop :=
  retainedRelativeDifferentTwoExponent = 16384 * 4 * d₂

/-- The local-to-global exponent formula immediately gives the corresponding
exact norm formula. -/
theorem retainedField_absNorm_differentIdeal_eq_of_localDifferentExponent
    (d₂ : ℕ) (hlocal : HasDyadicLocalDifferentExponent d₂) :
    Ideal.absNorm (differentIdeal (RingOfIntegers GenusField)
      (RingOfIntegers RetainedField)) = 2 ^ (16384 * 4 * d₂) := by
  rw [retainedField_absNorm_differentIdeal_eq_two_pow_factorization]
  exact congrArg (2 ^ ·) hlocal

/-- Once the completion comparison supplies the global scaling formula, the
sharp residual local premise is `d₂ ≤ 2`. -/
theorem retainedField_absNorm_differentIdeal_le_target_of_localDifferentExponent
    (d₂ : ℕ) (hlocal : HasDyadicLocalDifferentExponent d₂) (hd₂ : d₂ ≤ 2) :
    Ideal.absNorm (differentIdeal (RingOfIntegers GenusField)
      (RingOfIntegers RetainedField)) ≤ 2 ^ 131072 := by
  apply retainedField_absNorm_differentIdeal_le_target_of_twoExponent
  rw [hlocal]
  calc
    16384 * 4 * d₂ ≤ 16384 * 4 * 2 := Nat.mul_le_mul_left (16384 * 4) hd₂
    _ = 131072 := by norm_num

end ArithmeticRetained

namespace CanonicalRetained

open NumberFieldAnalysis Witness

/-- After the proved genus-discriminant computation, the canonical
retained-field root-discriminant bound follows from the residual exponent at
two alone. -/
theorem log_rootDiscriminant_le_logRD_of_relativeDifferentTwoExponent
    (hdyadic : ArithmeticRetained.retainedRelativeDifferentTwoExponent ≤ 131072) :
    Real.log (rootDiscriminant Carrier) ≤ logRD :=
  log_rootDiscriminant_le_logRD_of_relativeDifferent
    (ArithmeticRetained.retainedField_absNorm_differentIdeal_le_target_of_twoExponent
      hdyadic)

/-- Root-discriminant form with the completion formula and the local different
exponent bound kept as separate premises. -/
theorem log_rootDiscriminant_le_logRD_of_localDifferentExponent
    (d₂ : ℕ) (hlocal : ArithmeticRetained.HasDyadicLocalDifferentExponent d₂)
    (hd₂ : d₂ ≤ 2) :
    Real.log (rootDiscriminant Carrier) ≤ logRD :=
  log_rootDiscriminant_le_logRD_of_relativeDifferent
    (ArithmeticRetained.retainedField_absNorm_differentIdeal_le_target_of_localDifferentExponent
      d₂ hlocal hd₂)

end CanonicalRetained

open NumberFieldAnalysis Witness

/-- The strengthened planar endpoint with the relative-different norm premise
replaced by its exact residual exponent at two. -/
theorem target_of_pair_dyadicTwoExponent_and_zeta_bound
    (hoverlap : normalizedPairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMass ≤ normalizedPairMassUpper *
      (pairArchScale / (s * p - 1) ^ 2))
    (hdyadic : ArithmeticRetained.retainedRelativeDifferentTwoExponent ≤ 131072)
    (hfinite : Real.log (dedekindZeta CanonicalRetained.Carrier
          ((1 + (1 / 12000 : ℝ) : ℝ) : ℂ)).re / (524288 : ℝ) +
        (1 / 12000 : ℝ) *
          ((logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
            (logDeriv (dedekindZeta CanonicalRetained.Carrier) 2).re /
              (524288 : ℝ)) < ceiling) :
    Target :=
  target_of_pair_dyadic_and_zeta_bound hoverlap hmass
    (ArithmeticRetained.retainedField_absNorm_differentIdeal_le_target_of_twoExponent
      hdyadic)
    hfinite

/-- Certificate form of the strengthened endpoint. -/
theorem target_of_pair_dyadicTwoExponent_and_retained_zeta_certificate
    (hoverlap : normalizedPairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMass ≤ normalizedPairMassUpper *
      (pairArchScale / (s * p - 1) ^ 2))
    (hdyadic : ArithmeticRetained.retainedRelativeDifferentTwoExponent ≤ 131072)
    (hzeta : NumberFieldAnalysis.FixedZetaCertificate.Certificate
      ArithmeticRetained.RetainedField logRD) :
    Target :=
  target_of_pair_dyadic_and_retained_zeta_certificate hoverlap hmass
    (ArithmeticRetained.retainedField_absNorm_differentIdeal_le_target_of_twoExponent
      hdyadic)
    hzeta

/-- Certificate endpoint reduced to the explicit completion formula and the
local different exponent bound `d₂ ≤ 2`. -/
theorem target_of_pair_localDifferentExponent_and_retained_zeta_certificate
    (hoverlap : normalizedPairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMass ≤ normalizedPairMassUpper *
      (pairArchScale / (s * p - 1) ^ 2))
    (d₂ : ℕ) (hlocal : ArithmeticRetained.HasDyadicLocalDifferentExponent d₂)
    (hd₂ : d₂ ≤ 2)
    (hzeta : NumberFieldAnalysis.FixedZetaCertificate.Certificate
      ArithmeticRetained.RetainedField logRD) :
    Target :=
  target_of_pair_dyadic_and_retained_zeta_certificate hoverlap hmass
    (ArithmeticRetained.retainedField_absNorm_differentIdeal_le_target_of_localDifferentExponent
      d₂ hlocal hd₂)
    hzeta

end UnitDistance
