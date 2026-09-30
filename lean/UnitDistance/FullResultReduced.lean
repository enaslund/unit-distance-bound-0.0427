module

public import UnitDistance.FullResult
public import UnitDistance.PairFunctionalCertificate
public import UnitDistance.RetainedDiscriminantBridge
public import UnitDistance.RetainedFixedZetaReduction

@[expose] public section
set_option backward.privateInPublic true


/-!
# Full result with reduced numerical obligations

This endpoint refines all three scalar hypotheses of
`target_of_three_finite_bounds`:

* the pair functional is replaced by the two directed mass and overlap
  intervals emitted by the profile certificate;
* the genus discriminant is computed exactly and relative odd-prime
  ramification is eliminated, leaving the relative dyadic different;
* the fixed-field zeta inequality may be supplied by a proof-bearing finite
  Euler/debit certificate for the actual retained field.

The older five-premise theorem is retained below as a compatibility interface.
-/

noncomputable section
namespace UnitDistance
open NumberField
open NumberFieldAnalysis
open Witness

/-- The planar sequence theorem from direct profile intervals, two discrete
discriminant bounds, and the remaining fixed-field zeta inequality. -/
theorem target_of_reduced_finite_bounds
    (hoverlap : normalizedPairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMass ≤ normalizedPairMassUpper *
      (pairArchScale / (s * p - 1) ^ 2))
    (hgenus : (discr ArithmeticChosenGenus.GenusField).natAbs ≤
      2 ^ 256 * 15015 ^ 64)
    (hdyadic : Ideal.absNorm
      (differentIdeal (RingOfIntegers ArithmeticChosenGenus.GenusField)
        (RingOfIntegers ArithmeticRetained.RetainedField)) ≤ 2 ^ 131072)
    (hfinite : Real.log (dedekindZeta CanonicalRetained.Carrier
          ((1 + (1 / 12000 : ℝ) : ℝ) : ℂ)).re / (524288 : ℝ) +
        (1 / 12000 : ℝ) *
          ((logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
            (logDeriv (dedekindZeta CanonicalRetained.Carrier) 2).re /
              (524288 : ℝ)) < ceiling) :
    Target := by
  apply target_of_three_finite_bounds
  · exact pairFunctional_of_integral_intervals hoverlap hmass
  · exact CanonicalRetained.log_rootDiscriminant_le_logRD_of_genus_and_relativeDifferent
      hgenus hdyadic
  · exact hfinite

/-- Stronger endpoint after the exact genus-discriminant computation.  The
entire discriminant side is reduced to the dyadic relative different. -/
theorem target_of_pair_dyadic_and_zeta_bound
    (hoverlap : normalizedPairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMass ≤ normalizedPairMassUpper *
      (pairArchScale / (s * p - 1) ^ 2))
    (hdyadic : Ideal.absNorm
      (differentIdeal (RingOfIntegers ArithmeticChosenGenus.GenusField)
        (RingOfIntegers ArithmeticRetained.RetainedField)) ≤ 2 ^ 131072)
    (hfinite : Real.log (dedekindZeta CanonicalRetained.Carrier
          ((1 + (1 / 12000 : ℝ) : ℝ) : ℂ)).re / (524288 : ℝ) +
        (1 / 12000 : ℝ) *
          ((logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
            (logDeriv (dedekindZeta CanonicalRetained.Carrier) 2).re /
              (524288 : ℝ)) < ceiling) :
    Target := by
  apply target_of_three_finite_bounds
  · exact pairFunctional_of_integral_intervals hoverlap hmass
  · exact CanonicalRetained.log_rootDiscriminant_le_logRD_of_relativeDifferent
      hdyadic
  · exact hfinite

/-- The fixed-zeta premise can itself be supplied by the proof-bearing
finite-factor, finite-census, and prime-debit certificate. -/
theorem target_of_pair_dyadic_and_retained_zeta_certificate
    (hoverlap : normalizedPairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : pairMass ≤ normalizedPairMassUpper *
      (pairArchScale / (s * p - 1) ^ 2))
    (hdyadic : Ideal.absNorm
      (differentIdeal (RingOfIntegers ArithmeticChosenGenus.GenusField)
        (RingOfIntegers ArithmeticRetained.RetainedField)) ≤ 2 ^ 131072)
    (hzeta : NumberFieldAnalysis.FixedZetaCertificate.Certificate
      ArithmeticRetained.RetainedField logRD) :
    Target := by
  apply target_of_pair_dyadic_and_zeta_bound hoverlap hmass hdyadic
  exact NumberFieldAnalysis.RetainedFixedZetaReduction.canonical_hfinite_of_retained_certificate
    hzeta

end UnitDistance
