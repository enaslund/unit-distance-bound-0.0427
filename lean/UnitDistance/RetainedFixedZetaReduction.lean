module

public import UnitDistance.ArithmeticCompletedEmbedding
public import UnitDistance.FixedZetaCertificate
public import UnitDistance.NumberFieldNumericInvariance

@[expose] public section
set_option backward.privateInPublic true


/-!
# Fixed-zeta reduction for the actual retained field

This specializes the finite Euler-defect interface to the proved embedding of
the degree-`16384` completed field in the degree-`524288` retained field.  It
also transfers the resulting fixed-field inequality to the independently
defined canonical retained field used in `ChallengeFull`.
-/

noncomputable section
open NumberField IsDedekindDomain
open scoped BigOperators

namespace UnitDistance.NumberFieldAnalysis.RetainedFixedZetaReduction

open ArithmeticCompleted ArithmeticRetained
open FixedZetaCertificate

local instance completedRetainedAlgebra : Algebra CompletedField RetainedField :=
  completedEmbeddingRat.toRingHom.toAlgebra

/-- The proved completed-to-retained embedding has relative degree `32`. -/
theorem completedRetained_degree : Module.finrank CompletedField RetainedField = 32 := by
  have h := Module.finrank_mul_finrank ℚ CompletedField RetainedField
  rw [ArithmeticCompleted.completedField_degree,
    ArithmeticRetained.retainedField_degree] at h
  omega

/-- Closed local correction formula for the actual degree-`32` extension.
This leaves only finite fiber cardinality and norm certificates at each census
prime. -/
theorem completedRetained_primeFiberEulerDefect_eq_of_card_norm
    (p : HeightOneSpectrum (𝓞 CompletedField)) (s : ℝ) (q Q g : ℕ)
    (hbase : Ideal.absNorm p.asIdeal = q)
    (hcard : Fintype.card (PrimeFiber CompletedField RetainedField p) = g)
    (hnorm : ∀ P : PrimeFiber CompletedField RetainedField p,
      Ideal.absNorm P.1.asIdeal = Q) :
    primeFiberEulerDefect CompletedField RetainedField p s =
      32 * primeEulerLog q s - (g : ℝ) * primeEulerLog Q s := by
  rw [primeFiberEulerDefect_eq_of_card_norm CompletedField RetainedField p s q Q g
    hbase hcard hnorm, completedRetained_degree]
  norm_num

/-- The concrete remaining certificate data, with the actual completed-field
embedding supplying the extension in every local prime fiber. -/
def certificate_of_completed_defects
    (J : Finset (HeightOneSpectrum (𝓞 CompletedField)))
    (lower : HeightOneSpectrum (𝓞 CompletedField) → ℝ)
    (factorValue selectedPrimeContribution orderFourSaving centralSaving debitValue : ℝ)
    (hlower : ∀ p ∈ J,
      lower p ≤ primeFiberEulerDefect CompletedField RetainedField p (1 + epsilon))
    (hbase :
      Real.log (dedekindZeta CompletedField ((1 + epsilon : ℝ) : ℂ)).re /
          (Module.finrank ℚ CompletedField : ℝ) ≤
        factorValue + selectedPrimeContribution)
    (hsavings : orderFourSaving + centralSaving ≤
      (∑ p ∈ J, lower p) / (Module.finrank ℚ RetainedField : ℝ))
    (hfactor : factorValue ≤ factorAllowance)
    (hselected : selectedPrimeContribution ≤ selectedPrimeAllowance)
    (horderFour : orderFourSavingAllowance ≤ orderFourSaving)
    (hcentral : centralSavingAllowance ≤ centralSaving)
    (hdebit : epsilon *
      ((Witness.logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 +
        normalizedPrimeDebit RetainedField) ≤ debitValue)
    (hdebitUpper : debitValue ≤ debitAllowance) :
    Certificate RetainedField Witness.logRD where
  factorValue := factorValue
  selectedPrimeContribution := selectedPrimeContribution
  orderFourSaving := orderFourSaving
  centralSaving := centralSaving
  debitValue := debitValue
  eulerComparison := eulerComparison_of_finite_defects
    CompletedField RetainedField J lower factorValue selectedPrimeContribution
      orderFourSaving centralSaving hlower hbase hsavings
  factorUpper := hfactor
  selectedPrimeUpper := hselected
  orderFourLower := horderFour
  centralLower := hcentral
  debitComparison := hdebit
  debitUpper := hdebitUpper

/-- A retained-field certificate proves the exact canonical fixed-field
premise appearing in `ChallengeFull`. -/
theorem canonical_hfinite_of_retained_certificate
    (c : Certificate RetainedField Witness.logRD) :
    Real.log (dedekindZeta CanonicalRetained.Carrier
        ((1 + (1 / 12000 : ℝ) : ℝ) : ℂ)).re / (524288 : ℝ) +
      (1 / 12000 : ℝ) *
        ((Witness.logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
          (logDeriv (dedekindZeta CanonicalRetained.Carrier) 2).re / (524288 : ℝ)) <
      Witness.ceiling := by
  have h := zeta_logDeriv_lt_of_certificate RetainedField c
  rw [ArithmeticRetained.retainedField_degree] at h
  simpa only [Nat.cast_ofNat, dedekindZeta_eq_of_algEquiv CanonicalRetained.equiv,
    logDeriv_dedekindZeta_eq_of_algEquiv CanonicalRetained.equiv] using h

end UnitDistance.NumberFieldAnalysis.RetainedFixedZetaReduction
