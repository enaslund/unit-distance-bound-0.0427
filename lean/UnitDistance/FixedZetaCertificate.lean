module

public import UnitDistance.FiniteEulerCorrection
public import UnitDistance.PrimeDebitLogDerivative
public import UnitDistance.CanonicalRetainedEquiv

@[expose] public section
set_option backward.privateInPublic true


/-!
# Finite-certificate interface for the fixed-field zeta premise

The fixed-field premise in `FullResult` is supported in the manuscript by
five directed numerical allowances: a finite factor evaluation, restoration
of selected Euler factors, two disjoint finite-prime savings, and the
prime-budget debit.  This file records those exact rational endpoints and
proves their final strict arithmetic comparison in Lean.

The analytic and census outputs remain explicit proof fields of `Certificate`.
Thus constructing a value of that structure requires mathematical theorems
connecting each checked finite computation to the actual Dedekind zeta and
prime debit; a hash or a Boolean replay result cannot inhabit it.
-/

noncomputable section
open NumberField

namespace UnitDistance.NumberFieldAnalysis.FixedZetaCertificate

/-- The manuscript's fixed abscissa minus one. -/
def epsilon : ℝ := 1 / 12000

/-- Upper allowance for the imprimitive completed-field factor evaluation. -/
def factorAllowance : ℝ := 445355407103547 / 10^18

/-- Upper allowance for restoring the seven selected rational-prime factors. -/
def selectedPrimeAllowance : ℝ := 41727023150898786 / 10^18

/-- Lower allowance for the 45 order-four corrections. -/
def orderFourSavingAllowance : ℝ :=
  3724741189544274807446 / 10^26

/-- Lower allowance for the retained-versus-completed census correction. -/
def centralSavingAllowance : ℝ :=
  4201663320373563276702 / 10^26

/-- Upper allowance for `epsilon` times the archimedean and prime-debit slope. -/
def debitAllowance : ℝ :=
  6870442657779491222606 / 10^26

/-- The exact sum of the five published directed allowances clears the exact
ceiling.  This is kernel-checked rational arithmetic. -/
theorem allowance_sum_lt_ceiling :
    factorAllowance + selectedPrimeAllowance - orderFourSavingAllowance -
      centralSavingAllowance + debitAllowance < Witness.ceiling := by
  norm_num [factorAllowance, selectedPrimeAllowance, orderFourSavingAllowance,
    centralSavingAllowance, debitAllowance, Witness.ceiling]

/-- Build the certificate's Euler-comparison field from an actual finite
extension and finitely many certified local defects.  The first premise is
the completed/base-field factor evaluation (including restored factors); the
second says that the normalized finite defects cover the two stated savings.
-/
theorem eulerComparison_of_finite_defects
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K]
    (J : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (lower : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℝ)
    (factorValue selectedPrimeContribution orderFourSaving centralSaving : ℝ)
    (hlower : ∀ p ∈ J, lower p ≤ primeFiberEulerDefect F K p (1 + epsilon))
    (hbase :
      Real.log (dedekindZeta F ((1 + epsilon : ℝ) : ℂ)).re /
          (Module.finrank ℚ F : ℝ) ≤ factorValue + selectedPrimeContribution)
    (hsavings : orderFourSaving + centralSaving ≤
      (∑ p ∈ J, lower p) / (Module.finrank ℚ K : ℝ)) :
    Real.log (dedekindZeta K ((1 + epsilon : ℝ) : ℂ)).re /
        (Module.finrank ℚ K : ℝ) ≤
      factorValue + selectedPrimeContribution - orderFourSaving - centralSaving := by
  have hs : (1 : ℝ) < 1 + epsilon := by norm_num [epsilon]
  have h := normalized_log_dedekindZeta_le_sub_certificate F K hs J lower hlower
  linarith

variable (K : Type*) [Field K] [NumberField K]

/-- Proof-bearing interface for the fixed numerical computation.

`eulerComparison` is the mathematical bridge from the finite factor and
census quantities to the actual normalized zeta value.  The next four fields
are independently directed enclosures.  `debitComparison` connects the
remaining finite computation to the actual convergent prime debit. -/
structure Certificate (ell : ℝ) where
  factorValue : ℝ
  selectedPrimeContribution : ℝ
  orderFourSaving : ℝ
  centralSaving : ℝ
  debitValue : ℝ
  eulerComparison :
    Real.log (dedekindZeta K ((1 + epsilon : ℝ) : ℂ)).re /
        (Module.finrank ℚ K : ℝ) ≤
      factorValue + selectedPrimeContribution - orderFourSaving - centralSaving
  factorUpper : factorValue ≤ factorAllowance
  selectedPrimeUpper : selectedPrimeContribution ≤ selectedPrimeAllowance
  orderFourLower : orderFourSavingAllowance ≤ orderFourSaving
  centralLower : centralSavingAllowance ≤ centralSaving
  debitComparison :
    epsilon * ((ell - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 +
      normalizedPrimeDebit K) ≤ debitValue
  debitUpper : debitValue ≤ debitAllowance

/-- A proof-bearing certificate implies the strict fixed-base ceiling. -/
theorem fixedBaseResidueCeiling_lt_of_certificate {ell : ℝ}
    (c : Certificate K ell) :
    fixedBaseResidueCeiling K ell epsilon < Witness.ceiling := by
  rw [fixedBaseResidueCeiling]
  have hzeta :
      Real.log (dedekindZeta K ((1 + epsilon : ℝ) : ℂ)).re /
          (Module.finrank ℚ K : ℝ) ≤
        factorAllowance + selectedPrimeAllowance - orderFourSavingAllowance -
          centralSavingAllowance := by
    calc
      _ ≤ c.factorValue + c.selectedPrimeContribution - c.orderFourSaving -
          c.centralSaving := c.eulerComparison
      _ ≤ factorAllowance + selectedPrimeAllowance - orderFourSavingAllowance -
          centralSavingAllowance := by linarith [c.factorUpper, c.selectedPrimeUpper,
            c.orderFourLower, c.centralLower]
  have hdebit :
      epsilon * ((ell - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 +
        normalizedPrimeDebit K) ≤ debitAllowance :=
    c.debitComparison.trans c.debitUpper
  linarith [allowance_sum_lt_ceiling]

/-- The certificate conclusion in the exact zeta/logarithmic-derivative form
used by `FullResult`. -/
theorem zeta_logDeriv_lt_of_certificate {ell : ℝ}
    (c : Certificate K ell) :
    Real.log (dedekindZeta K ((1 + (1 / 12000 : ℝ) : ℝ) : ℂ)).re /
        (Module.finrank ℚ K : ℝ) + (1 / 12000 : ℝ) *
      ((ell - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
        (logDeriv (dedekindZeta K) 2).re / (Module.finrank ℚ K : ℝ)) <
      Witness.ceiling := by
  have h := fixedBaseResidueCeiling_lt_of_certificate K c
  rw [fixedBaseResidueCeiling_eq_zeta_logDeriv] at h
  exact h

/-- Specialization to the independently defined canonical retained field and
the literal denominator appearing in `ChallengeFull`. -/
theorem canonical_hfinite_of_certificate
    (c : Certificate CanonicalRetained.Carrier Witness.logRD) :
    Real.log (dedekindZeta CanonicalRetained.Carrier
        ((1 + (1 / 12000 : ℝ) : ℝ) : ℂ)).re / (524288 : ℝ) +
      (1 / 12000 : ℝ) *
        ((Witness.logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
          (logDeriv (dedekindZeta CanonicalRetained.Carrier) 2).re / (524288 : ℝ)) <
      Witness.ceiling := by
  have h := zeta_logDeriv_lt_of_certificate CanonicalRetained.Carrier c
  simpa only [CanonicalRetained.degree, Nat.cast_ofNat] using h

end UnitDistance.NumberFieldAnalysis.FixedZetaCertificate
