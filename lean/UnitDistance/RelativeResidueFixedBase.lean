module

public import UnitDistance.PrimeDebit
public import UnitDistance.RelativeResiduePrimeBudget
public import UnitDistance.Witness

@[expose] public section
set_option backward.privateInPublic true


/-!
# A fixed actual finite field supplies the residue ceiling

The sole numerical premise is an explicit scalar inequality involving the
zeta value and convergent prime remainder of the specified finite field `M`.
The field itself, its inclusions in the growing family, the actual root
discriminants and completed relative functions retain their literal meanings.
No assertion about an unspecified good base field is hidden in that scalar.
-/

noncomputable section
open NumberField Filter Topology
open scoped BigOperators
namespace UnitDistance.NumberFieldAnalysis

variable (M : Type*) [Field M] [NumberField M]
  (Ks Fs : ℕ → Type*)
  [∀ n, Field (Ks n)] [∀ n, NumberField (Ks n)]
  [∀ n, Field (Fs n)] [∀ n, NumberField (Fs n)]
  [∀ n, Algebra (Fs n) (Ks n)] [∀ n, Algebra M (Ks n)]

/-- The finite numerical expression attached to one actual, specified base
field. All quantities are independently defined ordinary arithmetic ones. -/
def fixedBaseResidueCeiling (ell epsilon : ℝ) : ℝ :=
  Real.log (dedekindZeta M ((1+epsilon:ℝ):ℂ)).re/(Module.finrank ℚ M : ℝ) +
    epsilon*((ell-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4+
      normalizedPrimeDebit M)

/-- The full family inherits the strict scalar ceiling from the fixed finite
base. Prime-frequency limits and the unconditional basic inequality are
proved internally by subsequence extraction. -/
theorem eventual_normalized_log_relativeResidue_lt_of_fixed_base
    (hquad : ∀ n, Module.finrank (Fs n) (Ks n) = 2)
    (hdegree : Tendsto (fun n => Module.finrank ℚ (Ks n)) atTop atTop)
    (hcomplex : ∀ᶠ n in atTop, InfinitePlace.nrRealPlaces (Ks n) = 0)
    {ell epsilon T : ℝ} (hepsilon : 0 < epsilon)
    (hdisc : ∀ᶠ n in atTop, Real.log (rootDiscriminant (Ks n)) ≤ ell)
    (hcomp : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      relativeCompletedReal (Ks n) (Fs n) ell 1 ≤
        relativeCompletedReal (Ks n) (Fs n) ell (1+eta))
    (hfinite : fixedBaseResidueCeiling M ell epsilon < T) :
    ∀ᶠ n in atTop, Real.log (relativeResidue (Ks n) (Fs n)) /
      (Module.finrank ℚ (Fs n) : ℝ) < T := by
  apply eventual_normalized_log_relativeResidue_lt_of_prime_budget Ks Fs
    hquad hdegree hcomplex hepsilon hdisc hcomp
    (Y := Real.log (dedekindZeta M ((1+epsilon:ℝ):ℂ)).re/(Module.finrank ℚ M : ℝ))
    (R := normalizedPrimeDebit M)
  · filter_upwards [] with n
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using
      normalized_log_dedekindZeta_le_base (Ks n) M (by linarith : 1<1+epsilon)
  · intro J
    filter_upwards [] with n
    have h := (finite_normalizedPrimeDebit_le (Ks n) J).trans
      (normalizedPrimeDebit_le_base (Ks n) M)
    simpa only [primeDebitWeight, Nat.cast_add, Nat.cast_ofNat] using h
  · exact hfinite

/-- The manuscript's abscissa and exact target are fixed rational numbers.
This endpoint retains only actual arithmetic-family/completion data and one
explicit numerical inequality for the specified finite field `M`. -/
theorem eventual_normalized_log_relativeResidue_lt_witness_of_fixed_base
    (hquad : ∀ n, Module.finrank (Fs n) (Ks n) = 2)
    (hdegree : Tendsto (fun n => Module.finrank ℚ (Ks n)) atTop atTop)
    (hcomplex : ∀ᶠ n in atTop, InfinitePlace.nrRealPlaces (Ks n) = 0)
    (hdisc : ∀ᶠ n in atTop, Real.log (rootDiscriminant (Ks n)) ≤ Witness.logRD)
    (hcomp : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      relativeCompletedReal (Ks n) (Fs n) Witness.logRD 1 ≤
        relativeCompletedReal (Ks n) (Fs n) Witness.logRD (1+eta))
    (hfinite : fixedBaseResidueCeiling M Witness.logRD (1/12000) < Witness.ceiling) :
    ∀ᶠ n in atTop, Real.log (relativeResidue (Ks n) (Fs n)) /
      (Module.finrank ℚ (Fs n) : ℝ) < Witness.ceiling :=
  eventual_normalized_log_relativeResidue_lt_of_fixed_base M Ks Fs
    hquad hdegree hcomplex (by norm_num) hdisc hcomp hfinite

end UnitDistance.NumberFieldAnalysis
