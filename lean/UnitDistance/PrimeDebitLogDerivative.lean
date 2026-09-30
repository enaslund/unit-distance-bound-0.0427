module

public import UnitDistance.RelativeResidueFixedBase

@[expose] public section
set_option backward.privateInPublic true


/-! The fixed-field prime remainder is the ordinary Dedekind zeta
logarithmic derivative at two. This identifies the numerical input with
fixed special-function values of the independently specified finite field. -/

noncomputable section
open NumberField IsDedekindDomain
open scoped BigOperators
namespace UnitDistance.NumberFieldAnalysis

variable (K : Type*) [Field K] [NumberField K]

theorem primeDebitWeight_complex_euler_term {q : ℝ} (hq : 1 < q) :
    Complex.log (q:ℂ)*(q:ℂ)^(-(2:ℂ))/(1-(q:ℂ)^(-(2:ℂ))) =
      (primeDebitWeight q : ℂ) := by
  have hq0 : 0 < q := by linarith
  have hqC : (q:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0.ne'
  rw [← Complex.ofReal_log hq0.le, Complex.cpow_neg, Complex.cpow_ofNat]
  have hd : (q:ℂ)^2-1 ≠ 0 := by
    have hreal : q^2-1 ≠ 0 := by nlinarith
    exact_mod_cast hreal
  simp only [primeDebitWeight, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_pow, Complex.ofReal_one]
  field_simp

/-- The actual convergent remainder equals one logarithmic derivative of
ordinary Dedekind zeta at the fixed real point two. -/
theorem normalizedPrimeDebit_eq_neg_logDeriv :
    normalizedPrimeDebit K = -(logDeriv (dedekindZeta K) 2).re /
      (Module.finrank ℚ K : ℝ) := by
  have h := DedekindResidue.neg_logDeriv_dedekindZeta_eq_tsum K
    (s := (2:ℂ)) (by norm_num)
  have hterm : (fun P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      Complex.log (Ideal.absNorm P.1 : ℂ)*(Ideal.absNorm P.1 : ℂ)^(-(2:ℂ))/
        (1-(Ideal.absNorm P.1 : ℂ)^(-(2:ℂ)))) =
      fun P => (primeDebitWeight (Ideal.absNorm P.1) : ℂ) := by
    funext P
    have hq : (1:ℝ) < Ideal.absNorm P.1 := by
      exact_mod_cast primeIdeal_absNorm_gt_one K ((tvPrimeIdealEquiv K) P)
    simpa only [Complex.ofReal_natCast] using primeDebitWeight_complex_euler_term hq
  rw [hterm] at h
  have hs : HasSum (fun P : HeightOneSpectrum (𝓞 K) =>
      (primeDebitWeight (Ideal.absNorm P.asIdeal) : ℂ))
      (Complex.ofReal (∑' P : HeightOneSpectrum (𝓞 K),
        primeDebitWeight (Ideal.absNorm P.asIdeal))) :=
    Complex.hasSum_ofReal.mpr (summable_primeDebit K).hasSum
  have hs' := (tvPrimeIdealEquiv K).hasSum_iff.mpr hs
  have he := congrArg Complex.re (h.trans hs'.tsum_eq)
  simp only [Complex.neg_re, Complex.ofReal_re] at he
  unfold normalizedPrimeDebit
  rw [← he]

/-- An equivalent version of the independently specified fixed-field scalar,
using only zeta and its logarithmic derivative at two fixed abscissae. -/
theorem fixedBaseResidueCeiling_eq_zeta_logDeriv (ell epsilon : ℝ) :
    fixedBaseResidueCeiling K ell epsilon =
      Real.log (dedekindZeta K ((1+epsilon:ℝ):ℂ)).re/(Module.finrank ℚ K : ℝ) +
        epsilon*((ell-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4-
          (logDeriv (dedekindZeta K) 2).re/(Module.finrank ℚ K : ℝ)) := by
  rw [fixedBaseResidueCeiling, normalizedPrimeDebit_eq_neg_logDeriv]
  ring

end UnitDistance.NumberFieldAnalysis
