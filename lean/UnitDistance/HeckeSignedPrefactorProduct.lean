module

public import UnitDistance.HeckeSignedNormalization

@[expose] public section
set_option backward.privateInPublic true


open NumberField NumberField.InfinitePlace DedekindResidue
open scoped Real Classical
namespace UnitDistance.NumberFieldAnalysis

/-- In a totally complex degree-two extension with squared absolute discriminant,
the actual completed-zeta prefactor factors by the signed Hecke prefactor. The
statement is purely algebraic in the signature and discriminant data and holds
at every complex parameter, including Gamma poles under their totalized values. -/
theorem completedZetaPrefactor_eq_mul_signedHeckePrefactor
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    (hreal : nrRealPlaces K = 0)
    (hdegree : Module.finrank ℚ K = 2 * Module.finrank ℚ F)
    (hdiscr : (|discr K| : ℝ) = (|discr F| : ℝ)^2) (s : ℂ) :
    completedZetaPrefactor K s = completedZetaPrefactor F s * signedHeckePrefactor F s := by
  have hc : nrComplexPlaces K = nrRealPlaces F + 2 * nrComplexPlaces F := by
    have hK := card_add_two_mul_card_eq_rank (K := K)
    have hF := card_add_two_mul_card_eq_rank (K := F)
    omega
  have hd : ((|discr K| : ℝ) : ℂ) ^ (s/2) =
      ((|discr F| : ℝ) : ℂ) ^ (s/2) * ((|discr F| : ℝ) : ℂ) ^ (s/2) := by
    rw [hdiscr, Complex.ofReal_pow, pow_two]
    exact Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _) _
  unfold completedZetaPrefactor gammaFactor signedHeckePrefactor
  rw [hd, hreal, pow_zero, one_mul, hc, pow_add, Nat.mul_comm 2 (nrComplexPlaces F), pow_mul]
  have hg : Complex.Gammaℝ s ^ nrRealPlaces F * Complex.Gammaℝ (s+1) ^ nrRealPlaces F =
      Complex.Gammaℂ s ^ nrRealPlaces F := by
    rw [← mul_pow, Complex.Gammaℝ_mul_Gammaℝ_add_one]
  rw [← hg]
  ring

end UnitDistance.NumberFieldAnalysis
