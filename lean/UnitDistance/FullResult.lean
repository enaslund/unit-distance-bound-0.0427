module

public import UnitDistance.SigmaCutTarget
public import UnitDistance.SigmaCutUnconditional
public import UnitDistance.CanonicalRetainedEquiv
public import UnitDistance.NumberFieldNumericInvariance

@[expose] public section
set_option backward.privateInPublic true


/-! The full ordinary planar sequence theorem. The only inputs are three
explicit inequalities about a fixed integral and an independently specified
finite number field. All growing-field arithmetic is proved internally. -/
noncomputable section
namespace UnitDistance
open NumberField NumberFieldAnalysis Witness

/-- The exponent `2083647/2000000` is attained along a sequence of ordinary
finite planar sets, under only the three stated fixed numerical bounds. -/
theorem target_of_three_finite_bounds
    (hpair : (1379635324335 : ℝ)/10^12 ≤ JPair)
    (hdisc : Real.log (rootDiscriminant CanonicalRetained.Carrier) ≤ logRD)
    (hfinite : Real.log (dedekindZeta CanonicalRetained.Carrier
          ((1+(1/12000:ℝ):ℝ):ℂ)).re / (524288 : ℝ) + (1/12000:ℝ)*
        ((logRD-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4-
          (logDeriv (dedekindZeta CanonicalRetained.Carrier) 2).re/(524288 : ℝ)) < ceiling) :
    Target := by
  apply ArithmeticProP.SigmaCut.target_of_arithmeticPresentation
    ArithmeticProP.SigmaCut.arithmetic_presentation hpair
  · simpa only [rootDiscriminant_eq_of_algEquiv CanonicalRetained.equiv] using hdisc
  · simpa only [dedekindZeta_eq_of_algEquiv CanonicalRetained.equiv] using hfinite

end UnitDistance
