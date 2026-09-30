module

public import UnitDistance.SharperPairFixedBaseCoreRun20260920
public import UnitDistance.RelativeArithmeticAmplitude

@[expose] public section
set_option backward.privateInPublic true


/-!
# Arithmetic-rate core of the sharper-pair fixed-base bridge

This research leaf connects the lightweight sharper-pair scalar bound to the
ordinary arithmetic rate.  It has no retained tower, Galois quotient, or
sigma-cut dependency.
-/

noncomputable section
set_option autoImplicit false

open NumberField

namespace UnitDistance.RelativeUnits

open NumberFieldAnalysis Witness

/-- Raising the residue cap from `ceiling` to `U` costs exactly `U-ceiling`
in the arithmetic rate. -/
theorem sharperPair_shifted_margin_le_arithmeticRate_run20260920
    {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
    {U : ℝ}
    (hdisc : Real.log (rootDiscriminant F) ≤ Witness.logRD)
    (hresidue : Real.log (relativeResidue K F) /
      (Module.finrank ℚ F : ℝ) ≤ U) :
    Witness.margin (signatureRatio F) - 4 * Witness.epsilon +
        Witness.ceiling - U ≤
      arithmeticRate F K Witness.finiteProfit Witness.epsilon := by
  have hd := mul_le_mul_of_nonneg_left hdisc
    (show (0 : ℝ) ≤ 1 / 2 - increment by norm_num [increment])
  dsimp only [Witness.margin, arithmeticRate]
  linarith

/-- The relaxed-threshold gap is a uniform lower bound for the actual
arithmetic rate under the corresponding residue cap. -/
theorem sharperFixedBaseGap_le_arithmeticRate_run20260920
    {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
    {U : ℝ}
    (hdisc : Real.log (rootDiscriminant F) ≤ Witness.logRD)
    (hresidue : Real.log (relativeResidue K F) /
      (Module.finrank ℚ F : ℝ) ≤ U)
    (hsignature : Witness.thetaMin ≤ signatureRatio F) :
    Witness.sharperFixedBaseCeilingRun20260920 - U ≤
      arithmeticRate F K Witness.finiteProfit Witness.epsilon :=
  (Witness.sharperFixedBaseGap_le_shiftedMargin_run20260920 hsignature).trans
    (sharperPair_shifted_margin_le_arithmeticRate_run20260920 hdisc hresidue)

end UnitDistance.RelativeUnits
