module

public import UnitDistance.Sqrt241.Geometry.RelativeArithmeticAmplitude

@[expose] public section
set_option backward.privateInPublic true


/-!
# Arithmetic-rate core of the fixed-base bridge over `ℚ(√241)`

Replaces `UnitDistance.SharperPairFixedBaseCoreRun20260920` and
`UnitDistance.SharperPairArithmeticRateCoreRun20260920`. The ℚ bridge relaxed
its threshold by `4e-6` using an internally proved sharper pair margin. Here
the threshold is `Witness.ceiling` itself, and the positivity of the margin
over the signature range is an explicit hypothesis `hmargin` (proved in `Numerics/`
as `UnitDistance.Sqrt241.Witness.uniform_margin`).
-/

noncomputable section
set_option autoImplicit false
open NumberField

namespace UnitDistance.Sqrt241.RelativeUnits
open UnitDistance.NumberFieldAnalysis UnitDistance.RelativeUnits

/-- Raising the residue cap from `ceiling` to `U` costs exactly `U - ceiling`
in the arithmetic rate. Copy of
`UnitDistance.RelativeUnits.sharperPair_shifted_margin_le_arithmeticRate_run20260920`. -/
theorem shifted_margin_le_arithmeticRate
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

/-- With a positive margin over the signature range, the gap between the
threshold `ceiling` and a residue cap `U` bounds the actual arithmetic rate. -/
theorem fixedBaseGap_le_arithmeticRate
    (hmargin : ∀ θ : ℝ, Witness.thetaMin ≤ θ →
      0 < Witness.margin θ - 4 * Witness.epsilon)
    {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
    {U : ℝ}
    (hdisc : Real.log (rootDiscriminant F) ≤ Witness.logRD)
    (hresidue : Real.log (relativeResidue K F) /
      (Module.finrank ℚ F : ℝ) ≤ U)
    (hsignature : Witness.thetaMin ≤ signatureRatio F) :
    Witness.ceiling - U ≤ arithmeticRate F K Witness.finiteProfit Witness.epsilon := by
  have h := hmargin _ hsignature
  have h2 := shifted_margin_le_arithmeticRate (K := K) hdisc hresidue
  linarith

end UnitDistance.Sqrt241.RelativeUnits
