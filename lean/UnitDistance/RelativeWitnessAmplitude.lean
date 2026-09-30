module

public import UnitDistance.RelativeArithmeticAmplitude
public import UnitDistance.TensorFiniteFunctional

@[expose] public section
set_option backward.privateInPublic true


/-! # Exact arithmetic amplitude of the actual finite-shell witness -/

noncomputable section
open NumberField NumberField.InfinitePlace
namespace UnitDistance.RelativeUnits
open NumberFieldAnalysis

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]
  {S : Type*} [Fintype S]

theorem witnessArithmeticAmplitude_eq_exp (hunr : FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (v : S → Fin 11)
    (hmultiplicity : ∀ a, (Fintype.card {s // v s = a} : ℝ)*
      ((Witness.ramification a : ℝ)*Witness.residueDegree a) = Module.finrank ℚ F)
    (ε : ℝ) :
    arithmeticAmplitude ι (Witness.tensorFiniteFunctional v) ε =
      Real.exp ((Module.finrank ℚ F:ℝ)*arithmeticRate F K Witness.finiteProfit ε)/
        (2:ℝ)^(3+increment) := by
  rw [arithmeticAmplitude_eq_exp hunr ι hι hb (Witness.tensorFiniteFunctional_pos v),
    Witness.log_tensorFiniteFunctional_div_degree v (degree_pos_real (F := F)).ne' hmultiplicity]

theorem witnessArithmeticAmplitude_lower (hunr : FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (v : S → Fin 11)
    (hmultiplicity : ∀ a, (Fintype.card {s // v s = a} : ℝ)*
      ((Witness.ramification a : ℝ)*Witness.residueDegree a) = Module.finrank ℚ F)
    (hpair : (1379635324335:ℝ)/10^12 ≤ Witness.JPair)
    (hdisc : Real.log (rootDiscriminant F) ≤ Witness.logRD)
    (hresidue : Real.log (relativeResidue K F)/(Module.finrank ℚ F:ℝ) ≤ Witness.ceiling)
    (hsignature : Witness.thetaMin ≤ signatureRatio F) :
    Real.exp ((Module.finrank ℚ F:ℝ)*((533:ℝ)/10^8))/(2:ℝ)^(3+increment) ≤
      arithmeticAmplitude ι (Witness.tensorFiniteFunctional v) Witness.epsilon := by
  apply arithmeticAmplitude_lower hunr ι hι hb (Witness.tensorFiniteFunctional_pos v)
    hpair _ hdisc hresidue hsignature
  rw [Witness.log_tensorFiniteFunctional_div_degree v (degree_pos_real (F := F)).ne' hmultiplicity]

end UnitDistance.RelativeUnits
