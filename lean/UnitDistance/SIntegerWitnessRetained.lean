module

public import UnitDistance.SIntegerWitnessQuadratic
public import UnitDistance.ArithmeticRetainedField

@[expose] public section
set_option backward.privateInPublic true


/-! The quadratic arithmetic-family target with the fixed numerical input
specialized to the independently constructed actual retained field. -/

noncomputable section
open Filter NumberField NumberField.InfinitePlace
open scoped Classical
namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeUnits NumberFieldAnalysis Witness

variable (Fs Ks : ℕ → Type) (Ss : ℕ → Type*)
  [∀ j, Field (Fs j)] [∀ j, Field (Ks j)]
  [∀ j, NumberField (Fs j)] [∀ j, NumberField (Ks j)]
  [∀ j, Algebra (Fs j) (Ks j)] [∀ j, Algebra ArithmeticRetained.RetainedField (Ks j)]
  [∀ j, Algebra.IsQuadraticExtension (Fs j) (Ks j)]
  [∀ j, IsTotallyComplex (Ks j)] [∀ j, Fintype (Ss j)]

/-- The planar sequence target with actual arithmetic family hypotheses and
only the pair-integral and one fixed-field scalar numerical inequalities.
The signed theta argument supplies the entire relative factor. -/
theorem target_of_witnessFields_retainedBase
    (ι : (j : ℕ) → Ks j ≃ₐ[Fs j] Ks j)
    (D : (j : ℕ) → PrimePairFamily (ι j) (Ss j)) (v : (j : ℕ) → Ss j → Fin 11)
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Fs j)) atTop atTop)
    (hunr : ∀ᶠ j in atTop, FiniteUnramified (Fs j) (Ks j))
    (hι : ∀ᶠ j in atTop, ι j ≠ 1)
    (hb : ∀ᶠ j in atTop, 0 < nrRealPlaces (Fs j))
    (hQ : ∀ᶠ j in atTop, ∀ s,
      (Ideal.absNorm ((D j).prime (s, false)).asIdeal : ℝ) = residueCard (v j s))
    (hmultiplicity : ∀ᶠ j in atTop, ∀ a,
      (Fintype.card {s // v j s = a}:ℝ)*((ramification a:ℝ)*residueDegree a) = Module.finrank ℚ (Fs j))
    (hpair : (1379635324335:ℝ)/10^12 ≤ JPair)
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Fs j)) ≤ logRD)
    (hr : ∀ᶠ j in atTop, ∃ r : Fs j, r^2 = 7)
    (hi : ∀ᶠ j in atTop, ∃ i : Ks j, i^2 = -1)
    (hfinite : Real.log (dedekindZeta ArithmeticRetained.RetainedField ((1+(1/12000:ℝ):ℝ):ℂ)).re /
        (524288 : ℝ) + (1/12000:ℝ)*
          ((logRD-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4-
            (logDeriv (dedekindZeta ArithmeticRetained.RetainedField) 2).re/(524288 : ℝ)) < ceiling)
    (hsignature : ∀ᶠ j in atTop, thetaMin ≤ signatureRatio (Fs j)) : Target := by
  apply target_of_witnessFields_quadratic_fixedBase ArithmeticRetained.RetainedField Fs Ks Ss
    ι D v hdegree hunr hι hb hQ hmultiplicity hpair hdisc hr hi _ hsignature
  simpa only [ArithmeticRetained.retainedField_degree, Nat.cast_ofNat] using hfinite

end UnitDistance.SIntegerCRT
