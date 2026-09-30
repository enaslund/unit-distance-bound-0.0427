module

public import UnitDistance.SIntegerWitnessAnalytic
public import UnitDistance.ImaginaryQuadraticContinuation

@[expose] public section
set_option backward.privateInPublic true


/-! The planar target from actual quadratic arithmetic families containing
roots of seven and minus one. Relative analytic continuation is proved by the
signed theta construction and actual prime Euler products. -/

noncomputable section
open Filter NumberField NumberField.InfinitePlace
open scoped Classical
namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeUnits NumberFieldAnalysis Witness

variable (M : Type*) [Field M] [NumberField M]
  (Fs Ks : ℕ → Type) (Ss : ℕ → Type*)
  [∀ j, Field (Fs j)] [∀ j, Field (Ks j)]
  [∀ j, NumberField (Fs j)] [∀ j, NumberField (Ks j)]
  [∀ j, Algebra (Fs j) (Ks j)] [∀ j, Algebra M (Ks j)]
  [∀ j, Algebra.IsQuadraticExtension (Fs j) (Ks j)]
  [∀ j, IsTotallyComplex (Ks j)] [∀ j, Fintype (Ss j)]

/-- The planar sequence target with actual arithmetic family hypotheses and
only the pair-integral and one fixed-field scalar numerical inequalities.
The signed theta argument supplies the entire relative factor. -/
theorem target_of_witnessFields_quadratic_fixedBase
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
    (hfinite : Real.log (dedekindZeta M ((1+(1/12000:ℝ):ℝ):ℂ)).re /
        (Module.finrank ℚ M : ℝ) + (1/12000:ℝ)*
          ((logRD-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4-
            (logDeriv (dedekindZeta M) 2).re/(Module.finrank ℚ M : ℝ)) < ceiling)
    (hsignature : ∀ᶠ j in atTop, thetaMin ≤ signatureRatio (Fs j)) : Target := by
  have hentire : ∀ᶠ j in atTop, ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ s : ℂ, 1 < s.re → completedZetaRight (Ks j) s = completedZetaRight (Fs j) s*L s := by
    filter_upwards [hunr, hb, hr, hi] with j hu hb hr hi
    obtain ⟨r, hr⟩ := hr
    obtain ⟨i, hi⟩ := hi
    obtain ⟨L, hL, hfactor⟩ := exists_entire_relative_factor_of_imaginary_quadratic
      (Fs j) (Ks j) r hr hb i hi
      (Algebra.IsQuadraticExtension.finrank_eq_two (Fs j) (Ks j)) hu
    exact ⟨L, hL, fun s hs => rightHalfPlaneFactor_of_entireFactor (Fs j) (Ks j) hfactor hs⟩
  exact target_of_witnessFields_entire_fixedBase M Fs Ks Ss ι D v
    hdegree hunr hι hb hQ hmultiplicity hpair hdisc hentire hfinite hsignature

end UnitDistance.SIntegerCRT
