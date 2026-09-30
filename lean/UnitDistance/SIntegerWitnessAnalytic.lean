module

public import UnitDistance.SIntegerWitnessAsymptotics
public import UnitDistance.PrimeDebitLogDerivative
public import UnitDistance.RelativeHeckeRightHalfPlane

@[expose] public section
set_option backward.privateInPublic true


/-! # The exact planar target from arithmetic families and actual entire factors

The growing-family residue estimate is proved through the unconditional
prime budget and inheritance from one specified finite base. The remaining
analytic premise is actual relative entire continuation. Field-family
existence and its prescribed prime/signature data remain explicit.
-/

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

/-- The ordinary planar sequence target, with the residue-family hypothesis
replaced by actual entire relative factors and one fixed-field numerical
inequality. The pair integral is the second finite numerical hypothesis. -/
theorem target_of_witnessFields_entire_fixedBase
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
    (hentire : ∀ᶠ j in atTop, ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ s : ℂ, 1 < s.re → completedZetaRight (Ks j) s = completedZetaRight (Fs j) s*L s)
    (hfinite : Real.log (dedekindZeta M ((1+(1/12000:ℝ):ℝ):ℂ)).re /
        (Module.finrank ℚ M : ℝ) + (1/12000:ℝ)*
          ((logRD-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4-
            (logDeriv (dedekindZeta M) 2).re/(Module.finrank ℚ M : ℝ)) < ceiling)
    (hsignature : ∀ᶠ j in atTop, thetaMin ≤ signatureRatio (Fs j)) : Target := by
  have hquad : ∀ j, Module.finrank (Fs j) (Ks j) = 2 := fun j =>
    Algebra.IsQuadraticExtension.finrank_eq_two (Fs j) (Ks j)
  have hdegreeK : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop := by
    apply tendsto_atTop_mono _ hdegree
    intro j
    have hd := Module.finrank_mul_finrank ℚ (Fs j) (Ks j)
    rw [hquad] at hd
    omega
  have hdiscK : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Ks j)) ≤ logRD := by
    filter_upwards [hunr, hdisc] with j hu hd
    rwa [rootDiscriminant_eq_of_finiteUnramified (Fs j) (Ks j) hu]
  have hcomp : ∀ eta : ℝ, 0 < eta → ∀ᶠ j in atTop,
      relativeCompletedReal (Ks j) (Fs j) logRD 1 ≤
        relativeCompletedReal (Ks j) (Fs j) logRD (1+eta) := by
    intro eta heta
    filter_upwards [hunr, hdisc, hentire] with j hu hd hL
    obtain ⟨L, hL, hfactor⟩ := hL
    exact relativeCompletedReal_monotoneOn_of_unramified_entire_factor
      (Ks j) (Fs j) (hquad j) hu hL hfactor hd
      (by simp) (by change 1 ≤ 1+eta; linarith) (by linarith)
  have hnum : fixedBaseResidueCeiling M logRD (1/12000) < ceiling := by
    rw [fixedBaseResidueCeiling_eq_zeta_logDeriv]
    exact hfinite
  have hresidue := eventual_normalized_log_relativeResidue_lt_witness_of_fixed_base M Ks Fs
    hquad hdegreeK (Eventually.of_forall fun j => IsTotallyComplex.nrRealPlaces_eq_zero (Ks j))
    hdiscK hcomp hnum
  exact target_of_witnessFields Fs Ks Ss ι D v hdegree hunr hι hb hQ hmultiplicity
    hpair hdisc (hresidue.mono fun _ h => h.le) hsignature

end UnitDistance.SIntegerCRT
