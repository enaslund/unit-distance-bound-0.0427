module

public import UnitDistance.SIntegerWitnessGraph
public import UnitDistance.ArithmeticSequence

@[expose] public section
set_option backward.privateInPublic true


/-! # The exact sequence target from actual arithmetic field families

The finite sets are constructed by the actual weighted S-integer graph
theorem. The concentration dimension threshold follows from degree growth.
Existence of the specified arithmetic family and its eventual residue bound
remain explicit nonnumerical obligations.
-/

noncomputable section
open Filter NumberField NumberField.InfinitePlace
open scoped Classical
namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeUnits NumberFieldAnalysis Witness

variable (Fs Ks : ℕ → Type) (Ss : ℕ → Type*)
  [∀ j, Field (Fs j)] [∀ j, Field (Ks j)]
  [∀ j, NumberField (Fs j)] [∀ j, NumberField (Ks j)]
  [∀ j, Algebra (Fs j) (Ks j)]
  [∀ j, Algebra.IsQuadraticExtension (Fs j) (Ks j)]
  [∀ j, IsTotallyComplex (Ks j)] [∀ j, Fintype (Ss j)]

/-- The manuscript's exact planar sequence theorem from ordinary field,
prime-ideal, discriminant, signature and residue data. No geometric or
concentration hypothesis remains. Only the displayed integral enclosure is
a finite numerical input; the arithmetic family hypotheses still require proofs. -/
theorem target_of_witnessFields
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
    (hresidue : ∀ᶠ j in atTop,
      Real.log (relativeResidue (Ks j) (Fs j))/(Module.finrank ℚ (Fs j):ℝ) ≤ ceiling)
    (hsignature : ∀ᶠ j in atTop, thetaMin ≤ signatureRatio (Fs j)) : Target := by
  have hd : Tendsto (fun j => (Module.finrank ℚ (Fs j):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdegree
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hlarge : ∀ᶠ j in atTop,
      4*mixedEnergyVarianceConstant ≤ epsilon^2*(Module.finrank ℚ (Fs j):ℝ) := by
    filter_upwards [tendsto_atTop.mp hd (4*mixedEnergyVarianceConstant/epsilon^2)] with j hj
    have h := (div_le_iff₀ (sq_pos_of_pos hepsilon)).mp hj
    simpa only [mul_comm] using h
  apply target_of_eventual_exponential_graphs _ hd
    (show (0:ℝ) < (533:ℝ)/10^8 by norm_num)
    (show (0:ℝ) < (2:ℝ)^(3+increment) by positivity)
  filter_upwards [hunr, hι, hb, hQ, hmultiplicity, hdisc, hresidue, hsignature, hlarge]
    with j hu hi hb hq hm hd hr hs hl
  obtain ⟨U, _, hU⟩ := witnessSInteger_uniform_graph hu hi hb (D j) (v j) hq hm
    hpair hd hr hs hl
  exact ⟨U, hU⟩

end UnitDistance.SIntegerCRT
