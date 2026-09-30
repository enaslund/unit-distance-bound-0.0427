module

public import UnitDistance.SIntegerWitnessProfile
public import UnitDistance.SIntegerProfileBound
public import UnitDistance.RelativeFieldEnergy
public import UnitDistance.GeometryEnergy

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual common S-integer witness window

The energy is the sum of the actual field archimedean energy and the negative
logarithm of the literal finite shell profile. Its supported sublevel set is
compact. The original Poisson estimate gives a uniform vertex bound for every
translate and archimedean deformation, including every signed reference shift.
-/

noncomputable section
open Set MeasureTheory NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

local instance windowLocalMeasurableSpace (P : S × Bool → HeightOneSpectrum (𝓞 K)) (t : S × Bool) :
    MeasurableSpace ((P t).adicCompletion K) := borel ((P t).adicCompletion K)
local instance windowLocalBorelSpace (P : S × Bool → HeightOneSpectrum (𝓞 K)) (t : S × Bool) :
    BorelSpace ((P t).adicCompletion K) := ⟨rfl⟩

theorem witnessLocalFactor_locallyConstant (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (t : S × Bool) : IsLocallyConstant (witnessLocalFactor D v n₀ t) :=
  Local.BallSystem.shellFactor_locallyConstant _ (Local.ValuedHaar.ball_clopen _) _ _ _

theorem witnessFiniteProfile_locallyConstant (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) : IsLocallyConstant (witnessFiniteProfile D v n₀) := by
  unfold witnessFiniteProfile
  generalize (Finset.univ : Finset (S × Bool)) = I
  induction I using Finset.induction_on with
  | empty =>
    apply IsLocallyConstant.of_constant
    intro x y
    simp
  | @insert t I ht ih =>
    simp only [Finset.prod_insert ht]
    exact ((witnessLocalFactor_locallyConstant D v n₀ t).comp_continuous (continuous_apply t)).mul ih

/-- The finite energy is interpreted only on the profile support. -/
def witnessFiniteEnergy (D : PrimePairFamily ι S) (v : S → Fin 11) (n₀ : S → ℤ)
    (x : LocalProduct D.prime) : ℝ := -Real.log (witnessFiniteProfile D v n₀ x)

/-- A literal finite sum of the fixed coefficient log bounds. -/
def witnessFiniteEnergyBound (v : S → Fin 11) : ℝ :=
  ∑ t : S × Bool, ∑ i ∈ Finset.range 6, |Real.log (Witness.shellWeightNat (v t.1) i)|

theorem witnessFiniteEnergy_continuous (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) : Continuous (witnessFiniteEnergy D v n₀) :=
  ((witnessFiniteProfile_locallyConstant D v n₀).comp (fun r => -Real.log r)).continuous

theorem witnessFiniteEnergy_norm_le (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (x : LocalProduct D.prime) :
    ‖witnessFiniteEnergy D v n₀ x‖ ≤ witnessFiniteEnergyBound v := by
  by_cases hx : witnessFiniteProfile D v n₀ x = 0
  · simp only [witnessFiniteEnergy, hx, Real.log_zero, neg_zero, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  · have hn : ∀ t ∈ (Finset.univ : Finset (S × Bool)), witnessLocalFactor D v n₀ t (x t) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hx
    rw [witnessFiniteEnergy, witnessFiniteProfile, norm_neg, Real.log_prod hn]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _ =>
      Local.BallSystem.shellFactor_log_norm_le _ _ _ _ (x t)))

theorem witnessFiniteEnergy_weight (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) {x : LocalProduct D.prime}
    (hx : x ∈ Function.support (witnessFiniteProfile D v n₀)) :
    Real.exp (-Witness.p*witnessFiniteEnergy D v n₀ x) = witnessFiniteWeight D v n₀ x := by
  rw [witnessFiniteWeight_eq_rpow, witnessFiniteEnergy,
    Real.rpow_def_of_pos (lt_of_le_of_ne (witnessFiniteProfile_nonneg D v n₀ x) (Ne.symm hx))]
  congr 1
  ring

theorem witnessFiniteProfile_support_compact (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) : IsCompact (Function.support (witnessFiniteProfile D v n₀)) := by
  let a : S × Bool → ℤ := fun t => -(witnessRadius v n₀ t + ((Finset.range 6).sup id : ℕ))
  apply (finitePeriod_compact D.prime a).of_isClosed_subset
    ((witnessFiniteProfile_locallyConstant D v n₀).isClopen_fiber 0).isOpen.isClosed_compl
  intro x hx t
  have hn : witnessLocalFactor D v n₀ t (x t) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hx t (Finset.mem_univ t)
  have hb := Local.BallSystem.shellFactor_support
    (Local.ValuedHaar.ballSystem ((D.prime t).adicCompletion K))
    (witnessRadius v n₀ t) (Finset.range 6) (Witness.shellWeightNat (v t.1)) hn
  change Valued.v (x t) ≤ WithZero.exp (-a t)
  change Local.ValuedHaar.intValuation ((D.prime t).adicCompletion K) (x t) ≤
    WithZero.exp (witnessRadius v n₀ t + ((Finset.range 6).sup id : ℕ)) at hb
  rw [canonical_intValuation_eq] at hb
  simpa only [a, neg_neg] using hb

variable [IsTotallyComplex K]

/-- Literal mixed archimedean and finite-place energy. -/
def witnessSAdicEnergy (hι : ι ≠ 1) (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (x : EuclideanIdeal.Space K × LocalProduct D.prime) : ℝ :=
  relativeEnergy ι hι x.1 + witnessFiniteEnergy D v n₀ x.2

def witnessSAdicSupport (D : PrimePairFamily ι S) (v : S → Fin 11) (n₀ : S → ℤ) :
    Set (EuclideanIdeal.Space K × LocalProduct D.prime) :=
  Set.univ ×ˢ Function.support (witnessFiniteProfile D v n₀)

def witnessSAdicWindow (hι : ι ≠ 1) (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (T : ℝ) : Set (EuclideanIdeal.Space K × LocalProduct D.prime) :=
  supportedWindow (witnessSAdicSupport D v n₀) (witnessSAdicEnergy hι D v n₀) T

theorem witnessSAdicEnergy_continuous (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11) (n₀ : S → ℤ) : Continuous (witnessSAdicEnergy hι D v n₀) :=
  ((continuous_relativeEnergy ι hι).comp continuous_fst).add
    ((witnessFiniteEnergy_continuous D v n₀).comp continuous_snd)

theorem witnessSAdicEnergy_weight (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11) (n₀ : S → ℤ) {x : EuclideanIdeal.Space K × LocalProduct D.prime}
    (hx : x ∈ witnessSAdicSupport D v n₀) :
    Real.exp (-Witness.p*witnessSAdicEnergy hι D v n₀ x) =
      relativeProfile ι hι x.1*witnessFiniteWeight D v n₀ x.2 := by
  rw [witnessSAdicEnergy, mul_add, Real.exp_add, relativeEnergy_weight_p,
    witnessFiniteEnergy_weight D v n₀ hx.2]

theorem witnessSAdicWindow_compact (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11) (n₀ : S → ℤ) (T : ℝ) :
    IsCompact (witnessSAdicWindow hι D v n₀ T) := by
  apply ((isCompact_relativeEnergy_window ι hι (T+witnessFiniteEnergyBound v)).prod
    (witnessFiniteProfile_support_compact D v n₀)).of_isClosed_subset
  · exact (isClosed_univ.prod (witnessFiniteProfile_support_compact D v n₀).isClosed).inter
      (isClosed_le (witnessSAdicEnergy_continuous hι D v n₀) continuous_const)
  · intro x hx
    refine ⟨?_, hx.1.2⟩
    have hb := neg_le_of_abs_le (show |witnessFiniteEnergy D v n₀ x.2| ≤
      witnessFiniteEnergyBound v by simpa only [Real.norm_eq_abs] using witnessFiniteEnergy_norm_le D v n₀ x.2)
    change relativeEnergy ι hι x.1 ≤ T+witnessFiniteEnergyBound v
    have ht : relativeEnergy ι hι x.1 + witnessFiniteEnergy D v n₀ x.2 ≤ T := hx.2
    linarith

theorem witnessSAdicSupport_measurable (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) : MeasurableSet (witnessSAdicSupport D v n₀) :=
  MeasurableSet.univ.prod (measurableSet_support (witnessFiniteProfile_measurable D v n₀))

theorem witnessSAdic_indicator_exp (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11) (n₀ : S → ℤ) :
    (witnessSAdicSupport D v n₀).indicator
      (fun x => Real.exp (-Witness.p*witnessSAdicEnergy hι D v n₀ x)) =
      fun x => relativeProfile ι hι x.1*witnessFiniteWeight D v n₀ x.2 := by
  funext x
  by_cases hx : x ∈ witnessSAdicSupport D v n₀
  · rw [Set.indicator_of_mem hx, witnessSAdicEnergy_weight hι D v n₀ hx]
  · rw [Set.indicator_of_notMem hx]
    have hz : witnessFiniteProfile D v n₀ x.2 = 0 := by
      simpa only [witnessSAdicSupport, Set.mem_prod, Set.mem_univ, true_and,
        Function.mem_support, not_not] using hx
    rw [witnessFiniteWeight_eq_rpow, hz, Real.zero_rpow Witness.witness_basic.2.2.1.ne', mul_zero]

theorem witnessSAdic_exp_integrable (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11) (n₀ : S → ℤ) :
    Integrable (fun x => Real.exp (-Witness.p*witnessSAdicEnergy hι D v n₀ x))
      ((semiLocalHaar D.prime).restrict (witnessSAdicSupport D v n₀)) := by
  apply (integrable_indicator_iff (witnessSAdicSupport_measurable D v n₀)).mp
  rw [witnessSAdic_indicator_exp]
  exact (integrable_relativeProfile ι hι).mul_prod (witnessFiniteWeight_integrable D v n₀)

/-- The exact p-mass of the literal mixed profile. -/
theorem witnessSAdic_exp_integral (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ) :
    (∫ x in witnessSAdicSupport D v n₀,
      Real.exp (-Witness.p*witnessSAdicEnergy hι D v n₀ x) ∂semiLocalHaar D.prime) =
      (Witness.compactMass^nrRealPlaces F*Witness.pairMass^nrComplexPlaces F)*
        Witness.tensorFiniteMass v := by
  rw [← integral_indicator (witnessSAdicSupport_measurable D v n₀), witnessSAdic_indicator_exp,
    semiLocalHaar, integral_prod_mul, integral_relativeProfile, witnessFiniteWeight_integral D v hQ n₀]

theorem witnessSAdicWindow_volume_finite (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11) (n₀ : S → ℤ) (T : ℝ) :
    semiLocalHaar D.prime (witnessSAdicWindow hι D v n₀ T) ≠ ⊤ :=
  supported_energy_window_finite (semiLocalHaar D.prime) (witnessSAdicSupport D v n₀)
    (witnessSAdicEnergy hι D v n₀) Witness.p T Witness.witness_basic.2.2.1.le
    (witnessSAdicEnergy_continuous hι D v n₀).measurable
    (witnessSAdic_exp_integrable hι D v n₀)

theorem witnessSAdicWindow_volume_bound (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ) (T : ℝ) :
    (semiLocalHaar D.prime).real (witnessSAdicWindow hι D v n₀ T) ≤
      Real.exp (Witness.p*T)*(Witness.compactMass^nrRealPlaces F*Witness.pairMass^nrComplexPlaces F)*
        Witness.tensorFiniteMass v := by
  have hb := supported_energy_window_volume (semiLocalHaar D.prime) (witnessSAdicSupport D v n₀)
    (witnessSAdicEnergy hι D v n₀) Witness.p T Witness.witness_basic.2.2.1.le
    (witnessSAdicEnergy_continuous hι D v n₀).measurable
    (witnessSAdic_exp_integrable hι D v n₀) (witnessSAdicWindow_volume_finite hι D v n₀ T)
  rw [witnessSAdic_exp_integral hι D v hQ n₀] at hb
  exact hb.trans_eq (mul_assoc _ _ _).symm

/-- The uniform S-integer weight bound for the actual finite shell witness. -/
theorem witnessSAdic_weight_sum_le (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ)
    (hgap : Real.log 2+2*Real.log 5+2 ≤
      EuclideanIdeal.dualScale K (periodIdeal D.prime (witnessPeriodExponent v n₀)))
    (h : PairPlaceIndex F → ℝ) (r : EuclideanIdeal.Space K) (t : LocalProduct D.prime)
    (s : Finset ((Set.range D.prime).integer K)) :
    (∑ x ∈ s, relativeProfile ι hι
      (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
        (r+EuclideanIdeal.embedding K x.val)) * witnessFiniteWeight D v n₀ (localEmbedding D.prime x.val+t)) ≤
      2*(Witness.compactMass^nrRealPlaces F*Witness.pairMass^nrComplexPlaces F)*
        Witness.tensorFiniteMass v / ((2⁻¹ : ℝ)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  simpa only [witnessFiniteWeight_integral D v hQ n₀] using
    sInteger_relativeProfile_sum_le ι hι D.prime (primePair_injective D) _ hgap
      (witnessFiniteWeight D v n₀) (witnessFiniteWeight_nonneg D v n₀)
      (witnessFiniteWeight_integrable D v n₀)
      (fun z hz x => witnessFiniteWeight_period D v n₀ hz x) h r t s

/-- The original supported common window gives the uniform vertex count on
every finite subset of actual S-integers and every deformation/translation. -/
theorem witnessSAdic_card_le (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ)
    (hgap : Real.log 2+2*Real.log 5+2 ≤
      EuclideanIdeal.dualScale K (periodIdeal D.prime (witnessPeriodExponent v n₀)))
    (h : PairPlaceIndex F → ℝ) (r : EuclideanIdeal.Space K) (t : LocalProduct D.prime)
    (T : ℝ) (s : Finset ((Set.range D.prime).integer K))
    (hs : ∀ x ∈ s,
      (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
        (r+EuclideanIdeal.embedding K x.val), localEmbedding D.prime x.val+t) ∈
        witnessSAdicWindow hι D v n₀ T) :
    (s.card : ℝ) ≤
      2*(Witness.compactMass^nrRealPlaces F*Witness.pairMass^nrComplexPlaces F)*
        Witness.tensorFiniteMass v*Real.exp (Witness.p*T) /
          ((2⁻¹ : ℝ)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  let location : (Set.range D.prime).integer K → EuclideanIdeal.Space K × LocalProduct D.prime :=
    fun x => (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
      (r+EuclideanIdeal.embedding K x.val), localEmbedding D.prime x.val+t)
  have hc := energy_window_card s (fun x => witnessSAdicEnergy hι D v n₀ (location x))
    Witness.p T Witness.witness_basic.2.2.1.le (fun x hx => (hs x hx).2)
  have he : (∑ x ∈ s, Real.exp (-Witness.p*witnessSAdicEnergy hι D v n₀ (location x))) =
      ∑ x ∈ s, relativeProfile ι hι (location x).1*witnessFiniteWeight D v n₀ (location x).2 := by
    apply Finset.sum_congr rfl
    intro x hx
    exact witnessSAdicEnergy_weight hι D v n₀ (hs x hx).1
  rw [he] at hc
  have hw := mul_le_mul_of_nonneg_left
    (witnessSAdic_weight_sum_le hι D v hQ n₀ hgap h r t s) (Real.exp_pos (Witness.p*T)).le
  exact hc.trans (hw.trans_eq (by ring))

end UnitDistance.SIntegerCRT
