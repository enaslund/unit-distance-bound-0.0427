module

public import UnitDistance.TensorFiniteFunctional
public import UnitDistance.LocalOverlapLaw
public import UnitDistance.TensorProfiles

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual supported finite-place tensor overlap law and moments

All local measures are the actual support-restricted products of valuation
counting measure, unit probability and additive Haar measure. Independence
is proved by factorizing their normalized densities. The common variance
constant depends only on the eleven fixed sets of rational shell weights.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace UnitDistance.Witness

/-- A uniform bound for the magnitude of the logarithmic local shell energy. -/
def finiteShellEnergyBound (v : Fin 11) : ℝ :=
  Local.BallSystem.shellEnergyBound (Finset.range 6 ×ˢ Finset.range 6)
    (fun ij => shellWeightNat v ij.1 * shellWeightNat v ij.2)

/-- One finite constant bounds every local variance, independent of the field. -/
def finiteEnergyVarianceConstant : ℝ := ∑ v : Fin 11, finiteShellEnergyBound v^2

theorem finiteEnergyVarianceConstant_nonneg : 0 ≤ finiteEnergyVarianceConstant :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem finiteShellEnergyBound_sq_le (v : Fin 11) :
    finiteShellEnergyBound v^2 ≤ finiteEnergyVarianceConstant :=
  Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ v)

section Local
variable {G U : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  [MeasurableSpace U] {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
  (v : Fin 11) (B : Local.BallSystem G μ (residueCard v))
  (S : B.ReciprocalSteps U) (ν : Measure U) [IsProbabilityMeasure ν]

/-- The negative logarithm of the literal local witness profile. -/
abbrev localShellEnergy : G × G → ℝ :=
  B.shellEnergy (periodPower v) (Finset.range 6 ×ˢ Finset.range 6)
    (fun ij => shellWeightNat v ij.1 * shellWeightNat v ij.2)

/-- The literal support-restricted local displacement/position measure. -/
abbrev localShellOverlapBase : Measure ((ℤ × U) × (G × G)) :=
  B.shellOverlapBase S ν (periodPower v) (Finset.range 6 ×ˢ Finset.range 6)
    (fun ij => shellWeightNat v ij.1 * shellWeightNat v ij.2)

/-- The normalized actual local overlap law, with its evaluated positive mass. -/
def localShellOverlapLaw : Measure ((ℤ × U) × (G × G)) :=
  overlapLaw (localShellOverlapBase v B S ν)
    (firstEnergy (localShellEnergy v B))
    (secondEnergy (localShellEnergy v B) (fun d => S.step d.1 d.2)) (finiteOverlapMass v)

theorem localShellOverlapLaw_eq (hs : ∀ n, Measurable (S.step n)) :
    localShellOverlapLaw v B S ν =
      B.shellOverlapLaw S ν (periodPower v) (Finset.range 6 ×ˢ Finset.range 6)
        (fun ij => shellWeightNat v ij.1 * shellWeightNat v ij.2) := by
  unfold localShellOverlapLaw Local.BallSystem.shellOverlapLaw
  rw [← localShellProfile_profileEnergy v B S ν hs]
  rfl

omit [μ.IsAddRightInvariant] in
theorem localShellOverlap_exp_integrable (hs : ∀ n, Measurable (S.step n)) :
    Integrable (fun z => Real.exp (-(firstEnergy (localShellEnergy v B) z +
      secondEnergy (localShellEnergy v B) (fun d => S.step d.1 d.2) z)))
      (localShellOverlapBase v B S ν) :=
  B.shellOverlap_exp_integrable S ν (zero_lt_one.trans (residueCard_gt_one v)) hs _ _ _
    (fun ij _ => mul_nonneg (shellWeightNat_nonneg v ij.1) (shellWeightNat_nonneg v ij.2))

theorem localShellOverlap_exp_integral (hs : ∀ n, Measurable (S.step n)) :
    (∫ z, Real.exp (-(firstEnergy (localShellEnergy v B) z +
      secondEnergy (localShellEnergy v B) (fun d => S.step d.1 d.2) z))
      ∂localShellOverlapBase v B S ν) = finiteOverlapMass v := by
  rw [← localShellProfile_profileEnergy v B S ν hs]
  exact B.shellOverlap_exp_integral S ν (zero_lt_one.trans (residueCard_gt_one v)) hs _ _ _
    (fun ij _ => mul_nonneg (shellWeightNat_nonneg v ij.1) (shellWeightNat_nonneg v ij.2))

theorem localShellOverlapLaw_probability (hs : ∀ n, Measurable (S.step n)) :
    IsProbabilityMeasure (localShellOverlapLaw v B S ν) :=
  overlapLaw_probability _ _ _ (finiteOverlapMass_pos v)
    (localShellOverlap_exp_integrable v B S ν hs) (localShellOverlap_exp_integral v B S ν hs)

/-- The actual local first-endpoint mean; no external moment value is supplied. -/
def localShellEnergyMean : ℝ :=
  ∫ z, firstEnergy (localShellEnergy v B) z ∂localShellOverlapLaw v B S ν

theorem localShell_endpoint_moments [MeasurableNeg G] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (hs : ∀ n, Measurable (S.step n)) :
    MemLp (firstEnergy (localShellEnergy v B)) 2 (localShellOverlapLaw v B S ν) ∧
    MemLp (secondEnergy (localShellEnergy v B) (fun d => S.step d.1 d.2)) 2
      (localShellOverlapLaw v B S ν) ∧
    (∫ z, secondEnergy (localShellEnergy v B) (fun d => S.step d.1 d.2) z
      ∂localShellOverlapLaw v B S ν) = localShellEnergyMean v B S ν ∧
    variance (firstEnergy (localShellEnergy v B)) (localShellOverlapLaw v B S ν) ≤
      finiteEnergyVarianceConstant ∧
    variance (secondEnergy (localShellEnergy v B) (fun d => S.step d.1 d.2))
      (localShellOverlapLaw v B S ν) ≤ finiteEnergyVarianceConstant := by
  have hZ : 0 < B.profileEnergy S ν (localShellProfile v B) := by
    rw [localShellProfile_profileEnergy v B S ν hs]
    exact finiteOverlapMass_pos v
  obtain ⟨hX, hY, hm, hvX, hvY⟩ := B.shellOverlapLaw_endpoint_moments S ν
    (zero_lt_one.trans (residueCard_gt_one v)) hs _ _ _
    (fun ij _ => mul_nonneg (shellWeightNat_nonneg v ij.1) (shellWeightNat_nonneg v ij.2)) hZ
  simp only [localShellEnergyMean, localShellOverlapLaw_eq v B S ν hs]
  exact ⟨hX, hY, hm, hvX.trans (finiteShellEnergyBound_sq_le v),
    hvY.trans (finiteShellEnergyBound_sq_le v)⟩

end Local

section Tensor
variable {ι : Type*} [Fintype ι] {G U : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, MeasurableSpace (G i)]
  [∀ i, MeasurableAdd₂ (G i)] [∀ i, MeasurableSpace (U i)]
  (v : ι → Fin 11) (μ : (i : ι) → Measure (G i))
  [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsAddRightInvariant]
  (B : (i : ι) → Local.BallSystem (G i) (μ i) (residueCard (v i)))
  (S : (i : ι) → (B i).ReciprocalSteps (U i))
  (ν : (i : ι) → Measure (U i)) [∀ i, IsProbabilityMeasure (ν i)]

abbrev FiniteEndpointCoordinates (G U : ι → Type*) :=
  (i : ι) → (ℤ × U i) × (G i × G i)

/-- The actual summed first endpoint energy. -/
def tensorFiniteFirstEnergy (z : FiniteEndpointCoordinates G U) : ℝ :=
  ∑ i, firstEnergy (localShellEnergy (v i) (B i)) (z i)

/-- The actual summed second endpoint energy. -/
def tensorFiniteSecondEnergy (z : FiniteEndpointCoordinates G U) : ℝ :=
  ∑ i, secondEnergy (localShellEnergy (v i) (B i)) (fun d => (S i).step d.1 d.2) (z i)

theorem measurable_tensorFiniteFirstEnergy : Measurable (tensorFiniteFirstEnergy v μ B (U := U)) := by
  apply Finset.measurable_sum
  intro i _
  exact ((B i).shellEnergy_measurable _ _ _).comp
    (measurable_snd.comp (measurable_pi_apply i))

theorem measurable_tensorFiniteSecondEnergy (hs : ∀ i n, Measurable ((S i).step n)) :
    Measurable (tensorFiniteSecondEnergy v μ B S) := by
  apply Finset.measurable_sum
  intro i _
  exact ((B i).shellEnergy_measurable _ _ _).comp
    ((measurable_snd.comp (measurable_pi_apply i)).add
      (((B i).reciprocalSteps_measurable (S i) (hs i)).comp
        (measurable_fst.comp (measurable_pi_apply i))))

/-- The actual product of support-restricted local endpoint measures. -/
def tensorFiniteOverlapBase : Measure (FiniteEndpointCoordinates G U) :=
  Measure.pi (fun i => localShellOverlapBase (v i) (B i) (S i) (ν i))

instance localShellOverlapBase_sigmaFinite (i : ι) :
    SigmaFinite (localShellOverlapBase (v i) (B i) (S i) (ν i)) := by
  change SigmaFinite (((Measure.count.prod (ν i)).prod ((μ i).prod (μ i))).restrict _)
  infer_instance

instance tensorFiniteOverlapBase_sigmaFinite : SigmaFinite (tensorFiniteOverlapBase v μ B S ν) := by
  unfold tensorFiniteOverlapBase
  infer_instance

/-- The actual normalized supported tensor density. -/
def tensorFiniteOverlapLaw : Measure (FiniteEndpointCoordinates G U) :=
  overlapLaw (tensorFiniteOverlapBase v μ B S ν)
    (tensorFiniteFirstEnergy v μ B) (tensorFiniteSecondEnergy v μ B S)
    (tensorFiniteOverlapMass v)

theorem tensorFiniteOverlapLaw_eq_product (hs : ∀ i n, Measurable ((S i).step n)) :
    tensorFiniteOverlapLaw v μ B S ν =
      Measure.pi (fun i => localShellOverlapLaw (v i) (B i) (S i) (ν i)) :=
  tensor_overlapLaw _ _ _ _ (fun i => finiteOverlapMass_pos (v i))
    (fun i => localShellOverlap_exp_integrable (v i) (B i) (S i) (ν i) (hs i))

theorem tensorFiniteOverlap_exp_integrable (hs : ∀ i n, Measurable ((S i).step n)) :
    Integrable (fun z => Real.exp (-(tensorFiniteFirstEnergy v μ B z+
      tensorFiniteSecondEnergy v μ B S z))) (tensorFiniteOverlapBase v μ B S ν) :=
  tensor_overlap_integrable _ _ _
    (fun i => localShellOverlap_exp_integrable (v i) (B i) (S i) (ν i) (hs i))

theorem tensorFiniteOverlap_exp_integral (hs : ∀ i n, Measurable ((S i).step n)) :
    (∫ z, Real.exp (-(tensorFiniteFirstEnergy v μ B z+tensorFiniteSecondEnergy v μ B S z))
      ∂tensorFiniteOverlapBase v μ B S ν) = tensorFiniteOverlapMass v := by
  refine (tensor_overlap_integral
    (fun i => localShellOverlapBase (v i) (B i) (S i) (ν i))
    (fun i => firstEnergy (localShellEnergy (v i) (B i)))
    (fun i => secondEnergy (localShellEnergy (v i) (B i)) (fun d => (S i).step d.1 d.2))).trans ?_
  exact Finset.prod_congr rfl (fun i _ =>
    localShellOverlap_exp_integral (v i) (B i) (S i) (ν i) (hs i))

theorem tensorFiniteOverlapLaw_probability (hs : ∀ i n, Measurable ((S i).step n)) :
    IsProbabilityMeasure (tensorFiniteOverlapLaw v μ B S ν) :=
  overlapLaw_probability _ _ _ (tensorFiniteOverlapMass_pos v)
    (tensorFiniteOverlap_exp_integrable v μ B S ν hs)
    (tensorFiniteOverlap_exp_integral v μ B S ν hs)

/-- The actual total mean under the independent supported local laws. -/
def tensorFiniteEnergyMean : ℝ := ∑ i, localShellEnergyMean (v i) (B i) (S i) (ν i)

/-- All actual endpoint moments required for concentration, with a constant
depending only on the fixed witness coefficients. -/
theorem tensorFinite_endpoint_moments
    [∀ i, MeasurableNeg (G i)] [∀ i, (μ i).IsAddLeftInvariant] [∀ i, (μ i).IsNegInvariant]
    (hs : ∀ i n, Measurable ((S i).step n)) :
    MemLp (tensorFiniteFirstEnergy v μ B) 2 (tensorFiniteOverlapLaw v μ B S ν) ∧
    MemLp (tensorFiniteSecondEnergy v μ B S) 2 (tensorFiniteOverlapLaw v μ B S ν) ∧
    (∫ z, tensorFiniteFirstEnergy v μ B z ∂tensorFiniteOverlapLaw v μ B S ν) =
      tensorFiniteEnergyMean v μ B S ν ∧
    (∫ z, tensorFiniteSecondEnergy v μ B S z ∂tensorFiniteOverlapLaw v μ B S ν) =
      tensorFiniteEnergyMean v μ B S ν ∧
    variance (tensorFiniteFirstEnergy v μ B) (tensorFiniteOverlapLaw v μ B S ν) ≤
      (Fintype.card ι : ℝ)*finiteEnergyVarianceConstant ∧
    variance (tensorFiniteSecondEnergy v μ B S) (tensorFiniteOverlapLaw v μ B S ν) ≤
      (Fintype.card ι : ℝ)*finiteEnergyVarianceConstant := by
  have hm (i : ι) := localShell_endpoint_moments (v i) (B i) (S i) (ν i) (hs i)
  exact tensor_overlap_moments
    (fun i => localShellOverlapBase (v i) (B i) (S i) (ν i))
    (fun i => firstEnergy (localShellEnergy (v i) (B i)))
    (fun i => secondEnergy (localShellEnergy (v i) (B i)) (fun d => (S i).step d.1 d.2))
    (fun i => finiteOverlapMass (v i))
    (fun i => localShellEnergyMean (v i) (B i) (S i) (ν i)) finiteEnergyVarianceConstant
    (fun i => finiteOverlapMass_pos (v i))
    (fun i => localShellOverlap_exp_integrable (v i) (B i) (S i) (ν i) (hs i))
    (fun i => localShellOverlap_exp_integral (v i) (B i) (S i) (ν i) (hs i))
    (fun i => (hm i).1) (fun i => (hm i).2.1) (fun _ => rfl)
    (fun i => (hm i).2.2.1) (fun i => (hm i).2.2.2.1) (fun i => (hm i).2.2.2.2)

end Tensor
end UnitDistance.Witness
