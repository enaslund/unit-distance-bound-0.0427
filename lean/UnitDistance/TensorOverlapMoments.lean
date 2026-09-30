module

public import UnitDistance.TensorOverlapLaw

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual tensor endpoint means and additive variances

The local normalized Gaussian and Student laws are independent by the proved
ordinary-volume density identity. Their actual energy means and variances
add with the number of singleton and paired blocks. Both endpoint energies
have finite second moments on the actual displacement/position overlap law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace UnitDistance

section TwoGroups

variable {ι κ Ω Ξ : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace Ω] [MeasurableSpace Ξ]
  (μ : ι → Measure Ω) (ν : κ → Measure Ξ)
  [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
  (X : ι → Ω → ℝ) (Y : κ → Ξ → ℝ)
  (hX : ∀ i, MemLp (X i) 2 (μ i)) (hY : ∀ j, MemLp (Y j) 2 (ν j))

include hX hY

theorem tensor_prod_energy_memLp :
    MemLp (fun w : (ι → Ω) × (κ → Ξ) => tensorEnergy X w.1+tensorEnergy Y w.2) 2
      ((Measure.pi μ).prod (Measure.pi ν)) :=
  ((tensorEnergy_memLp μ X hX).comp_fst (Measure.pi ν)).add
    ((tensorEnergy_memLp ν Y hY).comp_snd (Measure.pi μ))

theorem tensor_prod_energy_integral :
    (∫ w : (ι → Ω) × (κ → Ξ), tensorEnergy X w.1+tensorEnergy Y w.2
      ∂(Measure.pi μ).prod (Measure.pi ν)) =
      (∑ i, ∫ x, X i x ∂μ i) + ∑ j, ∫ y, Y j y ∂ν j := by
  have hCX := (tensorEnergy_memLp μ X hX).comp_fst (Measure.pi ν)
  have hPY := (tensorEnergy_memLp ν Y hY).comp_snd (Measure.pi μ)
  rw [integral_add (hCX.integrable (by norm_num)) (hPY.integrable (by norm_num)),
    integral_fun_fst, integral_fun_snd]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [tensorEnergy_integral μ X (fun i => (hX i).integrable (by norm_num)),
    tensorEnergy_integral ν Y (fun j => (hY j).integrable (by norm_num))]

theorem tensor_prod_energy_variance :
    variance (fun w : (ι → Ω) × (κ → Ξ) => tensorEnergy X w.1+tensorEnergy Y w.2)
      ((Measure.pi μ).prod (Measure.pi ν)) =
      (∑ i, variance (X i) (μ i)) + ∑ j, variance (Y j) (ν j) := by
  rw [variance_add_prod (tensorEnergy_memLp μ X hX) (tensorEnergy_memLp ν Y hY),
    tensorEnergy_variance μ X hX, tensorEnergy_variance ν Y hY]

end TwoGroups

namespace Witness

variable {β γ : Type*} [Fintype β] [Fintype γ]

/-- The actual common endpoint mean of the tensor overlap law. -/
def tensorEnergyMean (β γ : Type*) [Fintype β] [Fintype γ] : ℝ :=
  (Fintype.card β:ℝ)*compactEnergyMean+(Fintype.card γ:ℝ)*pairEnergyMean

/-- The exact additive variance, before its dimension-linear enlargement. -/
def tensorEnergyVariance (β γ : Type*) [Fintype β] [Fintype γ] : ℝ :=
  (Fintype.card β:ℝ)*compactEnergyVariance+(Fintype.card γ:ℝ)*pairEnergyVariance

theorem tensor_product_first_memLp :
    MemLp (tensorFirstEnergy (β := β) (γ := γ)) 2 tensorProductOverlapLaw := by
  letI : IsProbabilityMeasure compactOverlapLaw := compactOverlapLaw_probability
  letI : IsProbabilityMeasure pairOverlapLaw := pairOverlapLaw_probability
  exact tensor_prod_energy_memLp (fun _ : β => compactOverlapLaw) (fun _ : γ => pairOverlapLaw)
    (fun _ => compactEnergy) (fun _ => fun w => pairEnergy w.2)
    (fun _ => compact_endpoint_moments.1) (fun _ => pair_endpoint_moments.1)

theorem tensor_product_second_memLp :
    MemLp (tensorSecondEnergy (β := β) (γ := γ)) 2 tensorProductOverlapLaw := by
  letI : IsProbabilityMeasure compactOverlapLaw := compactOverlapLaw_probability
  letI : IsProbabilityMeasure pairOverlapLaw := pairOverlapLaw_probability
  exact tensor_prod_energy_memLp (fun _ : β => compactOverlapLaw) (fun _ : γ => pairOverlapLaw)
    (fun _ z => compactEnergy (z+1)) (fun _ w => pairEnergy (w.2+reciprocalPairStep w.1))
    (fun _ => compact_endpoint_moments.2.1) (fun _ => pair_endpoint_moments.2.1)

theorem tensor_product_first_integral :
    (∫ w : TensorEndpointCoordinates β γ, tensorFirstEnergy w ∂tensorProductOverlapLaw) =
      tensorEnergyMean β γ := by
  letI : IsProbabilityMeasure compactOverlapLaw := compactOverlapLaw_probability
  letI : IsProbabilityMeasure pairOverlapLaw := pairOverlapLaw_probability
  have h := tensor_prod_energy_integral (fun _ : β => compactOverlapLaw) (fun _ : γ => pairOverlapLaw)
    (fun _ => compactEnergy) (fun _ => fun w => pairEnergy w.2)
    (fun _ => compact_endpoint_moments.1) (fun _ => pair_endpoint_moments.1)
  simpa only [tensorFirstEnergy, tensorEnergy, tensorProductOverlapLaw, tensorEnergyMean, compactEnergyMean, pairEnergyMean,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

theorem tensor_product_second_integral :
    (∫ w : TensorEndpointCoordinates β γ, tensorSecondEnergy w ∂tensorProductOverlapLaw) =
      tensorEnergyMean β γ := by
  letI : IsProbabilityMeasure compactOverlapLaw := compactOverlapLaw_probability
  letI : IsProbabilityMeasure pairOverlapLaw := pairOverlapLaw_probability
  have h := tensor_prod_energy_integral (fun _ : β => compactOverlapLaw) (fun _ : γ => pairOverlapLaw)
    (fun _ z => compactEnergy (z+1)) (fun _ w => pairEnergy (w.2+reciprocalPairStep w.1))
    (fun _ => compact_endpoint_moments.2.1) (fun _ => pair_endpoint_moments.2.1)
  simpa only [tensorSecondEnergy, tensorEnergy, tensorProductOverlapLaw, compact_endpoint_moments.2.2.1, pair_endpoint_moments.2.2.1,
    tensorEnergyMean, compactEnergyMean, pairEnergyMean,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

theorem tensor_product_first_variance :
    variance (tensorFirstEnergy (β := β) (γ := γ)) tensorProductOverlapLaw =
      tensorEnergyVariance β γ := by
  change variance (fun w : TensorEndpointCoordinates β γ => tensorFirstEnergy w)
    tensorProductOverlapLaw = _
  letI : IsProbabilityMeasure compactOverlapLaw := compactOverlapLaw_probability
  letI : IsProbabilityMeasure pairOverlapLaw := pairOverlapLaw_probability
  have h := tensor_prod_energy_variance (fun _ : β => compactOverlapLaw) (fun _ : γ => pairOverlapLaw)
    (fun _ => compactEnergy) (fun _ => fun w => pairEnergy w.2)
    (fun _ => compact_endpoint_moments.1) (fun _ => pair_endpoint_moments.1)
  simpa only [tensorFirstEnergy, tensorEnergy, tensorProductOverlapLaw, tensorEnergyVariance, compactEnergyVariance, pairEnergyVariance,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

theorem tensor_product_second_variance :
    variance (tensorSecondEnergy (β := β) (γ := γ)) tensorProductOverlapLaw =
      tensorEnergyVariance β γ := by
  change variance (fun w : TensorEndpointCoordinates β γ => tensorSecondEnergy w)
    tensorProductOverlapLaw = _
  letI : IsProbabilityMeasure compactOverlapLaw := compactOverlapLaw_probability
  letI : IsProbabilityMeasure pairOverlapLaw := pairOverlapLaw_probability
  have h := tensor_prod_energy_variance (fun _ : β => compactOverlapLaw) (fun _ : γ => pairOverlapLaw)
    (fun _ z => compactEnergy (z+1)) (fun _ w => pairEnergy (w.2+reciprocalPairStep w.1))
    (fun _ => compact_endpoint_moments.2.1) (fun _ => pair_endpoint_moments.2.1)
  simpa only [tensorSecondEnergy, tensorEnergy, tensorProductOverlapLaw, compact_endpoint_moments.2.2.2, pair_endpoint_moments.2.2.2,
    tensorEnergyVariance, compactEnergyVariance, pairEnergyVariance,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

/-- Both actual endpoint energies have finite second moments, their common
mean is the sum of local means, and their variances are the exact local sum. -/
theorem tensor_endpoint_moments :
    MemLp (firstEnergy (D := γ → ℝ) (tensorPositionEnergy (β := β) (γ := γ))) 2 (tensorEndpointOverlapLaw (β := β) (γ := γ)) ∧
    MemLp (secondEnergy (tensorPositionEnergy (β := β) (γ := γ)) tensorStep) 2 (tensorEndpointOverlapLaw (β := β) (γ := γ)) ∧
    (∫ w, firstEnergy (tensorPositionEnergy (β := β) (γ := γ)) w ∂tensorEndpointOverlapLaw (β := β) (γ := γ)) = tensorEnergyMean β γ ∧
    (∫ w, secondEnergy (tensorPositionEnergy (β := β) (γ := γ)) tensorStep w ∂tensorEndpointOverlapLaw (β := β) (γ := γ)) =
      tensorEnergyMean β γ ∧
    variance (firstEnergy (tensorPositionEnergy (β := β) (γ := γ))) (tensorEndpointOverlapLaw (β := β) (γ := γ)) = tensorEnergyVariance β γ ∧
    variance (secondEnergy (tensorPositionEnergy (β := β) (γ := γ)) tensorStep) (tensorEndpointOverlapLaw (β := β) (γ := γ)) =
      tensorEnergyVariance β γ := by
  have hm := tensorOverlapCoordinates_preserves_overlapLaw (β := β) (γ := γ)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, tensorFirstEnergy_coordinates] using
      (tensor_product_first_memLp (β := β) (γ := γ)).comp_measurePreserving hm
  · simpa only [Function.comp_def, tensorSecondEnergy_coordinates] using
      (tensor_product_second_memLp (β := β) (γ := γ)).comp_measurePreserving hm
  · have h := hm.integral_comp' tensorFirstEnergy
    simpa only [tensorFirstEnergy_coordinates, tensor_product_first_integral] using h
  · have h := hm.integral_comp' tensorSecondEnergy
    simpa only [tensorSecondEnergy_coordinates, tensor_product_second_integral] using h
  · have h := hm.variance_fun_comp (tensor_product_first_memLp (β := β) (γ := γ)).aemeasurable
    simpa only [tensorFirstEnergy_coordinates, tensor_product_first_variance] using h
  · have h := hm.variance_fun_comp (tensor_product_second_memLp (β := β) (γ := γ)).aemeasurable
    simpa only [tensorSecondEnergy_coordinates, tensor_product_second_variance] using h

/-- One fixed, independently defined local variance constant bounds the
variance in every number of complex coordinates. -/
theorem tensorEnergyVariance_le_dimension :
    tensorEnergyVariance β γ ≤
      tensorEnergyVarianceConstant*(Fintype.card β+2*Fintype.card γ) := by
  have hc := mul_le_mul_of_nonneg_left
    (le_max_left compactEnergyVariance pairEnergyVariance) (Nat.cast_nonneg (α := ℝ) (Fintype.card β))
  have hp := mul_le_mul_of_nonneg_left
    (le_max_right compactEnergyVariance pairEnergyVariance) (Nat.cast_nonneg (α := ℝ) (Fintype.card γ))
  have hC := tensorEnergyVarianceConstant_nonneg
  unfold tensorEnergyVariance tensorEnergyVarianceConstant at *
  nlinarith [mul_nonneg hC (Nat.cast_nonneg (α := ℝ) (Fintype.card γ))]

end Witness
end UnitDistance
