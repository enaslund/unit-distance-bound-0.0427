module

public import UnitDistance.TensorOverlapCoordinates
public import UnitDistance.TensorLocalMoments

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact normalization and independence of the actual tensor overlap

All logarithmic pair displacements and all complex positions carry ordinary
Lebesgue measure. The normalized endpoint law is proved to be the product of
the actual local overlap laws after the explicit regrouping of coordinates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace UnitDistance.Witness

variable {β γ : Type*} [Fintype β] [Fintype γ]

/-- The original product of local overlap integrals. -/
def tensorOverlapMass (β γ : Type*) [Fintype β] [Fintype γ] : ℝ :=
  compactOverlap^Fintype.card β * pairOverlap^Fintype.card γ

theorem tensorOverlapMass_pos : 0 < tensorOverlapMass β γ := by
  unfold tensorOverlapMass
  positivity [compactOverlap_pos, pairOverlap_pos]

/-- The literal product of local overlap densities in grouped coordinates. -/
def tensorOverlapIntegrand (w : TensorEndpointCoordinates β γ) : ℝ :=
  (∏ i, compactProfile (w.1 i)*compactProfile (w.1 i+1)) *
    ∏ j, pairOverlapIntegrand (w.2 j)

theorem tensorOverlapIntegrand_pos (w : TensorEndpointCoordinates β γ) :
    0 < tensorOverlapIntegrand w := by
  apply mul_pos <;> apply Finset.prod_pos <;> intro i _
  · exact mul_pos (Real.exp_pos _) (Real.exp_pos _)
  · exact pairOverlapIntegrand_pos _

theorem tensorOverlapIntegrand_eq_energy (w : TensorEndpointCoordinates β γ) :
    tensorOverlapIntegrand w = Real.exp (-(tensorFirstEnergy w+tensorSecondEnergy w)) := by
  simp only [tensorOverlapIntegrand, ← compactEnergy_overlap_weight, ← pairEnergy_overlap_weight,
    ← Real.exp_sum, ← Real.exp_add, tensorFirstEnergy, tensorSecondEnergy,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  congr 1
  ring

theorem integrable_tensorOverlapIntegrand :
    Integrable (tensorOverlapIntegrand (β := β) (γ := γ)) :=
  (Integrable.fintype_prod (fun _ : β => compactOverlap_integrable)).mul_prod
    (Integrable.fintype_prod (fun _ : γ => integrable_pairOverlapIntegrand))

theorem integral_tensorOverlapIntegrand :
    (∫ w : TensorEndpointCoordinates β γ, tensorOverlapIntegrand w) = tensorOverlapMass β γ := by
  unfold tensorOverlapIntegrand
  rw [Measure.volume_eq_prod,
    integral_prod_mul (μ := volume) (ν := volume)
      (fun x : β → ℂ => ∏ i, compactProfile (x i)*compactProfile (x i+1))
      (fun y : γ → ℝ × (ℂ × ℂ) => ∏ j, pairOverlapIntegrand (y j)),
    integral_fintype_prod_volume_eq_prod
      (fun _ : β => fun z : ℂ => compactProfile z*compactProfile (z+1)),
    integral_fintype_prod_volume_eq_prod (fun _ : γ => pairOverlapIntegrand)]
  simp only [← pairOverlap_eq_integral, compactOverlap, tensorOverlapMass,
    Finset.prod_const, Finset.card_univ]

/-- The actual overlap law in grouped endpoint coordinates. -/
def tensorGroupedOverlapLaw : Measure (TensorEndpointCoordinates β γ) :=
  overlapLaw volume tensorFirstEnergy tensorSecondEnergy (tensorOverlapMass β γ)

/-- The independent product of the actual normalized local overlap laws. -/
def tensorProductOverlapLaw : Measure (TensorEndpointCoordinates β γ) :=
  (Measure.pi (fun _ : β => compactOverlapLaw)).prod
    (Measure.pi (fun _ : γ => pairOverlapLaw))

/-- Fubini and exact normalization prove the full block independence. -/
theorem tensorGroupedOverlapLaw_eq_product :
    tensorGroupedOverlapLaw (β := β) (γ := γ) = tensorProductOverlapLaw := by
  let CX : (β → ℂ) → ℝ := tensorEnergy (fun _ : β => compactEnergy)
  let CY : (β → ℂ) → ℝ := tensorEnergy (fun _ : β => fun z => compactEnergy (z+1))
  let PX : (γ → ℝ × (ℂ × ℂ)) → ℝ := tensorEnergy (fun _ : γ => fun w => pairEnergy w.2)
  let PY : (γ → ℝ × (ℂ × ℂ)) → ℝ :=
    tensorEnergy (fun _ : γ => fun w => pairEnergy (w.2+reciprocalPairStep w.1))
  have hc := continuous_compactEnergy.measurable
  have hp := measurable_pairEnergy
  have hs := measurable_reciprocalPairStep
  have hCX : Measurable CX := by
    change Measurable (fun x : β → ℂ => ∑ i, compactEnergy (x i))
    fun_prop
  have hCY : Measurable CY := by
    change Measurable (fun x : β → ℂ => ∑ i, compactEnergy (x i+1))
    fun_prop
  have hPX : Measurable PX := by
    change Measurable (fun x : γ → ℝ × (ℂ × ℂ) => ∑ j, pairEnergy (x j).2)
    fun_prop
  have hPY : Measurable PY := by
    change Measurable (fun x : γ → ℝ × (ℂ × ℂ) =>
      ∑ j, pairEnergy ((x j).2+reciprocalPairStep (x j).1))
    fun_prop
  have hC := tensor_overlapLaw (fun _ : β => (volume : Measure ℂ))
    (fun _ => compactEnergy) (fun _ z => compactEnergy (z+1)) (fun _ => compactOverlap)
    (fun _ => compactOverlap_pos) (fun _ => integrable_compactEnergy_overlap)
  have hP := tensor_overlapLaw (fun _ : γ => (volume : Measure (ℝ × (ℂ × ℂ))))
    (fun _ w => pairEnergy w.2) (fun _ w => pairEnergy (w.2+reciprocalPairStep w.1))
    (fun _ => pairOverlap) (fun _ => pairOverlap_pos) (fun _ => integrable_pairEnergy_overlap)
  simp only [Finset.prod_const, Finset.card_univ] at hC hP
  change overlapLaw (volume : Measure (β → ℂ)) CX CY (compactOverlap^Fintype.card β) = _ at hC
  change overlapLaw (volume : Measure (γ → ℝ × (ℂ × ℂ))) PX PY
    (pairOverlap^Fintype.card γ) = _ at hP
  change overlapLaw (volume.prod volume) (fun w => CX w.1+PX w.2) (fun w => CY w.1+PY w.2)
      (compactOverlap^Fintype.card β*pairOverlap^Fintype.card γ) = _
  rw [prod_overlapLaw volume volume CX CY PX PY hCX hCY hPX hPY
    (compactOverlap^Fintype.card β) (pairOverlap^Fintype.card γ)
    (pow_pos compactOverlap_pos _) (pow_pos pairOverlap_pos _), hC, hP]
  rfl

theorem tensorGroupedOverlapLaw_probability :
    IsProbabilityMeasure (tensorGroupedOverlapLaw (β := β) (γ := γ)) := by
  rw [tensorGroupedOverlapLaw_eq_product]
  letI : IsProbabilityMeasure compactOverlapLaw := compactOverlapLaw_probability
  letI : IsProbabilityMeasure pairOverlapLaw := pairOverlapLaw_probability
  unfold tensorProductOverlapLaw
  infer_instance

/-- The ordinary joint density over pair logs and all complex positions. -/
def tensorEndpointOverlapIntegrand (w : (γ → ℝ) × TensorCoordinates β γ) : ℝ :=
  Real.exp (-(firstEnergy tensorPositionEnergy w+secondEnergy tensorPositionEnergy tensorStep w))

theorem tensorEndpointOverlapIntegrand_coordinates (w : (γ → ℝ) × TensorCoordinates β γ) :
    tensorEndpointOverlapIntegrand w = tensorOverlapIntegrand (tensorOverlapCoordinates w) := by
  rw [tensorOverlapIntegrand_eq_energy, tensorFirstEnergy_coordinates, tensorSecondEnergy_coordinates]
  rfl

theorem integrable_tensorEndpointOverlapIntegrand :
    Integrable (tensorEndpointOverlapIntegrand (β := β) (γ := γ)) := by
  have h := (tensorOverlapCoordinates_measurePreserving (β := β) (γ := γ)).integrable_comp
    integrable_tensorOverlapIntegrand.aestronglyMeasurable
  simpa only [Function.comp_def, ← tensorEndpointOverlapIntegrand_coordinates] using
    h.mpr integrable_tensorOverlapIntegrand

theorem integral_tensorEndpointOverlapIntegrand :
    (∫ w : (γ → ℝ) × TensorCoordinates β γ, tensorEndpointOverlapIntegrand w) =
      tensorOverlapMass β γ := by
  simp_rw [tensorEndpointOverlapIntegrand_coordinates]
  rw [(tensorOverlapCoordinates_measurePreserving (β := β) (γ := γ)).integral_comp'
    tensorOverlapIntegrand, integral_tensorOverlapIntegrand]

/-- The iterated ordinary position/displacement overlap has exactly the
product of the independently defined Gaussian and Student overlap masses. -/
theorem tensorPositionEnergy_overlap_integral :
    (∫ u : γ → ℝ, ∫ x : TensorCoordinates β γ,
      Real.exp (-(tensorPositionEnergy x+tensorPositionEnergy (x+tensorStep u)))) =
      compactOverlap^Fintype.card β*pairOverlap^Fintype.card γ := by
  change (∫ u : γ → ℝ, ∫ x : TensorCoordinates β γ, tensorEndpointOverlapIntegrand (u,x)) = _
  rw [← integral_prod (μ := (volume : Measure (γ → ℝ)))
    (ν := (volume : Measure (TensorCoordinates β γ)))
    (tensorEndpointOverlapIntegrand (β := β) (γ := γ))
    integrable_tensorEndpointOverlapIntegrand]
  exact integral_tensorEndpointOverlapIntegrand

/-- The actual normalized overlap law on independent pair logs and positions. -/
def tensorEndpointOverlapLaw : Measure ((γ → ℝ) × TensorCoordinates β γ) :=
  overlapLaw volume (firstEnergy tensorPositionEnergy)
    (secondEnergy tensorPositionEnergy tensorStep) (tensorOverlapMass β γ)

theorem tensorEndpointOverlapLaw_probability :
    IsProbabilityMeasure (tensorEndpointOverlapLaw (β := β) (γ := γ)) :=
  overlapLaw_probability volume _ _ tensorOverlapMass_pos
    integrable_tensorEndpointOverlapIntegrand integral_tensorEndpointOverlapIntegrand

/-- The actual normalized endpoint law becomes the actual independent block
law under the concrete coordinate regrouping. -/
theorem tensorOverlapCoordinates_preserves_overlapLaw :
    MeasurePreserving (tensorOverlapCoordinates (β := β) (γ := γ))
      tensorEndpointOverlapLaw tensorProductOverlapLaw := by
  rw [← tensorGroupedOverlapLaw_eq_product]
  have h := overlapLaw_measurePreserving_coordinates
    (volume : Measure ((γ → ℝ) × TensorCoordinates β γ))
    (volume : Measure (TensorEndpointCoordinates β γ))
    (tensorOverlapCoordinates (β := β) (γ := γ))
    tensorOverlapCoordinates_measurePreserving tensorFirstEnergy tensorSecondEnergy (tensorOverlapMass β γ)
  simpa only [tensorEndpointOverlapLaw, tensorGroupedOverlapLaw,
    tensorFirstEnergy_coordinates, tensorSecondEnergy_coordinates] using h

end UnitDistance.Witness
