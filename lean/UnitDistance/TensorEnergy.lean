module

public import UnitDistance.TensorFourier
public import UnitDistance.GaussianWindows
public import UnitDistance.StudentWindows
public import UnitDistance.GeometryProductWindows

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual tensor energy and common energy window

The position energy is the literal sum of the published Gaussian and Student
logarithmic energies. Its p-th exponential is the original tensor weight.
The displacement is one in singleton coordinates and `(exp u, exp (-u))`
in every paired block. The actual common sublevel window is compact.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace UnitDistance.Witness

/-- The actual compact-place logarithmic energy. -/
def compactEnergy (z : ℂ) : ℝ := -Real.log (compactProfile z)

theorem compactEnergy_eq (z : ℂ) : compactEnergy z = (2*increment)*‖z‖^2 :=
  compactProfile_energy z

theorem compactEnergy_nonneg (z : ℂ) : 0 ≤ compactEnergy z := compactProfile_energy_nonneg z

theorem continuous_compactEnergy : Continuous compactEnergy := by
  simp only [show compactEnergy = (fun z : ℂ => (2*increment)*‖z‖^2) from funext compactEnergy_eq]
  fun_prop

@[simp] theorem compactEnergy_neg (z : ℂ) : compactEnergy (-z) = compactEnergy z := by
  simp only [compactEnergy_eq, norm_neg]

theorem compactEnergy_weight (q : ℝ) (z : ℂ) :
    Real.exp (-q*compactEnergy z) = compactProfile z^q := by
  have hz : 0 < compactProfile z := Real.exp_pos _
  rw [compactEnergy, Real.rpow_def_of_pos hz]
  congr 1
  ring

/-- The local energies depend only on the actual complex moduli. -/
theorem compactEnergy_eq_of_norm_eq {z w : ℂ} (h : ‖z‖ = ‖w‖) :
    compactEnergy z = compactEnergy w := by
  rw [compactEnergy_eq, compactEnergy_eq, h]

theorem pairEnergy_eq_of_norm_eq {z w : ℂ × ℂ}
    (h₁ : ‖z.1‖ = ‖w.1‖) (h₂ : ‖z.2‖ = ‖w.2‖) : pairEnergy z = pairEnergy w := by
  simp only [pairEnergy, pairProfile, h₁, h₂]

variable {β γ : Type*} [Fintype β] [Fintype γ]

/-- Ordinary tensor volume is sigma finite. Naming the intermediate factors
keeps instance synthesis independent of the nesting depth of product spaces. -/
instance tensorCoordinates_sigmaFinite : SigmaFinite (volume : Measure (TensorCoordinates β γ)) := by
  letI : SigmaFinite (volume : Measure (β → ℂ)) := inferInstance
  letI : SigmaFinite (volume : Measure (γ → ℂ × ℂ)) := inferInstance
  change SigmaFinite ((volume : Measure (β → ℂ)).prod (volume : Measure (γ → ℂ × ℂ)))
  infer_instance

/-- The literal total logarithmic energy on ordinary block coordinates. -/
def tensorPositionEnergy (x : TensorCoordinates β γ) : ℝ :=
  (∑ i, compactEnergy (x.1 i)) + ∑ j, pairEnergy (x.2 j)

/-- The actual normalized displacement specified by the independent pair logs. -/
def tensorStep (u : γ → ℝ) : TensorCoordinates β γ :=
  (fun _ => 1, fun j => reciprocalPairStep (u j))

omit [Fintype β] [Fintype γ] in
theorem continuous_tensorStep : Continuous (tensorStep (β := β) (γ := γ)) := by
  unfold tensorStep reciprocalPairStep
  fun_prop

theorem continuous_tensorPositionEnergy :
    Continuous (tensorPositionEnergy (β := β) (γ := γ)) := by
  unfold tensorPositionEnergy
  exact (continuous_finsetSum _ (fun i _ => continuous_compactEnergy.comp
    ((continuous_apply i).comp continuous_fst))).add
      (continuous_finsetSum _ (fun j _ => continuous_pairEnergy.comp
        ((continuous_apply j).comp continuous_snd)))

@[simp] theorem tensorPositionEnergy_neg (x : TensorCoordinates β γ) :
    tensorPositionEnergy (-x) = tensorPositionEnergy x := by
  simp [tensorPositionEnergy, compactEnergy_neg, pairEnergy_neg]

/-- The exponential of the actual summed energy is the literal product of
local powers, in particular the original Poisson weight at `q = p`. -/
theorem tensorPositionEnergy_weight (q : ℝ) (x : TensorCoordinates β γ) :
    Real.exp (-q*tensorPositionEnergy x) =
      (∏ i, compactProfile (x.1 i)^q) * ∏ j, pairProfile (x.2 j)^q := by
  unfold tensorPositionEnergy
  rw [mul_add, Real.exp_add]
  simp only [Finset.mul_sum, Real.exp_sum, compactEnergy_weight, pairEnergy_weight]

theorem tensorPositionEnergy_weight_p (x : TensorCoordinates β γ) :
    Real.exp (-p*tensorPositionEnergy x) = tensorWeight x := tensorPositionEnergy_weight p x

/-- Coordinate phases do not change the actual tensor energy. -/
theorem tensorPositionEnergy_eq_of_norm_eq {x y : TensorCoordinates β γ}
    (hc : ∀ i, ‖x.1 i‖ = ‖y.1 i‖)
    (hp₁ : ∀ j, ‖(x.2 j).1‖ = ‖(y.2 j).1‖)
    (hp₂ : ∀ j, ‖(x.2 j).2‖ = ‖(y.2 j).2‖) :
    tensorPositionEnergy x = tensorPositionEnergy y := by
  unfold tensorPositionEnergy
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => compactEnergy_eq_of_norm_eq (hc i))
  · exact Finset.sum_congr rfl (fun j _ => pairEnergy_eq_of_norm_eq (hp₁ j) (hp₂ j))

/-- Coordinate phases do not change the original Poisson weight. -/
theorem tensorWeight_eq_of_norm_eq {x y : TensorCoordinates β γ}
    (hc : ∀ i, ‖x.1 i‖ = ‖y.1 i‖)
    (hp₁ : ∀ j, ‖(x.2 j).1‖ = ‖(y.2 j).1‖)
    (hp₂ : ∀ j, ‖(x.2 j).2‖ = ‖(y.2 j).2‖) : tensorWeight x = tensorWeight y := by
  rw [← tensorPositionEnergy_weight_p, ← tensorPositionEnergy_weight_p,
    tensorPositionEnergy_eq_of_norm_eq hc hp₁ hp₂]

theorem integrable_tensorPositionEnergy_weight :
    Integrable (fun x : TensorCoordinates β γ => Real.exp (-p*tensorPositionEnergy x)) := by
  simpa only [tensorPositionEnergy_weight_p] using integrable_tensorWeight (β := β) (γ := γ)

theorem integral_tensorPositionEnergy_weight :
    (∫ x : TensorCoordinates β γ, Real.exp (-p*tensorPositionEnergy x)) =
      compactMass^Fintype.card β * pairMass^Fintype.card γ := by
  simpa only [tensorPositionEnergy_weight_p] using integral_tensorWeight (β := β) (γ := γ)

theorem compactEnergy_sum_nonneg (x : β → ℂ) : 0 ≤ ∑ i, compactEnergy (x i) :=
  Finset.sum_nonneg (fun _ _ => compactEnergy_nonneg _)

theorem pairEnergy_sum_lower (x : γ → ℂ × ℂ) :
    -(Fintype.card γ : ℝ)*Real.log 14 ≤ ∑ j, pairEnergy (x j) := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_neg, neg_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => pairEnergy_lower (x j))

theorem tensorPositionEnergy_lower (x : TensorCoordinates β γ) :
    -(Fintype.card γ : ℝ)*Real.log 14 ≤ tensorPositionEnergy x := by
  unfold tensorPositionEnergy
  linarith [compactEnergy_sum_nonneg x.1, pairEnergy_sum_lower x.2]

/-- Compactness concerns the actual common sublevel set of the summed energy.
The product windows occur only as a containing compact set. -/
theorem isCompact_tensorPositionEnergy_window (T : ℝ) :
    IsCompact (energyWindow (tensorPositionEnergy (β := β) (γ := γ)) T) := by
  have hc : IsCompact (energyWindow (fun x : β → ℂ => ∑ i, compactEnergy (x i))
      (T+(Fintype.card γ:ℝ)*Real.log 14)) :=
    isCompact_sum_energyWindow (fun _ : β => compactEnergy) (fun _ => continuous_compactEnergy)
      (fun _ => 0) (fun _ z => compactEnergy_nonneg z)
      (fun _ t => isCompact_compactProfile_energyWindow t) _
  have hp : IsCompact (energyWindow (fun x : γ → ℂ × ℂ => ∑ j, pairEnergy (x j)) T) :=
    isCompact_sum_energyWindow (fun _ : γ => pairEnergy) (fun _ => continuous_pairEnergy)
      (fun _ => -Real.log 14) (fun _ z => pairEnergy_lower z)
      (fun _ t => isCompact_pair_energyWindow t) _
  apply (hc.prod hp).of_isClosed_subset
    (isClosed_le continuous_tensorPositionEnergy continuous_const)
  intro x hx
  change tensorPositionEnergy x ≤ T at hx
  change (∑ i, compactEnergy (x.1 i)) ≤ T+(Fintype.card γ:ℝ)*Real.log 14 ∧
    (∑ j, pairEnergy (x.2 j)) ≤ T
  unfold tensorPositionEnergy at hx
  constructor <;> linarith [compactEnergy_sum_nonneg x.1, pairEnergy_sum_lower x.2]

end UnitDistance.Witness
