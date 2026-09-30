module

public import UnitDistance.DeformedIdealPoisson

@[expose] public section
set_option backward.privateInPublic true


/-! The same deformed-ideal Poisson estimate on the fixed original lattice.
This is the form used when windows and energies are pulled back by coordinates. -/

noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors Classical FourierTransform
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K]

/-- The actual diagonal map bijects the original and deformed ideal lattices. -/
def latticeDeformation (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : ComplexPlace K → ℝ) :
    lattice K I ≃+ deformedLattice K I h where
  toFun x := ⟨deformation K h x, by
    change deformation K (-h) (deformation K h x) ∈ lattice K I
    rw [deformation_neg_apply]
    exact x.prop⟩
  invFun x := ⟨deformation K (-h) x, x.prop⟩
  left_inv x := Subtype.ext (deformation_neg_apply K h x)
  right_inv x := Subtype.ext (deformation_apply_neg K h x)
  map_add' x y := Subtype.ext ((deformation K h).map_add x y)

@[simp] theorem latticeDeformation_coe (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : ComplexPlace K → ℝ) (x : lattice K I) :
    (latticeDeformation K I h x : Space K) = deformation K h x := rfl

variable [IsTotallyComplex K]

/-- The original ideal lattice with the actual pulled-back energy/profile.
The same bound holds for every translate and every zero-sum deformation. -/
theorem translated_pulledBack_ideal_sum_le_of_envelope
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : ComplexPlace K → ℝ)
    (hh : ∑ w, h w = 0) {f : Space K → ℝ}
    (hf : f.HasTemperateGrowth) (hpos : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    (hA : 0 < ∫ x, f x) {M σ : ℝ} (hM : 1 ≤ M) (hσ : 0 ≤ σ)
    (hgap : Real.log M+2*Real.log 5+2 ≤ σ*dualScale K I)
    (hFourier : ∀ ξ : Space K, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ≤
      ((∫ x, f x)*M^nrComplexPlaces K)*Real.exp (-σ*coordinateNorm K ξ))
    (r : Space K) (points : Finset (lattice K I)) :
    ∑ v ∈ points, f (deformation K h (r+(v:Space K))) ≤
      2*(∫ x, f x) / ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        (2⁻¹)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  have hb := translated_deformed_ideal_sum_le_of_envelope K I h hh hf hpos hfi hA
    hM hσ hgap hFourier (deformation K h r)
    (points.map (latticeDeformation K I h).toEquiv.toEmbedding)
  simp only [Finset.sum_map] at hb
  change (∑ v ∈ points, f (deformation K h r+deformation K h (v:Space K))) ≤ _ at hb
  simpa only [map_add] using hb

end UnitDistance.EuclideanIdeal
