module

public import UnitDistance.EuclideanIdealDeformation
public import UnitDistance.EuclideanIdealExponentialSum

@[expose] public section
set_option backward.privateInPublic true


/-! Uniform exponential sums on the duals of actual deformed ideal lattices. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindZeta
open scoped nonZeroDivisors Classical
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

abbrev NonzeroDeformedDual (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : ComplexPlace K → ℝ) :=
  {w : PoissonSummation.dualLattice (deformedLattice K I h) // w ≠ 0}

/-- The complete sum and its convergence are uniform in the deformation.
Its geometric ratio contains only the actual ideal norm and discriminant. -/
theorem deformed_dual_exponential_summable_and_le
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : ComplexPlace K → ℝ)
    (hh : ∑ w, h w = 0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hq : dualPackingRatio K I σ < 1) :
    Summable (fun w : NonzeroDeformedDual K I h =>
      Real.exp (-σ*coordinateNorm K (w.1 : Space K))) ∧
    (∑' w : NonzeroDeformedDual K I h,
      Real.exp (-σ*coordinateNorm K (w.1 : Space K))) ≤
      dualPackingRatio K I σ/(1-dualPackingRatio K I σ) := by
  let f : NonzeroDeformedDual K I h → SumNormSpace K :=
    fun w => sumNormCoordinates K (w.1 : Space K)
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext ((sumNormCoordinates K).injective hxy))
  have hmin : ∀ w : NonzeroDeformedDual K I h,
      (nrComplexPlaces K : ℝ)*dualScale K I ≤ ‖f w‖ := by
    intro w
    rw [norm_sumNormCoordinates]
    apply dual_deformedLattice_coordinateNorm_minimum K I h hh (w.1 : Space K) w.1.2
    intro hw
    exact w.2 (Subtype.ext hw)
  have hsep : ∀ x y : NonzeroDeformedDual K I h, x ≠ y →
      (nrComplexPlaces K : ℝ)*dualScale K I ≤ ‖f x-f y‖ := by
    intro x y hxy
    dsimp only [f]
    rw [← map_sub, norm_sumNormCoordinates]
    apply dual_deformedLattice_coordinateNorm_minimum K I h hh
      ((x.1 : Space K)-(y.1 : Space K))
    · exact (PoissonSummation.dualLattice (deformedLattice K I h)).sub_mem x.1.2 y.1.2
    · intro hz
      exact hxy (Subtype.ext (Subtype.ext (sub_eq_zero.mp hz)))
  have hR : 0 < (nrComplexPlaces K : ℝ)*dualScale K I :=
    mul_pos (by exact_mod_cast complex_places_pos K) (dualScale_pos K I)
  have hq' : Packing.packingRatio (SumNormSpace K)
      ((nrComplexPlaces K : ℝ)*dualScale K I) σ < 1 := by
    simpa only [Packing.packingRatio, finrank_sumNormSpace, dualPackingRatio] using hq
  have ht := Packing.summable_exp_and_tsum_le_of_injective f hinj hR hσ hmin hsep hq'
  simpa only [f, norm_sumNormCoordinates, Packing.packingRatio, finrank_sumNormSpace,
    dualPackingRatio] using ht

end UnitDistance.EuclideanIdeal
