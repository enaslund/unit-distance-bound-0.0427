module

public import UnitDistance.EuclideanIdealPacking
public import UnitDistance.LatticeExponentialSum

@[expose] public section
set_option backward.privateInPublic true


/-! Actual nonzero dual-lattice exponential sums, with no assumed separation. -/
noncomputable section
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace DedekindZeta
open scoped nonZeroDivisors Classical
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

abbrev NonzeroDual (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  {w : PoissonSummation.dualLattice (lattice K I) // w ≠ 0}

def dualPackingRatio (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σ : ℝ) : ℝ :=
  (5:ℝ)^(2*nrComplexPlaces K) *
    Real.exp (-σ*((nrComplexPlaces K : ℝ)*dualScale K I))

/-- Absolute convergence and an exact geometric bound for the nonzero dual
exponential sum of every actual totally complex fractional ideal lattice. -/
theorem dual_exponential_summable_and_le
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hq : dualPackingRatio K I σ < 1) :
    Summable (fun w : NonzeroDual K I =>
      Real.exp (-σ*coordinateNorm K (w.1 : Space K))) ∧
    (∑' w : NonzeroDual K I, Real.exp (-σ*coordinateNorm K (w.1 : Space K))) ≤
      dualPackingRatio K I σ/(1-dualPackingRatio K I σ) := by
  let f : NonzeroDual K I → SumNormSpace K := fun w => sumNormCoordinates K (w.1 : Space K)
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact (sumNormCoordinates K).injective h
  have hmin : ∀ w : NonzeroDual K I,
      (nrComplexPlaces K : ℝ)*dualScale K I ≤ ‖f w‖ := by
    intro w
    rw [norm_sumNormCoordinates]
    apply dual_lattice_coordinateNorm_minimum K I (w.1 : Space K) w.1.2
    intro h
    exact w.2 (Subtype.ext h)
  have hsep : ∀ x y : NonzeroDual K I, x ≠ y →
      (nrComplexPlaces K : ℝ)*dualScale K I ≤ ‖f x-f y‖ := by
    intro x y hxy
    dsimp only [f]
    rw [← map_sub, norm_sumNormCoordinates]
    apply dual_lattice_coordinateNorm_minimum K I ((x.1 : Space K)-(y.1 : Space K))
    · exact (PoissonSummation.dualLattice (lattice K I)).sub_mem x.1.2 y.1.2
    · intro h
      exact hxy (Subtype.ext (Subtype.ext (sub_eq_zero.mp h)))
  have hR : 0 < (nrComplexPlaces K : ℝ)*dualScale K I :=
    mul_pos (by exact_mod_cast complex_places_pos K) (dualScale_pos K I)
  have hq' : Packing.packingRatio (SumNormSpace K)
      ((nrComplexPlaces K : ℝ)*dualScale K I) σ < 1 := by
    simpa only [Packing.packingRatio, finrank_sumNormSpace, dualPackingRatio] using hq
  have h := Packing.summable_exp_and_tsum_le_of_injective f hinj hR hσ hmin hsep hq'
  simpa only [f, norm_sumNormCoordinates, Packing.packingRatio, finrank_sumNormSpace,
    dualPackingRatio] using h

end UnitDistance.EuclideanIdeal
