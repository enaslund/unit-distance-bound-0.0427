module

public import UnitDistance.EuclideanIdealSeparation
public import UnitDistance.LatticePacking

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual dual ideal lattice packing in the sum of complex-coordinate norms

The auxiliary norm is the ordinary L1 sum of the complex norms. The linear
coordinate equivalence preserves all points and their differences; it is used
for packing, without changing the Euclidean metric of the unit-distance target.
-/
noncomputable section
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace DedekindZeta
open scoped nonZeroDivisors Classical
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

abbrev SumNormSpace := PiLp 1 (fun _ : {w : InfinitePlace K // w.IsComplex} => ℂ)

/-- Delete the empty real-place block, and put the sum norm on the complex coordinates. -/
def sumNormCoordinates : Space K ≃L[ℝ] SumNormSpace K := by
  letI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩
  exact ((coordinates K).toLinearEquiv.trans
    (LinearEquiv.uniqueProd (R := ℝ) (M := {w : InfinitePlace K // w.IsComplex} → ℂ)) |>.trans
      (WithLp.linearEquiv 1 ℝ ({w : InfinitePlace K // w.IsComplex} → ℂ)).symm).toContinuousLinearEquiv

@[simp] theorem sumNormCoordinates_apply (y : Space K) (w : {w : InfinitePlace K // w.IsComplex}) :
    sumNormCoordinates K y w = (coordinates K y).2 w := rfl

theorem norm_sumNormCoordinates (y : Space K) :
    ‖sumNormCoordinates K y‖ = coordinateNorm K y := by
  rw [PiLp.norm_eq_of_L1]
  rfl

theorem finrank_sumNormSpace : Module.finrank ℝ (SumNormSpace K) = 2*nrComplexPlaces K := by
  rw [← (sumNormCoordinates K).toLinearEquiv.finrank_eq,
    mixedEmbedding.euclidean.finrank, IsTotallyComplex.finrank K]

/-- Every finite collection of actual dual points in the `j`th bounding ball
satisfies the paper's exact shell count. Neither separation nor a point-count
estimate is an input; separation is derived from the codifferent. -/
theorem dual_shell_card_le_five (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (s : Finset (Space K)) (hs : ∀ y ∈ s, y ∈ PoissonSummation.dualLattice (lattice K I))
    (j : ℕ) (hj : 1 ≤ j)
    (hbound : ∀ y ∈ s, coordinateNorm K y ≤
      (j+1)*((nrComplexPlaces K : ℝ)*dualScale K I)) :
    (s.card : ℝ) ≤ (5:ℝ)^((2*nrComplexPlaces K)*j) := by
  let f := sumNormCoordinates K
  let t := s.image f
  have hR : 0 < (nrComplexPlaces K : ℝ)*dualScale K I :=
    mul_pos (by exact_mod_cast complex_places_pos K) (dualScale_pos K I)
  have ht : ∀ c ∈ t, ‖c‖ ≤ (j+1)*((nrComplexPlaces K : ℝ)*dualScale K I) := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
    rw [norm_sumNormCoordinates]
    exact hbound y hy
  have hsep : ∀ c ∈ t, ∀ d ∈ t, c ≠ d →
      (nrComplexPlaces K : ℝ)*dualScale K I ≤ ‖c-d‖ := by
    intro c hc d hd hcd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hd
    rw [← map_sub, norm_sumNormCoordinates]
    apply dual_lattice_coordinateNorm_minimum K I (x-y)
    · exact (PoissonSummation.dualLattice (lattice K I)).sub_mem (hs x hx) (hs y hy)
    · intro h
      exact hcd (congrArg f (sub_eq_zero.mp h))
  have hh := Packing.card_shell_le_five t hR j hj ht hsep
  have hcard : t.card = s.card := Finset.card_image_of_injective _ f.injective
  rwa [hcard, finrank_sumNormSpace K] at hh

end UnitDistance.EuclideanIdeal
