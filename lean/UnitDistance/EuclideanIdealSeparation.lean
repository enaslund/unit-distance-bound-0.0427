module

public import UnitDistance.EuclideanIdealMinimum
public import Mathlib.Analysis.MeanInequalities

@[expose] public section
set_option backward.privateInPublic true


/-! The additive coordinate norm minimum from the actual dual product bound. -/
noncomputable section
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace DedekindZeta
open scoped nonZeroDivisors Classical
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem complex_places_pos : 0 < nrComplexPlaces K := by
  have h := Module.finrank_pos (R := ℚ) (M := K)
  rw [IsTotallyComplex.finrank K] at h
  omega

/-- The exact geometric mean of the discriminant product minimum. -/
def dualScale (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  ((2 : ℝ)^nrComplexPlaces K /
    Real.sqrt ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
      |(discr K : ℝ)|)) ^ (1/(nrComplexPlaces K : ℝ))

omit [IsTotallyComplex K] in
theorem dualScale_pos (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : 0 < dualScale K I := by
  have hi : 0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_pos.mpr (IdealMinimum.absNorm_pos K I I.ne_zero)
  have hd : 0 < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  unfold dualScale
  positivity

def coordinateNorm (y : Space K) : ℝ :=
  ∑ w : {w : InfinitePlace K // w.IsComplex}, ‖(coordinates K y).2 w‖

theorem dual_lattice_coordinateNorm_minimum
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : Space K)
    (hy : y ∈ PoissonSummation.dualLattice (lattice K I)) (hy0 : y ≠ 0) :
    (nrComplexPlaces K : ℝ) * dualScale K I ≤ coordinateNorm K y := by
  have hd : 0 < (nrComplexPlaces K : ℝ) := by exact_mod_cast complex_places_pos K
  let z := fun w : {w : InfinitePlace K // w.IsComplex} => ‖(coordinates K y).2 w‖
  have hg := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ => (1/(nrComplexPlaces K : ℝ))) z (by intro _ _; positivity)
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul];
        change (nrComplexPlaces K : ℝ) * (1/(nrComplexPlaces K : ℝ)) = 1
        field_simp) (by intro _ _; exact norm_nonneg _)
  have hp := dual_lattice_product_minimum K I y hy hy0
  have hm := Real.rpow_le_rpow (by positivity) hp (by positivity : 0 ≤ 1/(nrComplexPlaces K : ℝ))
  rw [← Real.finsetProd_rpow Finset.univ z (fun _ _ => norm_nonneg _)
    (1/(nrComplexPlaces K : ℝ))] at hm
  have hh : dualScale K I ≤ (1/(nrComplexPlaces K : ℝ)) * coordinateNorm K y := by
    exact hm.trans (by simpa only [← Finset.mul_sum, coordinateNorm] using hg)
  have hmul := mul_le_mul_of_nonneg_left hh hd.le
  calc
    _ ≤ (nrComplexPlaces K : ℝ) * ((1/(nrComplexPlaces K : ℝ)) * coordinateNorm K y) := hmul
    _ = coordinateNorm K y := by field_simp

end UnitDistance.EuclideanIdeal
