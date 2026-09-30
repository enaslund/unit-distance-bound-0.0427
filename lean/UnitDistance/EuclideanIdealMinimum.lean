module

public import UnitDistance.EuclideanFractionalDual
public import UnitDistance.FractionalIdealMinimum

@[expose] public section
set_option backward.privateInPublic true


/-!
# The discriminant product minimum of actual Euclidean dual vectors

The field is totally complex. Each Euclidean dual coordinate is twice the
conjugate of an actual inverse-different ideal element. Its product minimum
follows from the absolute norm minimum and the actual discriminant identity.
-/
noncomputable section
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory DedekindZeta
open scoped nonZeroDivisors Classical
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K]

theorem absNorm_dualIdeal (I : Ideal (𝓞 K)) :
    FractionalIdeal.absNorm (MinkowskiTrace.dualIdeal K I) =
      ((Ideal.absNorm I : ℚ) * (discr K).natAbs)⁻¹ := by
  rw [MinkowskiTrace.dualIdeal, map_inv₀, map_mul,
    FractionalIdeal.coeIdeal_absNorm, MinkowskiTrace.differentFractionalIdeal,
    FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal K]

theorem dualIdeal_norm_minimum (I : Ideal (𝓞 K)) (b : K)
    (hb : b ∈ (MinkowskiTrace.dualIdeal K I : Submodule (𝓞 K) K)) (hb0 : b ≠ 0) :
    (((Ideal.absNorm I : ℝ) * |(discr K : ℝ)|)⁻¹) ≤ |(Algebra.norm ℚ b : ℝ)| := by
  have h := IdealMinimum.absNorm_le_abs_norm K (MinkowskiTrace.dualIdeal K I) b hb hb0
  rw [absNorm_dualIdeal K I] at h
  have hd : ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by simp
  rw [← hd]
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_inv, Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs] using hr

theorem absNorm_dualFractionalIdeal (I : FractionalIdeal (𝓞 K)⁰ K) :
    FractionalIdeal.absNorm (MinkowskiTrace.dualFractionalIdeal K I) =
      (FractionalIdeal.absNorm I * (discr K).natAbs)⁻¹ := by
  rw [MinkowskiTrace.dualFractionalIdeal, map_inv₀, map_mul,
    MinkowskiTrace.differentFractionalIdeal,
    FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal K]

theorem dualFractionalIdeal_norm_minimum (I : FractionalIdeal (𝓞 K)⁰ K) (b : K)
    (hb : b ∈ MinkowskiTrace.dualFractionalIdeal K I) (hb0 : b ≠ 0) :
    (((FractionalIdeal.absNorm I : ℝ) * |(discr K : ℝ)|)⁻¹) ≤ |(Algebra.norm ℚ b : ℝ)| := by
  have h := IdealMinimum.absNorm_le_abs_norm K (MinkowskiTrace.dualFractionalIdeal K I) b hb hb0
  rw [absNorm_dualFractionalIdeal K I] at h
  have hd : ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by simp
  rw [← hd]
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_inv, Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs] using hr

variable [IsTotallyComplex K]

theorem complex_product_sq_eq_abs_norm (b : K) :
    (∏ w : {w : InfinitePlace K // w.IsComplex}, ‖(mixedEmbedding K b).2 w‖)^2 =
      |(Algebra.norm ℚ b : ℝ)| := by
  have h := InfinitePlace.prod_eq_abs_norm b
  simp only [IsTotallyComplex.mult_eq] at h
  rw [Finset.prod_pow, Rat.cast_abs] at h
  rw [← h]
  congr 1
  refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun w => IsTotallyComplex.isComplex w))
    (fun w => ‖(mixedEmbedding K b).2 w‖) (fun w => w b) ?_
  intro w
  exact InfinitePlace.norm_embedding_eq w.1 b

/-- The product minimum in `geo:dual-product`, for an actual fractional ideal
and the ordinary Euclidean dual. The factor `2^d` comes from real trace duality. -/
theorem dual_lattice_product_minimum
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : Space K)
    (hy : y ∈ PoissonSummation.dualLattice (lattice K I)) (hy0 : y ≠ 0) :
    (2 : ℝ)^nrComplexPlaces K /
        Real.sqrt ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          |(discr K : ℝ)|) ≤
      ∏ w : {w : InfinitePlace K // w.IsComplex}, ‖(coordinates K y).2 w‖ := by
  obtain ⟨b, hb, hyb⟩ := (mem_dual_fractional_lattice_iff K I y).mp hy
  have hb0 : b ≠ 0 := by
    intro h
    apply hy0
    apply (coordinates K).injective
    rw [hyb, h, map_zero, map_zero]
    ext w <;> simp [dualCoordinates]
  have hmin := Real.sqrt_le_sqrt (dualFractionalIdeal_norm_minimum K I b hb hb0)
  rw [← complex_product_sq_eq_abs_norm K b,
    Real.sqrt_sq (Finset.prod_nonneg (fun _ _ => norm_nonneg _)), Real.sqrt_inv] at hmin
  have hp : (∏ w : {w : InfinitePlace K // w.IsComplex}, ‖(coordinates K y).2 w‖) =
      (2 : ℝ)^nrComplexPlaces K *
        ∏ w : {w : InfinitePlace K // w.IsComplex}, ‖(mixedEmbedding K b).2 w‖ := by
    rw [hyb]
    simp only [dualCoordinates, norm_mul, Complex.norm_conj, RCLike.norm_two,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [hp, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hmin (by positivity)

end UnitDistance.EuclideanIdeal
