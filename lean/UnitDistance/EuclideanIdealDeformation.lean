module

public import UnitDistance.EuclideanIdealPacking
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section
set_option backward.privateInPublic true


/-!
# Reciprocal deformations of the actual ideal lattice

The complex coordinates are multiplied by `exp(h w)`. When their logarithms
sum to zero this preserves ordinary Lebesgue covolume and the complete dual
product minimum. In particular there is no bound on the deformation parameter.
-/
noncomputable section
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors Classical RealInnerProductSpace
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K]

abbrev ComplexPlace := {w : InfinitePlace K // w.IsComplex}

def mixedDeformation (h : ComplexPlace K → ℝ) : mixedSpace K ≃ₗ[ℝ] mixedSpace K where
  toFun x := (x.1, fun w => Real.exp (h w) • x.2 w)
  invFun x := (x.1, fun w => Real.exp (-h w) • x.2 w)
  left_inv x := by
    refine Prod.ext ?_ ?_
    · rfl
    funext w
    change Real.exp (-h w) • (Real.exp (h w) • x.2 w) = x.2 w
    rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  right_inv x := by
    refine Prod.ext ?_ ?_
    · rfl
    funext w
    change Real.exp (h w) • (Real.exp (-h w) • x.2 w) = x.2 w
    rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  map_add' x y := by ext w <;> simp [smul_add]
  map_smul' a x := by
    refine Prod.ext ?_ ?_
    · rfl
    funext w
    change Real.exp (h w) • (a • x.2 w) = a • (Real.exp (h w) • x.2 w)
    exact smul_comm (Real.exp (h w)) a (x.2 w)

/-- The actual positive diagonal deformation in ordinary Euclidean coordinates. -/
def deformation (h : ComplexPlace K → ℝ) : Space K ≃L[ℝ] Space K :=
  ((coordinates K).toLinearEquiv.trans (mixedDeformation K h) |>.trans
    (coordinates K).symm.toLinearEquiv).toContinuousLinearEquiv

@[simp] theorem coordinates_deformation (h : ComplexPlace K → ℝ) (x : Space K) :
    coordinates K (deformation K h x) =
      ((coordinates K x).1, fun w => Real.exp (h w) • (coordinates K x).2 w) := by
  simp [deformation, mixedDeformation]

@[simp] theorem deformation_neg_apply (h : ComplexPlace K → ℝ) (x : Space K) :
    deformation K (-h) (deformation K h x) = x := by
  apply (coordinates K).injective
  rw [coordinates_deformation, coordinates_deformation]
  refine Prod.ext ?_ ?_
  · rfl
  funext w
  change Real.exp (-h w) • (Real.exp (h w) • _) = _
  rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

@[simp] theorem deformation_apply_neg (h : ComplexPlace K → ℝ) (x : Space K) :
    deformation K h (deformation K (-h) x) = x := by
  apply (coordinates K).injective
  rw [coordinates_deformation, coordinates_deformation]
  refine Prod.ext ?_ ?_
  · rfl
  funext w
  change Real.exp (h w) • (Real.exp (-h w) • _) = _
  rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

theorem deformation_selfAdjoint (h : ComplexPlace K → ℝ) (x y : Space K) :
    inner ℝ x (deformation K h y) = inner ℝ (deformation K h x) y := by
  simp only [WithLp.prod_inner_apply, PiLp.inner_apply]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro w _
    change inner ℝ ((coordinates K x).2 w)
      (Real.exp (h w) • (coordinates K y).2 w) =
      inner ℝ (Real.exp (h w) • (coordinates K x).2 w) ((coordinates K y).2 w)
    rw [real_inner_smul_right, real_inner_smul_left]

theorem mixedDeformation_det (h : ComplexPlace K → ℝ) :
    LinearMap.det (mixedDeformation K h).toLinearMap = Real.exp (2*∑ w, h w) := by
  have hm : (mixedDeformation K h).toLinearMap =
      LinearMap.prodMap (LinearMap.id : ({w : InfinitePlace K // w.IsReal} → ℝ) →ₗ[ℝ] _)
        (LinearMap.pi (fun w =>
          ((Real.exp (h w)) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj w))) := by
    ext x w <;> rfl
  rw [hm, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_pi]
  simp only [LinearMap.det_smul, Complex.finrank_real_complex, LinearMap.det_id, mul_one]
  simp_rw [← Real.exp_nat_mul]
  rw [← Real.exp_sum]
  congr 1
  simp [Finset.mul_sum]

theorem deformation_det (h : ComplexPlace K → ℝ) :
    LinearMap.det (deformation K h).toLinearMap = Real.exp (2*∑ w, h w) := by
  have hc := LinearMap.det_conj (mixedDeformation K h).toLinearMap
    (coordinates K).symm.toLinearEquiv
  rw [mixedDeformation_det] at hc
  exact hc

theorem deformation_measurePreserving (h : ComplexPlace K → ℝ) (hh : ∑ w, h w = 0) :
    MeasurePreserving (deformation K h) volume volume := by
  refine ⟨(deformation K h).continuous.measurable, ?_⟩
  have hd : LinearMap.det (deformation K h).toLinearMap = 1 := by
    rw [deformation_det, hh, mul_zero, Real.exp_zero]
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Space K))
    (f := (deformation K h).toLinearMap) (by rw [hd]; exact one_ne_zero)
  simp only [hd, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at hm
  convert hm using 1

/-- The image of the ideal lattice under the stated diagonal deformation. -/
def deformedLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : ComplexPlace K → ℝ) :
    Submodule ℤ (Space K) :=
  ZLattice.comap ℝ (lattice K I) (deformation K (-h)).toLinearMap

instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : ComplexPlace K → ℝ) :
    DiscreteTopology (deformedLattice K I h) := by unfold deformedLattice; infer_instance

instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : ComplexPlace K → ℝ) :
    IsZLattice ℝ (deformedLattice K I h) := by unfold deformedLattice; infer_instance

theorem mem_deformedLattice_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : ComplexPlace K → ℝ) (x : Space K) :
    x ∈ deformedLattice K I h ↔ deformation K (-h) x ∈ lattice K I := Iff.rfl

theorem covolume_deformedLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : ComplexPlace K → ℝ) (hh : ∑ w, h w = 0) :
    ZLattice.covolume (deformedLattice K I h) = ZLattice.covolume (lattice K I) := by
  exact ZLattice.covolume_comap (lattice K I) volume volume
    (deformation_measurePreserving K (-h) (by simpa using congrArg Neg.neg hh))

/-- Reciprocal inversion on the dual, proved from the actual real inner product. -/
theorem mem_dual_deformedLattice_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : ComplexPlace K → ℝ) (y : Space K) :
    y ∈ DedekindZeta.PoissonSummation.dualLattice (deformedLattice K I h) ↔
      deformation K h y ∈ DedekindZeta.PoissonSummation.dualLattice (lattice K I) := by
  simp only [DedekindZeta.PoissonSummation.mem_dualLattice]
  constructor
  · intro hy x hx
    rw [← deformation_selfAdjoint]
    apply hy
    change deformation K (-h) (deformation K h x) ∈ lattice K I
    simpa using hx
  · intro hy x hx
    have hx' : deformation K (-h) x ∈ lattice K I := hx
    have ht := hy (deformation K (-h) x) hx'
    rw [← deformation_selfAdjoint, deformation_apply_neg] at ht
    exact ht

theorem deformation_complex_product (h : ComplexPlace K → ℝ) (hh : ∑ w, h w = 0)
    (y : Space K) :
    (∏ w : ComplexPlace K, ‖(coordinates K (deformation K h y)).2 w‖) =
      ∏ w : ComplexPlace K, ‖(coordinates K y).2 w‖ := by
  simp only [coordinates_deformation, _root_.norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Finset.prod_mul_distrib]
  rw [← Real.exp_sum, hh, Real.exp_zero, one_mul]

variable [IsTotallyComplex K]

/-- The same discriminant product bound for every reciprocal deformation. -/
theorem dual_deformedLattice_product_minimum (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : ComplexPlace K → ℝ) (hh : ∑ w, h w = 0) (y : Space K)
    (hy : y ∈ DedekindZeta.PoissonSummation.dualLattice (deformedLattice K I h))
    (hy0 : y ≠ 0) :
    (2 : ℝ)^nrComplexPlaces K /
        Real.sqrt ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          |(discr K : ℝ)|) ≤ ∏ w : ComplexPlace K, ‖(coordinates K y).2 w‖ := by
  have hp := dual_lattice_product_minimum K I (deformation K h y)
    ((mem_dual_deformedLattice_iff K I h y).mp hy)
    (by intro he; exact hy0 ((deformation K h).injective (he.trans (map_zero _).symm)))
  rwa [deformation_complex_product K h hh] at hp

/-- The arithmetic product bound gives the same additive separation after
every volume-preserving diagonal deformation. -/
theorem dual_deformedLattice_coordinateNorm_minimum
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : ComplexPlace K → ℝ)
    (hh : ∑ w, h w = 0) (y : Space K)
    (hy : y ∈ DedekindZeta.PoissonSummation.dualLattice (deformedLattice K I h))
    (hy0 : y ≠ 0) :
    (nrComplexPlaces K : ℝ)*dualScale K I ≤ coordinateNorm K y := by
  have hd : 0 < (nrComplexPlaces K : ℝ) := by exact_mod_cast complex_places_pos K
  let z := fun w : ComplexPlace K => ‖(coordinates K y).2 w‖
  have hg := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ => (1/(nrComplexPlaces K : ℝ))) z (by intro _ _; positivity)
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change (nrComplexPlaces K : ℝ) * (1/(nrComplexPlaces K : ℝ)) = 1
        field_simp) (by intro _ _; exact norm_nonneg _)
  have hp := dual_deformedLattice_product_minimum K I h hh y hy hy0
  have hm : dualScale K I ≤ (∏ w : ComplexPlace K, z w)^(1/(nrComplexPlaces K : ℝ)) :=
    Real.rpow_le_rpow
      (by positivity : (0:ℝ) ≤ (2:ℝ)^nrComplexPlaces K /
        Real.sqrt ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)*
          |(discr K : ℝ)|)) hp
      (by positivity : 0 ≤ 1/(nrComplexPlaces K : ℝ))
  rw [← Real.finsetProd_rpow Finset.univ z (fun _ _ => norm_nonneg _)
    (1/(nrComplexPlaces K : ℝ))] at hm
  have hx : dualScale K I ≤ (1/(nrComplexPlaces K : ℝ))*coordinateNorm K y := by
    exact hm.trans (by simpa only [← Finset.mul_sum, coordinateNorm] using hg)
  have hmul := mul_le_mul_of_nonneg_left hx hd.le
  calc
    _ ≤ (nrComplexPlaces K : ℝ)*((1/(nrComplexPlaces K : ℝ))*coordinateNorm K y) := hmul
    _ = coordinateNorm K y := by field_simp

end UnitDistance.EuclideanIdeal
