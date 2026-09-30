module

public import UnitDistance.DeformedIdealExponentialSum
public import UnitDistance.LatticeGaussianPoisson
public import UnitDistance.PackingCoefficient

@[expose] public section
set_option backward.privateInPublic true


/-!
# Uniform Poisson bounds on actual reciprocally deformed ideal lattices

The original profile's exponential Fourier envelope is the analytic input.
The actual ideal-dual separation, all deformations, exponential summability,
Gaussian approximation and the strict-tail passage are proved here.
-/
noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory Filter
open scoped nonZeroDivisors Classical FourierTransform
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- The sum of ordinary complex-coordinate norms as an actual seminorm. -/
def coordinateSeminorm : Seminorm ℝ (Space K) :=
  (normSeminorm ℝ (SumNormSpace K)).comp (sumNormCoordinates K).toLinearMap

@[simp] theorem coordinateSeminorm_apply (x : Space K) :
    coordinateSeminorm K x = coordinateNorm K x := norm_sumNormCoordinates K x

theorem coordinateSeminorm_le (x : Space K) :
    coordinateSeminorm K x ≤ ‖(sumNormCoordinates K).toContinuousLinearMap‖*‖x‖ :=
  (sumNormCoordinates K).toContinuousLinearMap.le_opNorm x

/-- The fixed sufficient inequality proves strict smallness of the actual
normalized exponential dual sum, uniformly over the full deformation space. -/
theorem deformed_dual_normalized_exponential_sum_lt
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : ComplexPlace K → ℝ)
    (hh : ∑ w, h w = 0) {A M σ : ℝ} (hA : 0 < A) (hM : 1 ≤ M) (hσ : 0 ≤ σ)
    (hgap : Real.log M+2*Real.log 5+2 ≤ σ*dualScale K I) :
    Summable (fun w : NonzeroDeformedDual K I h =>
      Real.exp (-σ*coordinateNorm K (w.1 : Space K))) ∧
    (A*M^nrComplexPlaces K)*
      (∑' w : NonzeroDeformedDual K I h, Real.exp (-σ*coordinateNorm K (w.1 : Space K))) < A := by
  have hc : dualPackingRatio K I σ < 1 ∧
      M^nrComplexPlaces K*dualPackingRatio K I σ/(1-dualPackingRatio K I σ) < 1 := by
    simpa only [dualPackingRatio, Packing.coefficientRatio] using
      Packing.coefficientRatio_bounds (nrComplexPlaces K) (complex_places_pos K)
        M (dualScale K I) σ hM hgap
  have hs := deformed_dual_exponential_summable_and_le K I h hh hσ hc.1
  refine ⟨hs.1, ?_⟩
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  calc
    _ ≤ (A*M^nrComplexPlaces K)*(dualPackingRatio K I σ/(1-dualPackingRatio K I σ)) :=
      mul_le_mul_of_nonneg_left hs.2 (by positivity)
    _ = A*(M^nrComplexPlaces K*dualPackingRatio K I σ/(1-dualPackingRatio K I σ)) := by ring
    _ < A*1 := mul_lt_mul_of_pos_left hc.2 hA
    _ = A := mul_one _

/-- Every translated finite sum of an actual ideal lattice after any
reciprocal deformation has the paper's factor-two mass/covolume bound.
No actual Fourier-tail or approximation hypothesis is retained. -/
theorem translated_deformed_ideal_sum_le_of_envelope
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : ComplexPlace K → ℝ)
    (hh : ∑ w, h w = 0) {f : Space K → ℝ}
    (hf : f.HasTemperateGrowth) (hpos : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    (hA : 0 < ∫ x, f x) {M σ : ℝ} (hM : 1 ≤ M) (hσ : 0 ≤ σ)
    (hgap : Real.log M+2*Real.log 5+2 ≤ σ*dualScale K I)
    (hFourier : ∀ ξ : Space K, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ≤
      ((∫ x, f x)*M^nrComplexPlaces K)*Real.exp (-σ*coordinateNorm K ξ))
    (r : Space K) (points : Finset (deformedLattice K I h)) :
    ∑ v ∈ points, f (r+(v:Space K)) ≤
      2*(∫ x, f x) / ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        (2⁻¹)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  have hs := deformed_dual_normalized_exponential_sum_lt K I h hh hA hM hσ hgap
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hb := translated_gaussian_limit_sum_le_of_envelope (deformedLattice K I h)
    (coordinateSeminorm K) (coordinateSeminorm_le K) hf hpos hfi
    (by positivity : 0 ≤ (∫ x, f x)*M^nrComplexPlaces K) hσ
    (by simpa only [coordinateSeminorm_apply] using hFourier)
    (by simpa only [coordinateSeminorm_apply] using hs.1)
    (by simpa only [coordinateSeminorm_apply] using hs.2) r points
  rwa [covolume_deformedLattice K I h hh, covolume_lattice K I] at hb

end UnitDistance.EuclideanIdeal
