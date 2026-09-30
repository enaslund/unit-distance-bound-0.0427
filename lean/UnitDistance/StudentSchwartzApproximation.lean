module

public import UnitDistance.StudentSchwartzGaussian
public import UnitDistance.ProfilePoisson
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Gaussian Schwartz approximation of the published Student weight

The functions are the actual weight multiplied by `exp(-‖x‖²/(n+1))`.
Nonnegativity, pointwise convergence, integrability and integral convergence
are proved. The Poisson consequence retains only bounds for the independently
defined Fourier tails of these explicit approximants.
-/

open MeasureTheory Filter
open scoped Topology ContDiff

namespace UnitDistance

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Gaussian regularization of a real temperate multiplier. Its formula is
proved below whenever the multiplier has temperate growth. -/
noncomputable def gaussianRegularization (f : V → ℝ) (n : ℕ) : SchwartzMap V ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    (SchwartzMap.smulLeftCLM ℝ f (gaussianSchwartz (1/((n:ℝ)+1)) (by positivity)))

theorem gaussianRegularization_apply {f : V → ℝ} (hf : f.HasTemperateGrowth)
    (n : ℕ) (x : V) :
    gaussianRegularization f n x = (f x * Real.exp (-(1/((n:ℝ)+1))*‖x‖^2) : ℝ) := by
  simp only [gaussianRegularization, SchwartzMap.postcompCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply hf, gaussianSchwartz_apply, smul_eq_mul,
    Complex.ofRealCLM_apply]

theorem gaussianRegularization_nonneg {f : V → ℝ} (hf : f.HasTemperateGrowth)
    (hpos : ∀ x, 0 ≤ f x) (n : ℕ) (x : V) :
    0 ≤ (gaussianRegularization f n x).re := by
  rw [gaussianRegularization_apply hf, Complex.ofReal_re]
  exact mul_nonneg (hpos x) (Real.exp_pos _).le

theorem gaussianRegularization_le {f : V → ℝ} (hf : f.HasTemperateGrowth)
    (hpos : ∀ x, 0 ≤ f x) (n : ℕ) (x : V) :
    (gaussianRegularization f n x).re ≤ f x := by
  rw [gaussianRegularization_apply hf, Complex.ofReal_re]
  have he : Real.exp (-(1/((n:ℝ)+1))*‖x‖^2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left he (hpos x)).trans_eq (mul_one _)

theorem gaussianRegularization_tendsto {f : V → ℝ} (hf : f.HasTemperateGrowth)
    (x : V) : Tendsto (fun n => (gaussianRegularization f n x).re) atTop (𝓝 (f x)) := by
  simp_rw [gaussianRegularization_apply hf, Complex.ofReal_re]
  have hε : Tendsto (fun n : ℕ => -(1/((n:ℝ)+1))*‖x‖^2) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.neg.mul_const (‖x‖^2)
  simpa using (Real.continuous_exp.continuousAt.tendsto.comp hε).const_mul (f x)

variable [MeasurableSpace V] [BorelSpace V]

/-- Dominated convergence preserves the actual mass; the majorant is the
original integrable weight itself. This is valid for any underlying measure. -/
theorem gaussianRegularization_integral_tendsto (μ : Measure V) {f : V → ℝ}
    (hf : f.HasTemperateGrowth) (hpos : ∀ x, 0 ≤ f x) (hfi : Integrable f μ) :
    Tendsto (fun n => ∫ x, (gaussianRegularization f n x).re ∂μ)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence f
  · intro n
    exact (Complex.continuous_re.comp (gaussianRegularization f n).continuous).aestronglyMeasurable
  · exact hfi
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianRegularization_nonneg hf hpos n x)]
    exact gaussianRegularization_le hf hpos n x
  · exact Filter.Eventually.of_forall (gaussianRegularization_tendsto hf)

omit [BorelSpace V] in
theorem gaussianRegularization_integral_eq {f : V → ℝ} (hf : f.HasTemperateGrowth) (n : ℕ)
    (μ : Measure V) :
    (∫ x, gaussianRegularization f n x ∂μ) =
      ((∫ x, (gaussianRegularization f n x).re ∂μ : ℝ) : ℂ) := by
  simp_rw [gaussianRegularization_apply hf, Complex.ofReal_re]
  exact integral_complex_ofReal

/-- The Gaussian approximation limit only needs Fourier-tail control for
sufficiently weak damping, as in the manuscript's strict-tail argument. -/
theorem gaussian_regularization_poisson_bound [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {f : V → ℝ} (hf : f.HasTemperateGrowth) (hpos : ∀ x, 0 ≤ f x)
    (hfi : Integrable f)
    (hTail : ∀ᶠ n in atTop, nonzeroFourierMass L (gaussianRegularization f n) ≤
      ∫ x, (gaussianRegularization f n x).re)
    (r : V) (points : Finset L) :
    ∑ v ∈ points, f (r+v) ≤ 2*(∫ x, f x) / ZLattice.covolume L := by
  have hleft : Tendsto (fun n => ∑ v ∈ points, (gaussianRegularization f n (r+v)).re)
      atTop (𝓝 (∑ v ∈ points, f (r+v))) :=
    tendsto_finsetSum points (fun v _ => gaussianRegularization_tendsto hf (r+v))
  have hright : Tendsto
      (fun n => 2*(∫ x, (gaussianRegularization f n x).re) / ZLattice.covolume L)
      atTop (𝓝 (2*(∫ x, f x) / ZLattice.covolume L)) :=
    (tendsto_const_nhds.mul (gaussianRegularization_integral_tendsto volume hf hpos hfi)).div_const _
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hTail] with n hn
  exact translated_schwartz_weighted_sum_le L (gaussianRegularization f n) _
    (integral_nonneg (gaussianRegularization_nonneg hf hpos n))
    (gaussianRegularization_integral_eq hf n volume)
    (gaussianRegularization_nonneg hf hpos n) hn r points

namespace Witness

/-- The prescribed pair weight in ordinary complex coordinates on a real
inner-product space. The coordinate map is an actual continuous linear map. -/
noncomputable def studentSchwartzApprox (e : V →L[ℝ] (ℂ × ℂ)) (n : ℕ) : SchwartzMap V ℂ :=
  gaussianRegularization (fun x => pairProfile (e x)^p) n

omit [MeasurableSpace V] [BorelSpace V] in
theorem temperateGrowth_pairWeight_coordinates (e : V →L[ℝ] (ℂ × ℂ)) :
    (fun x => pairProfile (e x)^p).HasTemperateGrowth :=
  (temperateGrowth_pairProfile_rpow p).comp e.hasTemperateGrowth

omit [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem studentSchwartzApprox_apply (e : V →L[ℝ] (ℂ × ℂ)) (n : ℕ) (x : V) :
    studentSchwartzApprox e n x =
      ((pairProfile (e x)^p * Real.exp (-(1/((n:ℝ)+1))*‖x‖^2)) : ℝ) :=
  gaussianRegularization_apply (temperateGrowth_pairWeight_coordinates e) n x

omit [MeasurableSpace V] [BorelSpace V] in
theorem studentSchwartzApprox_nonneg (e : V →L[ℝ] (ℂ × ℂ)) (n : ℕ) (x : V) :
    0 ≤ (studentSchwartzApprox e n x).re :=
  gaussianRegularization_nonneg (temperateGrowth_pairWeight_coordinates e)
    (fun y => (Real.rpow_pos_of_pos (pairProfile_pos (e y)) p).le) n x

omit [MeasurableSpace V] [BorelSpace V] in
theorem studentSchwartzApprox_tendsto (e : V →L[ℝ] (ℂ × ℂ)) (x : V) :
    Tendsto (fun n => (studentSchwartzApprox e n x).re) atTop (𝓝 (pairProfile (e x)^p)) :=
  gaussianRegularization_tendsto (temperateGrowth_pairWeight_coordinates e) x

variable [FiniteDimensional ℝ V]

/-- Mass convergence is to the manuscript's independently defined `pairMass`
under actual measure-preserving complex coordinates. -/
theorem studentSchwartzApprox_mass_tendsto (e : V ≃L[ℝ] (ℂ × ℂ))
    (he : MeasurePreserving e volume volume) :
    Tendsto (fun n => ∫ x, (studentSchwartzApprox e.toContinuousLinearMap n x).re)
      atTop (𝓝 pairMass) := by
  have hfi : Integrable (fun x => pairProfile (e x)^p) :=
    (he.integrable_comp integrable_pairMass.aestronglyMeasurable).mpr integrable_pairMass
  have hmass : (∫ x, pairProfile (e x)^p) = pairMass := by
    exact he.integral_comp e.toHomeomorph.measurableEmbedding (fun z : ℂ × ℂ => pairProfile z^p)
  have h := gaussianRegularization_integral_tendsto volume
    (temperateGrowth_pairWeight_coordinates e.toContinuousLinearMap)
    (fun x => (Real.rpow_pos_of_pos (pairProfile_pos _) p).le) hfi
  change Tendsto (fun n => ∫ x, (studentSchwartzApprox e.toContinuousLinearMap n x).re)
    atTop (𝓝 (∫ x, pairProfile (e x)^p)) at h
  rwa [hmass] at h

/-- A Poisson bound for the actual published Student weight. The approximants
and all their limiting properties are now constructed. The remaining input
is the actual nonzero dual Fourier mass bound, at each damping parameter. -/
theorem student_poisson_weighted_sum_le
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (e : V ≃L[ℝ] (ℂ × ℂ)) (he : MeasurePreserving e volume volume)
    (hTail : ∀ᶠ n in atTop, nonzeroFourierMass L (studentSchwartzApprox e.toContinuousLinearMap n) ≤
      ∫ x, (studentSchwartzApprox e.toContinuousLinearMap n x).re)
    (r : V) (points : Finset L) :
    ∑ v ∈ points, pairProfile (e (r+v))^p ≤ 2*pairMass / ZLattice.covolume L := by
  have hfi : Integrable (fun x => pairProfile (e x)^p) :=
    (he.integrable_comp integrable_pairMass.aestronglyMeasurable).mpr integrable_pairMass
  have hmass : (∫ x, pairProfile (e x)^p) = pairMass :=
    he.integral_comp e.toHomeomorph.measurableEmbedding (fun z : ℂ × ℂ => pairProfile z^p)
  have h := gaussian_regularization_poisson_bound L
    (temperateGrowth_pairWeight_coordinates e.toContinuousLinearMap)
    (fun x => (Real.rpow_pos_of_pos (pairProfile_pos (e x)) p).le) hfi hTail r points
  change (∑ v ∈ points, pairProfile (e (r+v))^p) ≤
    2*(∫ x, pairProfile (e x)^p) / ZLattice.covolume L at h
  rwa [hmass] at h

end Witness
end UnitDistance
