module

public import UnitDistance.HeckeParityTheta
public import UnitDistance.HeckeMellinDecay

@[expose] public section
set_option backward.privateInPublic true


open Complex Set Filter Asymptotics MeasureTheory
open scoped Topology Real
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis

variable {ι U : Type*} [Fintype ι] [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]

noncomputable def heckeParityAverage (p : ι → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) (W : ℝ → U → ι → ℝ) (μ : Measure U) (t : ℝ) : ℂ :=
  ∫ u, heckeParityTheta p L (W t u) ∂μ

/-- A finite-measure average of positive-weight theta kernels is continuous in its radial parameter.
Only ordinary continuity and a uniform positive lower bound for the actual weights are used. -/
theorem continuousOn_heckeParityAverage (p : ι → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    (W : ℝ → U → ι → ℝ) (μ : Measure U) [IsFiniteMeasure μ]
    {r m : ℝ} (hr : 0 < r) (hm : 0 < m)
    (hpos : ∀ t, 0 < t → ∀ u i, 0 < W t u i)
    (hWu : ∀ t, 0 < t → ∀ i, Continuous (fun u => W t u i))
    (hWt : ∀ u i, ContinuousOn (fun t => W t u i) (Ioi 0))
    (hlo : ∀ t, 0 < t → ∀ u i, m*t^r ≤ W t u i) :
    ContinuousOn (heckeParityAverage p L W μ) (Ioi 0) := by
  intro t₀ ht₀
  apply ContinuousAt.continuousWithinAt
  have ht₀' : 0 < t₀ := ht₀
  let A : ℝ := m*(t₀/2)^r
  have hA : 0 < A := mul_pos hm (Real.rpow_pos_of_pos (by positivity) _)
  let C : ℝ := ∑' v : L, Real.exp (-Real.pi*∑ i, (A/2)*((v : EuclideanSpace ℝ ι) i)^2)
  have hcontU (t : ℝ) (ht : 0 < t) : Continuous (fun u => heckeParityTheta p L (W t u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (continuousAt_heckeParityTheta p L (hpos t ht u)).comp
      (continuous_pi (hWu t ht)).continuousAt
  have hcontT (u : U) : ContinuousAt (fun t => heckeParityTheta p L (W t u)) t₀ := by
    have hw : ContinuousAt (fun t : ℝ => W t u) t₀ :=
      continuousAt_pi.mpr (fun i => (hWt u i).continuousAt (isOpen_Ioi.mem_nhds ht₀'))
    exact (continuousAt_heckeParityTheta p L (hpos t₀ ht₀' u)).comp (x := t₀) hw
  unfold heckeParityAverage
  apply continuousAt_of_dominated (bound := fun _ : U => C)
  · filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < t₀ from ht₀')] with t ht
    exact (hcontU t ht).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (show t₀/2 < t₀ by linarith)] with t ht
    change t₀/2 < t at ht
    have ht' : 0 < t := by linarith
    apply ae_of_all
    intro u
    have hbound : ∀ i, A ≤ W t u i := fun i =>
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ht.le hr.le) hm.le).trans (hlo t ht' u i)
    exact norm_heckeParityTheta_le_gaussian p L hA hbound
  · exact integrable_const C
  · exact ae_of_all _ hcontT

/-- Entire Mellin transform of an actual finite-measure signed theta average, under the
ordinary normalized Hecke weight identities. -/
theorem differentiable_mellin_heckeParityAverage (p : ι → Bool) (hp : ∃ i, p i = true)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    (W : ℝ → U → ι → ℝ) (μ : Measure U) [IsFiniteMeasure μ]
    {r m M : ℝ} (hr : 0 < r) (hm : 0 < m) (hM : 0 < M)
    (hpos : ∀ t, 0 < t → ∀ u i, 0 < W t u i)
    (hWu : ∀ t, 0 < t → ∀ i, Continuous (fun u => W t u i))
    (hWt : ∀ u i, ContinuousOn (fun t => W t u i) (Ioi 0))
    (hlo : ∀ t, 0 < t → ∀ u i, m*t^r ≤ W t u i)
    (hhi : ∀ t, 0 < t → ∀ u i, W t u i ≤ M*t^r)
    (hprod : ∀ t, 0 < t → ∀ u, (∏ i, W t u i) = t) :
    Differentiable ℂ (mellin (heckeParityAverage p L W μ)) := by
  obtain ⟨C₁, k₁, hC₁, hk₁, hb₁⟩ := exists_heckeParityTheta_radial_bound p hp L hr hm
  obtain ⟨C₂, k₂, hC₂, hk₂, hb₂⟩ := exists_heckeParityTheta_inverse_radial_bound p hp L hr hM
  apply differentiable_mellin_of_two_sided_stretched_exp
    (continuousOn_heckeParityAverage p L W μ hr hm hpos hWu hWt hlo) hk₁ hk₂ hr hr
    (C₁ := C₁ * μ.real univ) (C₂ := C₂ * μ.real univ) (b := -(1/2 : ℝ))
  · intro t ht
    have ht' : 0 < t := by linarith
    have h := norm_integral_le_of_norm_le_const
      (f := fun u => heckeParityTheta p L (W t u)) (μ := μ)
      (ae_of_all μ (fun u => hb₁ t ht (W t u) (hlo t ht' u)))
    simpa only [heckeParityAverage, mul_assoc, mul_comm, mul_left_comm] using h
  · intro t ht ht1
    have h := norm_integral_le_of_norm_le_const
      (f := fun u => heckeParityTheta p L (W t u)) (μ := μ)
      (ae_of_all μ (fun u => hb₂ t ht ht1 (W t u) (hpos t ht u) (hhi t ht u) (hprod t ht u)))
    simpa only [heckeParityAverage, mul_assoc, mul_comm, mul_left_comm] using h

/-- Absolute convergence of the same actual averaged Mellin integral at every parameter. -/
theorem mellinConvergent_heckeParityAverage (p : ι → Bool) (hp : ∃ i, p i = true)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    (W : ℝ → U → ι → ℝ) (μ : Measure U) [IsFiniteMeasure μ]
    {r m M : ℝ} (hr : 0 < r) (hm : 0 < m) (hM : 0 < M)
    (hpos : ∀ t, 0 < t → ∀ u i, 0 < W t u i)
    (hWu : ∀ t, 0 < t → ∀ i, Continuous (fun u => W t u i))
    (hWt : ∀ u i, ContinuousOn (fun t => W t u i) (Ioi 0))
    (hlo : ∀ t, 0 < t → ∀ u i, m*t^r ≤ W t u i)
    (hhi : ∀ t, 0 < t → ∀ u i, W t u i ≤ M*t^r)
    (hprod : ∀ t, 0 < t → ∀ u, (∏ i, W t u i) = t) (s : ℂ) :
    MellinConvergent (heckeParityAverage p L W μ) s := by
  obtain ⟨C₁, k₁, hC₁, hk₁, hb₁⟩ := exists_heckeParityTheta_radial_bound p hp L hr hm
  obtain ⟨C₂, k₂, hC₂, hk₂, hb₂⟩ := exists_heckeParityTheta_inverse_radial_bound p hp L hr hM
  apply mellinConvergent_of_two_sided_stretched_exp (s := s)
    (continuousOn_heckeParityAverage p L W μ hr hm hpos hWu hWt hlo) hk₁ hk₂ hr hr
    (C₁ := C₁ * μ.real univ) (C₂ := C₂ * μ.real univ) (b := -(1/2 : ℝ))
  · intro t ht
    have ht' : 0 < t := by linarith
    have h := norm_integral_le_of_norm_le_const
      (f := fun u => heckeParityTheta p L (W t u)) (μ := μ)
      (ae_of_all μ (fun u => hb₁ t ht (W t u) (hlo t ht' u)))
    simpa only [heckeParityAverage, mul_assoc, mul_comm, mul_left_comm] using h
  · intro t ht ht1
    have h := norm_integral_le_of_norm_le_const
      (f := fun u => heckeParityTheta p L (W t u)) (μ := μ)
      (ae_of_all μ (fun u => hb₂ t ht ht1 (W t u) (hpos t ht u) (hhi t ht u) (hprod t ht u)))
    simpa only [heckeParityAverage, mul_assoc, mul_comm, mul_left_comm] using h

end UnitDistance.NumberFieldAnalysis
