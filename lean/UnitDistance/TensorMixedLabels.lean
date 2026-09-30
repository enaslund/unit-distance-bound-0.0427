module

public import UnitDistance.TensorMixedVolume
public import Mathlib.Data.Fintype.Pi

@[expose] public section
set_option backward.privateInPublic true


/-! # Finite signed valuation labels for the actual common window

Every local overlap vanishes outside [-5,k+5]. The global canonical overlap
therefore has a finite set of valuation labels, independent of the energy
threshold. Coordinates retain the actual logarithmic displacements.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace UnitDistance.Witness

variable {β γ ι : Type*} [Fintype β] [Fintype γ] [Fintype ι]
  {G U : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, MeasurableSpace (G i)]
  [∀ i, MeasurableAdd₂ (G i)] [∀ i, MeasurableNeg (G i)]
  [∀ i, MeasurableSpace (U i)]
  (v : ι → Fin 11) (μ : (i : ι) → Measure (G i))
  [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsAddRightInvariant]
  [∀ i, (μ i).IsAddLeftInvariant] [∀ i, (μ i).IsNegInvariant]
  (B : (i : ι) → Local.BallSystem (G i) (μ i) (residueCard (v i)))
  (S : (i : ι) → (B i).ReciprocalSteps (U i))

/-- All possible valuation labels contributing to the witness overlap. -/
def finiteValuationLabels : Finset (ι → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (-5:ℤ) (periodPower (v i)+5))

@[simp] theorem mem_finiteValuationLabels (n : ι → ℤ) :
    n ∈ finiteValuationLabels v ↔ ∀ i, -5 ≤ n i ∧ n i ≤ periodPower (v i)+5 := by
  simp [finiteValuationLabels]

/-- The literal overlap for chosen canonical local unit directions. -/
def mixedCanonicalOverlap (u₀ : (i : ι) → U i) (T : ℝ)
    (n : ι → ℤ) (u : γ → ℝ) : ℝ≥0∞ :=
  mixedPositionMeasure (β := β) (γ := γ) μ
    (overlapSet (supportedWindow (mixedPositionSupport v μ B) (mixedPositionEnergy v μ B) T)
      (mixedStep v μ B S (u, fun i => (n i, u₀ i))))

theorem measurable_mixedCanonicalOverlap (hs : ∀ i n, Measurable ((S i).step n))
    (u₀ : (i : ι) → U i) (T : ℝ) (n : ι → ℤ) :
    Measurable (mixedCanonicalOverlap (β := β) (γ := γ) v μ B S u₀ T n) := by
  have hW := measurableSet_supportedWindow (measurableSet_mixedPositionSupport (β := β) (γ := γ) v μ B)
    (measurable_mixedPositionEnergy v μ B) T
  have hs' : Measurable (fun u : γ → ℝ => mixedStep (β := β) v μ B S
      (u, fun i => (n i, u₀ i))) :=
    (measurable_mixedStep v μ B S hs).comp (measurable_id.prodMk measurable_const)
  exact measurable_overlap_volume _ _ hW _ hs'

/-- A missing valuation label makes the actual overlap set empty. -/
theorem mixedCanonicalOverlap_eq_zero (u₀ : (i : ι) → U i) (T : ℝ)
    (n : ι → ℤ) (hn : n ∉ finiteValuationLabels v) (u : γ → ℝ) :
    mixedCanonicalOverlap (β := β) (γ := γ) v μ B S u₀ T n u = 0 := by
  have hn' : ¬∀ i, n i ∈ Finset.Icc (-5:ℤ) (periodPower (v i)+5) := by
    simpa only [finiteValuationLabels, Fintype.mem_piFinset] using hn
  obtain ⟨i, hi⟩ := not_forall.mp hn'
  unfold mixedCanonicalOverlap
  suffices he : overlapSet
      (supportedWindow (mixedPositionSupport (β := β) (γ := γ) v μ B)
        (mixedPositionEnergy v μ B) T)
      (mixedStep v μ B S (u, fun i => (n i, u₀ i))) = ∅ by rw [he, measure_empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx₁ : tensorFiniteProfile v μ B x.2 ≠ 0 := hx.1.1
  have hx₂ : tensorFiniteProfile v μ B
      (fun j => x.2 j+(S j).step (n j) (u₀ j)) ≠ 0 := hx.2.1
  have h₁ := (Finset.prod_ne_zero_iff.mp hx₁) i (Finset.mem_univ i)
  have h₂ := (Finset.prod_ne_zero_iff.mp hx₂) i (Finset.mem_univ i)
  apply mul_ne_zero h₁ h₂
  exact (B i).shellProfile_overlap_zero (S i) (periodPower (v i))
    (Finset.range 6 ×ˢ Finset.range 6)
    (fun ij => shellWeightNat (v i) ij.1 * shellWeightNat (v i) ij.2)
    5 5 (fun ij hij => by simp only [Finset.mem_product, Finset.mem_range] at hij; omega)
    (n i) hi (u₀ i) (x.2 i)

theorem mixedCanonicalOverlap_finite (u₀ : (i : ι) → U i) (T : ℝ)
    (n : ι → ℤ) (u : γ → ℝ) :
    mixedCanonicalOverlap (β := β) (γ := γ) v μ B S u₀ T n u ≠ ∞ :=
  ne_top_of_le_ne_top (mixed_supportedWindow_finite v μ B T)
    (measure_mono Set.inter_subset_left)

theorem measurable_mixedCanonicalOverlap_joint (hs : ∀ i n, Measurable ((S i).step n))
    (u₀ : (i : ι) → U i) (T : ℝ) :
    Measurable (fun p : (γ → ℝ) × (ι → ℤ) =>
      mixedCanonicalOverlap (β := β) v μ B S u₀ T p.2 p.1) := by
  have hW := measurableSet_supportedWindow (measurableSet_mixedPositionSupport (β := β) (γ := γ) v μ B)
    (measurable_mixedPositionEnergy v μ B) T
  have hs' : Measurable (fun p : (γ → ℝ) × (ι → ℤ) =>
      mixedStep (β := β) v μ B S (p.1, fun i => (p.2 i, u₀ i))) :=
    (measurable_mixedStep v μ B S hs).comp (measurable_fst.prodMk
      (Measurable.of_eval (fun i =>
        ((measurable_pi_apply i).comp measurable_snd).prodMk measurable_const)))
  exact measurable_overlap_volume _ _ hW _ hs'

theorem pi_int_count : (Measure.pi (fun _ : ι => (Measure.count : Measure ℤ))) =
    (Measure.count : Measure (ι → ℤ)) := by
  apply Measure.ext_of_singleton
  intro n
  simp

/-- Dirac unit directions give the literal canonical overlap sum. No phase
invariance hypothesis is needed for this normalization. -/
theorem mixed_dirac_supportedWindowOverlap_eq_sum
    (hs : ∀ i n, Measurable ((S i).step n)) (u₀ : (i : ι) → U i) (T : ℝ) :
    supportedWindowOverlap (mixedDisplacementMeasure (γ := γ) (fun i => Measure.dirac (u₀ i)))
      (mixedPositionMeasure (β := β) (γ := γ) μ) (mixedStep v μ B S)
      (mixedPositionSupport v μ B) (mixedPositionEnergy v μ B) T =
      ∑ n ∈ finiteValuationLabels v, ∫⁻ u : γ → ℝ,
        mixedCanonicalOverlap (β := β) v μ B S u₀ T n u := by
  have hi (i : ι) : MeasurePreserving (fun n : ℤ => (n, u₀ i))
      Measure.count ((Measure.count : Measure ℤ).prod (Measure.dirac (u₀ i))) :=
    ⟨measurable_id.prodMk measurable_const, (Measure.prod_dirac _).symm⟩
  have hpi := measurePreserving_pi (fun _ : ι => (Measure.count : Measure ℤ))
    (fun i => (Measure.count : Measure ℤ).prod (Measure.dirac (u₀ i))) hi
  rw [pi_int_count] at hpi
  have he := (MeasurePreserving.id (volume : Measure (γ → ℝ))).prod hpi
  have hW := measurableSet_supportedWindow (measurableSet_mixedPositionSupport (β := β) (γ := γ) v μ B)
    (measurable_mixedPositionEnergy v μ B) T
  have hF := measurable_overlap_volume (mixedPositionMeasure (β := β) (γ := γ) μ)
    _ hW (mixedStep v μ B S) (measurable_mixedStep v μ B S hs)
  have hΦ := measurable_mixedCanonicalOverlap_joint (β := β) (γ := γ) v μ B S hs u₀ T
  calc
    _ = ∫⁻ p : (γ → ℝ) × (ι → ℤ),
        mixedCanonicalOverlap (β := β) v μ B S u₀ T p.2 p.1
          ∂(volume.prod Measure.count) := (he.lintegral_comp hF).symm
    _ = ∫⁻ u : γ → ℝ, ∫⁻ n : ι → ℤ,
        mixedCanonicalOverlap (β := β) v μ B S u₀ T n u ∂Measure.count :=
      lintegral_prod _ hΦ.aemeasurable
    _ = ∑' n : ι → ℤ, ∫⁻ u : γ → ℝ,
        mixedCanonicalOverlap (β := β) v μ B S u₀ T n u := by
      simp_rw [lintegral_count]
      exact lintegral_tsum (fun n => (measurable_mixedCanonicalOverlap v μ B S hs u₀ T n).aemeasurable)
    _ = _ := tsum_eq_sum (fun n hn => by
      simp only [mixedCanonicalOverlap_eq_zero v μ B S u₀ T n hn, lintegral_zero])

end UnitDistance.Witness
