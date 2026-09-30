module

public import UnitDistance.TensorMixedLabels

@[expose] public section
set_option backward.privateInPublic true


/-! # Concentration as a finite sum of canonical overlap integrals -/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace UnitDistance.Witness

variable {β γ ι : Type*} [Fintype β] [Fintype γ] [Fintype ι] {G U : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, MeasurableSpace (G i)]
  [∀ i, MeasurableAdd₂ (G i)] [∀ i, MeasurableNeg (G i)]
  [∀ i, MeasurableSpace (U i)]
  (v : ι → Fin 11) (μ : (i : ι) → Measure (G i))
  [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsAddRightInvariant]
  [∀ i, (μ i).IsAddLeftInvariant] [∀ i, (μ i).IsNegInvariant]
  (B : (i : ι) → Local.BallSystem (G i) (μ i) (residueCard (v i)))
  (S : (i : ι) → (B i).ReciprocalSteps (U i))

abbrev FiniteValuationIndex := ↥(finiteValuationLabels v)

def mixedCanonicalMean (u₀ : (i : ι) → U i) (β γ : Type*) [Fintype β] [Fintype γ] : ℝ :=
  mixedEnergyMean v μ B S (fun i => Measure.dirac (u₀ i)) β γ

theorem mixedCanonicalOverlap_integral_finite
    (hs : ∀ i n, Measurable ((S i).step n)) (u₀ : (i : ι) → U i) (T : ℝ) (n : ι → ℤ) :
    (∫⁻ u : γ → ℝ, mixedCanonicalOverlap (β := β) v μ B S u₀ T n u) ≠ ∞ := by
  by_cases hn : n ∈ finiteValuationLabels v
  · have h := mixed_supportedWindowOverlap_finite (β := β) (γ := γ) v μ B S
      (fun i => Measure.dirac (u₀ i)) hs T
    rw [mixed_dirac_supportedWindowOverlap_eq_sum v μ B S hs u₀ T] at h
    exact ne_top_of_le_ne_top h (Finset.single_le_sum
      (f := fun n : ι → ℤ => ∫⁻ u : γ → ℝ, mixedCanonicalOverlap (β := β) v μ B S u₀ T n u)
      (fun _ _ => bot_le) hn)
  · simp only [mixedCanonicalOverlap_eq_zero v μ B S u₀ T n hn, lintegral_zero, ne_eq,
      ENNReal.zero_ne_top, not_false_eq_true]

theorem mixed_dirac_supportedWindowOverlap_toReal_sum
    (hs : ∀ i n, Measurable ((S i).step n)) (u₀ : (i : ι) → U i) (T : ℝ) :
    (supportedWindowOverlap (mixedDisplacementMeasure (γ := γ) (fun i => Measure.dirac (u₀ i)))
      (mixedPositionMeasure (β := β) (γ := γ) μ) (mixedStep v μ B S)
      (mixedPositionSupport v μ B) (mixedPositionEnergy v μ B) T).toReal =
      ∑ n : FiniteValuationIndex v,
        (∫⁻ u : γ → ℝ, mixedCanonicalOverlap (β := β) v μ B S u₀ T n u).toReal := by
  rw [mixed_dirac_supportedWindowOverlap_eq_sum v μ B S hs u₀ T,
    ENNReal.toReal_sum (fun n _ => mixedCanonicalOverlap_integral_finite v μ B S hs u₀ T n)]
  exact (Finset.sum_coe_sort (finiteValuationLabels v)
    (fun n : ι → ℤ =>
      (∫⁻ u : γ → ℝ, mixedCanonicalOverlap (β := β) v μ B S u₀ T n u).toReal)).symm

/-- The literal finite-label overlap sum, with the full mixed concentration
mass and dimension-linear variance constant. -/
theorem mixedCanonicalOverlap_sum_concentration
    (hs : ∀ i n, Measurable ((S i).step n)) (u₀ : (i : ι) → U i)
    (hcount : (Fintype.card ι:ℝ) ≤ (69/32:ℝ)*((Fintype.card β:ℝ)+2*Fintype.card γ))
    {ε : ℝ} (hε : 0 < ε) (hd : 0 < (Fintype.card β:ℝ)+2*Fintype.card γ)
    (hlarge : 4*mixedEnergyVarianceConstant ≤ ε^2*((Fintype.card β:ℝ)+2*Fintype.card γ)) :
    let d : ℝ := (Fintype.card β:ℝ)+2*Fintype.card γ
    let mean := mixedCanonicalMean v μ B S u₀ β γ
    (1/2:ℝ)*mixedOverlapMass v β γ*Real.exp (2*(mean-ε*d)) ≤
      ∑ n : FiniteValuationIndex v,
        (∫⁻ u : γ → ℝ, mixedCanonicalOverlap (β := β) v μ B S u₀ (mean+ε*d) n u).toReal := by
  dsimp only
  rw [← mixed_dirac_supportedWindowOverlap_toReal_sum v μ B S hs u₀]
  exact mixed_concentrated_supportedWindowOverlap v μ B S
    (fun i => Measure.dirac (u₀ i)) hs hcount hε hd hlarge

end UnitDistance.Witness
