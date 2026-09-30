module

public import UnitDistance.LocalRegularity
public import UnitDistance.ProductMeasurableGroup
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual joint local overlap integral

Counting all integer displacements is harmless because a finite shell
profile has a proved finite displacement cutoff. The resulting joint
integral is exactly the already evaluated local operator energy.
-/

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators ENNReal
namespace UnitDistance.Local.BallSystem

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  {μ : Measure G} [SFinite μ] {Q : ℝ} (B : BallSystem G μ Q)
  {U : Type*} [MeasurableSpace U] (S : B.ReciprocalSteps U)
  (ν : Measure U) [IsProbabilityMeasure ν]

theorem reciprocalSteps_measurable (hs : ∀ n, Measurable (S.step n)) :
    Measurable (fun d : ℤ × U => S.step d.1 d.2) :=
  measurable_from_prod_countable_right hs

/-- Actual weight on integer displacement, unit parameter, and position. -/
def shellOverlapWeight (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (z : (ℤ × U) × (G × G)) : ℝ :=
  B.shellProfile k I w z.2 * B.shellProfile k I w (z.2 + S.step z.1.1 z.1.2)

theorem shellOverlapWeight_measurable (hs : ∀ n, Measurable (S.step n))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    Measurable (B.shellOverlapWeight S k I w) :=
  ((B.shellProfile_measurable k I w).comp measurable_snd).mul
    ((B.shellProfile_measurable k I w).comp
      (measurable_snd.add ((B.reciprocalSteps_measurable S hs).comp measurable_fst)))

theorem shellOverlapWeight_integrable (hQ : 0 < Q)
    (hs : ∀ n, Measurable (S.step n))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    Integrable (B.shellOverlapWeight S k I w)
      ((Measure.count.prod ν).prod (μ.prod μ)) := by
  let Lx := I.sup Prod.fst
  let Ly := I.sup Prod.snd
  have hI : ∀ ij ∈ I, ij.1 ≤ Lx ∧ ij.2 ≤ Ly :=
    fun ij hij => ⟨Finset.le_sup hij, Finset.le_sup hij⟩
  let N := Finset.Icc (-(Lx : ℤ)) (k + (Ly : ℤ))
  let R : Set (G × G) := (B.ball Lx : Set G) ×ˢ (B.ball (k + (Ly : ℤ)) : Set G)
  let M : ℝ := ∑ ij ∈ I, |w ij|
  let T : Set ((ℤ × U) × (G × G)) := ((N : Set ℤ) ×ˢ Set.univ) ×ˢ R
  have hRm : MeasurableSet R := (B.measurable _).prod (B.measurable _)
  have hTm : MeasurableSet T := (N.measurableSet.prod MeasurableSet.univ).prod hRm
  have hTf : ((Measure.count.prod ν).prod (μ.prod μ)) T ≠ ∞ := by
    simp only [T, R, Measure.prod_prod, measure_univ, mul_one]
    exact ENNReal.mul_ne_top (by simp)
      (ENNReal.mul_ne_top (B.ball_measure_ne_top hQ _) (B.ball_measure_ne_top hQ _))
  have hdom : Integrable (T.indicator (fun _ => M*M))
      ((Measure.count.prod ν).prod (μ.prod μ)) :=
    (integrable_indicator_iff hTm).mpr (integrableOn_const hTf)
  apply hdom.mono' (B.shellOverlapWeight_measurable S hs k I w).aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z ∈ T
  · rw [Set.indicator_of_mem hz, shellOverlapWeight, norm_mul]
    exact mul_le_mul (B.shellProfile_norm_le k I w _) (B.shellProfile_norm_le k I w _)
      (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  · rw [Set.indicator_of_notMem hz]
    have hwzero : B.shellOverlapWeight S k I w z = 0 := by
      by_cases hn : z.1.1 ∈ N
      · have hx : z.2 ∉ R := fun hx => hz ⟨⟨hn, Set.mem_univ _⟩, hx⟩
        have hf : B.shellProfile k I w z.2 = 0 := by
          by_contra hf
          exact hx (B.shellProfile_support k I w Lx Ly hI hf)
        simp [shellOverlapWeight, hf]
      · exact B.shellProfile_overlap_zero S k I w Lx Ly hI _ hn _ _
    simp [hwzero]

/-- The actual counting-product integral equals the literal iterated local
energy, with all uses of Fubini justified by integrability. -/
theorem shellOverlapWeight_integral (hQ : 0 < Q)
    (hs : ∀ n, Measurable (S.step n))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    (∫ z, B.shellOverlapWeight S k I w z
      ∂(Measure.count.prod ν).prod (μ.prod μ)) =
      B.profileEnergy S ν (B.shellProfile k I w) := by
  have hi := B.shellOverlapWeight_integrable S ν hQ hs k I w
  rw [integral_prod _ hi, integral_prod _ hi.integral_prod_left,
    integral_countable hi.integral_prod_left.integral_prod_left]
  simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  rfl

end UnitDistance.Local.BallSystem
