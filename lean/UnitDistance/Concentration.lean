module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Simultaneous endpoint concentration

The endpoints need not be independent. Independence is required only between
different profile blocks within each endpoint. This distinction is essential
for the overlap probability law in Sections 5--6.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace UnitDistance

theorem real_chebyshev {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) {r : ℝ} (hr : 0 < r) :
    μ.real {ω | r ≤ |X ω - ∫ ω, X ω ∂μ|} ≤ variance X μ / r^2 := by
  have h := meas_ge_le_variance_div_sq hX hr
  have h' := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h
  simpa only [measureReal_def,
    ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg r))]
    using h'

/-- Both energies lie strictly within radius `r` of their respective means
with the stated probability. No independence between `X` and `Y` is assumed. -/
theorem two_endpoint_concentration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) {r : ℝ} (hr : 0 < r) :
    1 - (variance X μ + variance Y μ) / r^2 ≤
      μ.real {ω | |X ω - ∫ ω, X ω ∂μ| < r ∧
                    |Y ω - ∫ ω, Y ω ∂μ| < r} := by
  let B₁ := {ω | r ≤ |X ω - ∫ ω, X ω ∂μ|}
  let B₂ := {ω | r ≤ |Y ω - ∫ ω, Y ω ∂μ|}
  have hm₁ : MeasurableSet B₁ := measurableSet_le measurable_const (by
    simpa only [Real.norm_eq_abs] using (hXm.sub_const (∫ ω, X ω ∂μ)).norm)
  have hm₂ : MeasurableSet B₂ := measurableSet_le measurable_const (by
    simpa only [Real.norm_eq_abs] using (hYm.sub_const (∫ ω, Y ω ∂μ)).norm)
  have heq : {ω | |X ω - ∫ ω, X ω ∂μ| < r ∧
      |Y ω - ∫ ω, Y ω ∂μ| < r} = (B₁ ∪ B₂)ᶜ := by
    ext ω
    simp [B₁, B₂, not_le]
  rw [heq, probReal_compl_eq_one_sub (hm₁.union hm₂)]
  have h₁ := real_chebyshev μ X hX hr
  have h₂ := real_chebyshev μ Y hY hr
  have hu := measureReal_union_le (μ := μ) B₁ B₂
  dsimp [B₁, B₂] at hu
  rw [add_div]
  linarith

/-- Variance grows at most linearly in the number of independent blocks. -/
theorem independent_sum_variance_le {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (X : ι → Ω → ℝ) (C : ℝ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hind : Set.Pairwise (s : Set ι) (fun i j => IndepFun (X i) (X j) μ))
    (hv : ∀ i ∈ s, variance (X i) μ ≤ C) :
    variance (fun ω => ∑ i ∈ s, X i ω) μ ≤ s.card * C := by
  have h := IndepFun.variance_sum hX hind
  have heq : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
    funext ω
    simp
  rw [heq, h]
  calc
    ∑ i ∈ s, variance (X i) μ ≤ ∑ _i ∈ s, C := Finset.sum_le_sum hv
    _ = s.card * C := by simp

/-- The paper's uniform probability `1/2`, with an explicit sufficient
dimension threshold and exact energy radius `ε d`. -/
theorem two_endpoint_half_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (C ε d : ℝ) (hε : 0 < ε) (hd : 0 < d)
    (hvX : variance X μ ≤ C*d) (hvY : variance Y μ ≤ C*d)
    (hlarge : 4*C ≤ ε^2*d) :
    (1 / 2 : ℝ) ≤ μ.real {ω |
      |X ω - ∫ ω, X ω ∂μ| < ε*d ∧ |Y ω - ∫ ω, Y ω ∂μ| < ε*d} := by
  have hc := two_endpoint_concentration μ X Y hXm hYm hX hY (mul_pos hε hd)
  have hp : 0 < (ε*d)^2 := sq_pos_of_pos (mul_pos hε hd)
  have hv : (variance X μ + variance Y μ) / (ε*d)^2 ≤ 1/2 := by
    apply (div_le_iff₀ hp).mpr
    have h := mul_le_mul_of_nonneg_right hlarge hd.le
    nlinarith
  linarith

end UnitDistance
