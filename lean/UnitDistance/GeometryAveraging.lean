module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section
set_option backward.privateInPublic true


/-!
# Weighted selection and joint averaging

The finite selection is the class-group pigeonhole step of Section 6.
The measure theorem selects vertices and edges at the *same* parameter.
No probability normalization is required: both integrals use one measure.
-/

open scoped BigOperators
open MeasureTheory

namespace UnitDistance

/-- Weighted pigeonhole principle, with a positive-weight reference in the
selected class. The class map may be any map to a nonempty finite quotient. -/
theorem weighted_class_selection {ι C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (s : Finset ι) (classOf : ι → C) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hpos : 0 < ∑ i ∈ s, w i) :
    ∃ c : C, (∑ i ∈ s, w i) / Fintype.card C ≤
      ∑ i ∈ s.filter (fun i => classOf i = c), w i ∧
      ∃ i₀ ∈ s, classOf i₀ = c ∧ 0 < w i₀ := by
  classical
  let W : C → ℝ := fun c => ∑ i ∈ s.filter (fun i => classOf i = c), w i
  have hsum : ∑ c : C, W c = ∑ i ∈ s, w i := by
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) w
  have hcard : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hbound : (∑ c : C, (∑ i ∈ s, w i) / Fintype.card C) ≤ ∑ c : C, W c := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum]
    exact (mul_div_cancel₀ _ (ne_of_gt hcard)).le
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hbound
  refine ⟨c, hc, ?_⟩
  have hcpos : 0 < W c := lt_of_lt_of_le (div_pos hpos hcard) hc
  obtain ⟨i, hi, hwi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i hi => hw i (Finset.mem_filter.mp hi).1)).mp hcpos
  obtain ⟨his, hic⟩ := Finset.mem_filter.mp hi
  exact ⟨i, his, hic, hwi⟩

/-- If the integrated edge mass is at least `a` times the integrated vertex
mass, a nonempty parameter attains that ratio. `zero_edges` is the ordinary
fact that a configuration with no vertices has no edges. -/
theorem exists_joint_parameter {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (N E : T → ℝ) (a : ℝ)
    (hN : Integrable N μ) (hE : Integrable E μ)
    (hNnonneg : ∀ t, 0 ≤ N t)
    (zero_edges : ∀ t, N t = 0 → E t = 0)
    (hNpos : 0 < ∫ t, N t ∂μ)
    (hmass : a * (∫ t, N t ∂μ) ≤ ∫ t, E t ∂μ) :
    ∃ t, 0 < N t ∧ a * N t ≤ E t := by
  by_contra! hnone
  have hle : ∀ t, E t ≤ a * N t := by
    intro t
    rcases (hNnonneg t).eq_or_lt with hn | hn
    · rw [← hn, zero_edges t hn.symm]
      simp
    · exact (hnone t hn).le
  have h_int_le := integral_mono hE (hN.const_mul a) hle
  rw [integral_const_mul] at h_int_le
  have h_int_eq : (∫ t, E t ∂μ) = ∫ t, a * N t ∂μ := by
    rw [integral_const_mul]
    exact le_antisymm h_int_le hmass
  have heq : E =ᵐ[μ] fun t => a * N t :=
    (integral_eq_iff_of_ae_le hE (hN.const_mul a) (Filter.Eventually.of_forall hle)).mp h_int_eq
  have hnzero : N =ᵐ[μ] 0 := by
    filter_upwards [heq] with t ht
    rcases (hNnonneg t).eq_or_lt with hn | hn
    · exact hn.symm
    · exact (False.elim ((hnone t hn).ne ht))
  have : (∫ t, N t ∂μ) = 0 := by simpa using integral_congr_ae hnzero
  linarith

/-- A uniform vertex bound applies to the identical parameter produced by
joint averaging, yielding the exact real-power denominator. -/
theorem exists_joint_parameter_rpow {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (N E : T → ℝ) (a B δ : ℝ)
    (hN : Integrable N μ) (hE : Integrable E μ)
    (hNnonneg : ∀ t, 0 ≤ N t)
    (zero_edges : ∀ t, N t = 0 → E t = 0)
    (hNpos : 0 < ∫ t, N t ∂μ)
    (hmass : a * (∫ t, N t ∂μ) ≤ ∫ t, E t ∂μ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hbound : ∀ t, N t ≤ B) :
    ∃ t, 0 < N t ∧ N t ≤ B ∧ a / B ^ δ ≤ E t / N t ^ (1 + δ) := by
  obtain ⟨t, ht, he⟩ := exists_joint_parameter μ N E a hN hE hNnonneg zero_edges hNpos hmass
  have hB : 0 < B := lt_of_lt_of_le ht (hbound t)
  have hp : 0 < N t ^ (1 + δ) := Real.rpow_pos_of_pos ht _
  have hpow : N t ^ δ ≤ B ^ δ := Real.rpow_le_rpow ht.le (hbound t) hδ
  have hpB : 0 < B ^ δ := Real.rpow_pos_of_pos hB _
  refine ⟨t, ht, hbound t, ?_⟩
  apply (le_div_iff₀ hp).mpr
  rw [Real.rpow_add ht, Real.rpow_one]
  calc
    a / B ^ δ * (N t * N t ^ δ) = N t * (a * N t ^ δ / B ^ δ) := by ring
    _ ≤ N t * a := mul_le_mul_of_nonneg_left ((div_le_iff₀ hpB).mpr (mul_le_mul_of_nonneg_left hpow ha)) ht.le
    _ ≤ E t := by simpa [mul_comm] using he

end UnitDistance
