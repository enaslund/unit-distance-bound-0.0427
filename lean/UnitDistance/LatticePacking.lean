/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Generalized in September 2026 by the GPT-6 Astra formalization run from
Mathlib's Besicovitch.card_le_of_separated, at the project's pinned Mathlib
revision. The original packing-by-Haar-balls proof is adapted to arbitrary
radii to supply the manuscript's exact shell constants.
-/
module

public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Quantitative finite packing in any finite-dimensional real normed space. -/
open MeasureTheory Metric Set Module
open scoped ENNReal Function
namespace UnitDistance.Packing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Separated centers in a radius-`A` ball have cardinality at most
`((A+r)/r)^dim` when their mutual distances are at least `2r`. -/
theorem card_le_pow_ratio (s : Finset E) {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r)
    (hs : ∀ c ∈ s, ‖c‖ ≤ A)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 2*r ≤ ‖c-d‖) :
    (s.card : ℝ) ≤ ((A+r)/r)^finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have har : 0 < A+r := by positivity
  let U := ⋃ c ∈ s, ball (c : E) r
  have hd : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) r) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    simpa only [two_mul] using hsep c hc d hd hcd
  have hu : U ⊆ ball (0 : E) (A+r) := by
    refine iUnion₂_subset fun c hc => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    linarith [hs c hc]
  have hi : (s.card : ℝ≥0∞) * ENNReal.ofReal (r^finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((A+r)^finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ U := by
        rw [show U = ⋃ c ∈ s, ball (c : E) r from rfl,
          measure_biUnion_finset hd fun _ _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hr, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) (A+r)) := measure_mono hu
      _ = _ := μ.addHaar_ball_of_pos _ har
  have hj := (ENNReal.mul_le_mul_iff_left
    (measure_ball_pos μ (0 : E) zero_lt_one).ne' measure_ball_lt_top.ne).mp hi
  have hk := ENNReal.toReal_le_of_le_ofReal (pow_nonneg har.le _) hj
  have hreal : (s.card : ℝ) * r^finrank ℝ E ≤ (A+r)^finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hr.le _)] using hk
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hr _)).mpr hreal

/-- The exact `(2j+3)^dim` count used for the manuscript's `j`th shell.
Only the upper shell boundary is needed for this packing bound. -/
theorem card_shell_le (s : Finset E) {R : ℝ} (hR : 0 < R) (j : ℕ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ (j+1)*R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → R ≤ ‖c-d‖) :
    (s.card : ℝ) ≤ (2*(j:ℝ)+3)^finrank ℝ E := by
  have h := card_le_pow_ratio s (A := (j+1)*R) (r := R/2) (by positivity)
    (by positivity) hs (by simpa only [mul_div_cancel₀ _ (two_ne_zero : (2:ℝ) ≠ 0)] using hsep)
  have he : (((j:ℝ)+1)*R+R/2)/(R/2) = 2*(j:ℝ)+3 := by field_simp; ring
  rwa [he] at h

/-- The shell polynomial is bounded by the manuscript's geometric base. -/
theorem two_mul_add_three_le_pow_five (j : ℕ) (hj : 1 ≤ j) :
    2*j+3 ≤ 5^j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    rw [pow_succ]
    omega

theorem card_shell_le_five (s : Finset E) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (hj : 1 ≤ j) (hs : ∀ c ∈ s, ‖c‖ ≤ (j+1)*R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → R ≤ ‖c-d‖) :
    (s.card : ℝ) ≤ (5 : ℝ)^(finrank ℝ E*j) := by
  have hbase : 2*(j:ℝ)+3 ≤ (5:ℝ)^j := by
    exact_mod_cast two_mul_add_three_le_pow_five j hj
  calc
    _ ≤ (2*(j:ℝ)+3)^finrank ℝ E := card_shell_le s hR j hs hsep
    _ ≤ ((5:ℝ)^j)^finrank ℝ E := pow_le_pow_left₀ (by positivity) hbase _
    _ = (5:ℝ)^(finrank ℝ E*j) := by rw [← pow_mul, Nat.mul_comm]

end UnitDistance.Packing
