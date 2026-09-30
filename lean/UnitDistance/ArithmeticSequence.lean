module

public import UnitDistance.Counting
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section
set_option backward.privateInPublic true


/-! # Sequence extraction from eventual finite arithmetic constructions -/

open Filter
open scoped Classical

namespace UnitDistance

/-- An eventual construction with divergent ratio bounds suffices for the
exact sequence target. There is no requirement on the initial indices. -/
theorem target_of_eventual_ratio_bounds (a : ℕ → ℝ)
    (ha : Tendsto a atTop atTop)
    (hU : ∀ᶠ j in atTop, ∃ U : Finset ℂ,
      a j ≤ unitPairs U/(U.card : ℝ)^exponent) : Target := by
  classical
  let U : ℕ → Finset ℂ := fun j =>
    if h : ∃ V : Finset ℂ, a j ≤ unitPairs V/(V.card : ℝ)^exponent then
      Classical.choose h else ∅
  have hle : ∀ᶠ j in atTop, a j ≤ unitPairs (U j)/((U j).card : ℝ)^exponent := by
    filter_upwards [hU] with j hj
    dsimp only [U]
    rw [dif_pos hj]
    exact Classical.choose_spec hj
  have ht := tendsto_atTop_mono' atTop hle ha
  exact ⟨U, card_tendsto_of_ratio_tendsto U (by norm_num [exponent]) ht, ht⟩

/-- A fixed positive exponential rate in any growing dimension parameter
gives the exact target once the finite configurations have been constructed. -/
theorem target_of_eventual_exponential_graphs (d : ℕ → ℝ)
    (hd : Tendsto d atTop atTop) {η c : ℝ} (hη : 0 < η) (hc : 0 < c)
    (hU : ∀ᶠ j in atTop, ∃ U : Finset ℂ,
      Real.exp (d j*η)/c ≤ unitPairs U/(U.card : ℝ)^exponent) : Target := by
  apply target_of_eventual_ratio_bounds _ _ hU
  exact (Real.tendsto_exp_atTop.comp (hd.atTop_mul_const hη)).atTop_div_const hc

end UnitDistance
