module

public import UnitDistance.PadicTwoSquareclasses

@[expose] public section
set_option backward.privateInPublic true


/-! The genuine norm obstruction preventing a cyclic quartic lift of the
Q₂(i) character. The proof clears a largest-norm coordinate and reduces
three squares modulo eight. -/
noncomputable section
namespace UnitDistance.PadicTwo
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem residue_two_squares : ∀ a b : ZMod 8,a^2+b^2+1≠0 := by decide +kernel

theorem int_sum_squares_add_one_ne_zero (a b : ℤ_[2]) : a^2+b^2+1≠0 := by
  intro h
  have he := congrArg residue8 h
  simp only [map_add,map_pow,map_one,map_zero] at he
  exact residue_two_squares (residue8 a) (residue8 b) he

private theorem normalized_sum_squares (a b : ℚ_[2])
    (ha : ‖a‖≤1) (hb : ‖b‖≤1) : a^2+b^2+1≠0 := by
  intro h
  apply int_sum_squares_add_one_ne_zero (⟨a,ha⟩ : ℤ_[2]) (⟨b,hb⟩ : ℤ_[2])
  apply PadicInt.ext
  exact h

/-- Minus one is not a sum of two actual 2-adic squares. -/
theorem sum_squares_ne_neg_one (x y : ℚ_[2]) : x^2+y^2≠ -1 := by
  intro h
  have hsum : x^2+y^2+1=0 := by linear_combination h
  by_cases hx : ‖x‖≤1
  · by_cases hy : ‖y‖≤1
    · exact normalized_sum_squares x y hx hy hsum
    · have hy' : 1<‖y‖ := lt_of_not_ge hy
      have hy0 : y≠0 := norm_pos_iff.mp (lt_trans zero_lt_one hy')
      have hxy : ‖x/y‖≤1 := by
        rw [norm_div,div_le_one (norm_pos_iff.mpr hy0)]
        exact hx.trans hy'.le
      have hyinv : ‖1/y‖≤1 := by
        rw [norm_div,norm_one,div_le_one (norm_pos_iff.mpr hy0)]
        exact hy'.le
      apply normalized_sum_squares (x/y) (1/y) hxy hyinv
      field_simp
      linear_combination hsum
  · have hx' : 1<‖x‖ := lt_of_not_ge hx
    by_cases hyx : ‖y‖≤‖x‖
    · have hx0 : x≠0 := norm_pos_iff.mp (lt_trans zero_lt_one hx')
      have hydiv : ‖y/x‖≤1 := by
        rw [norm_div,div_le_one (norm_pos_iff.mpr hx0)]
        exact hyx
      have hxinv : ‖1/x‖≤1 := by
        rw [norm_div,norm_one,div_le_one (norm_pos_iff.mpr hx0)]
        exact hx'.le
      apply normalized_sum_squares (y/x) (1/x) hydiv hxinv
      field_simp
      linear_combination hsum
    · have hy' : 1<‖y‖ := hx'.trans (lt_of_not_ge hyx)
      have hy0 : y≠0 := norm_pos_iff.mp (lt_trans zero_lt_one hy')
      have hxy : ‖x/y‖≤1 := by
        rw [norm_div,div_le_one (norm_pos_iff.mpr hy0)]
        exact (lt_of_not_ge hyx).le
      have hyinv : ‖1/y‖≤1 := by
        rw [norm_div,norm_one,div_le_one (norm_pos_iff.mpr hy0)]
        exact hy'.le
      apply normalized_sum_squares (x/y) (1/y) hxy hyinv
      field_simp
      linear_combination hsum

end UnitDistance.PadicTwo
