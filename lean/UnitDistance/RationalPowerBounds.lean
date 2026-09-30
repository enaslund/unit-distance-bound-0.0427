module

public import UnitDistance.LogBounds

@[expose] public section
set_option backward.privateInPublic true


/-! # Sound rational-power checking through ordinary logarithms -/

namespace UnitDistance

theorem log_bounds_of_lower {x l ε lo hi : ℝ} (hl : 0 < l) (hxl : l ≤ x)
    (hxu : x ≤ l+ε) (hlog : lo ≤ Real.log l ∧ Real.log l ≤ hi) :
    lo ≤ Real.log x ∧ Real.log x ≤ hi+ε/l := by
  have hx := hl.trans_le hxl
  have hupper := Real.log_le_sub_one_of_pos (div_pos hx hl)
  rw [Real.log_div hx.ne' hl.ne'] at hupper
  have hdiv : x/l-1 ≤ ε/l := by
    calc
      x/l-1 = (x-l)/l := by field_simp
      _ ≤ ε/l := div_le_div_of_nonneg_right (by linarith) hl.le
  exact ⟨hlog.1.trans (Real.log_le_log hl hxl), by linarith [hlog.2]⟩

theorem log_scale_two (q r : ℝ) (k : ℤ) (hr : 0 < r) (hq : q = 2^k*r) :
    Real.log q = (k : ℝ)*Real.log 2 + Real.log r := by
  rw [hq, Real.log_mul (zpow_ne_zero _ (by norm_num)) hr.ne', Real.log_zpow]

theorem rpow_le_of_log_bounds {w u p a b : ℝ} (hw : 0 < w) (hu : 0 < u)
    (hp : 0 ≤ p) (hlogw : Real.log w ≤ a) (hlogu : b ≤ Real.log u)
    (hbound : p*a ≤ b) : w^p ≤ u := by
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hw _) hu).mp
  rw [Real.log_rpow hw]
  exact (mul_le_mul_of_nonneg_left hlogw hp).trans (hbound.trans hlogu)

end UnitDistance
