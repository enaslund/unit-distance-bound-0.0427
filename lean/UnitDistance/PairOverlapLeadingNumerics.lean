module

public import UnitDistance.PairOverlapLeadingCollection
public import UnitDistance.PairFunctionalCertificate

@[expose] public section
set_option backward.privateInPublic true


/-! A rational lower bound for the averaged leading overlap term. -/
noncomputable section
namespace UnitDistance.Witness

private theorem log_a_reduced_upper :
    Real.log ((257266483516 : ℝ) / 152587890625) ≤
      (52237168652613924670 : ℝ) / 10^20 := by
  exact (log_enclosure ((257266483516 : ℝ) / 152587890625) 25 (by norm_num)
    ((52237168652613924669 : ℝ) / 10^20)
    ((52237168652613924670 : ℝ) / 10^20)
    (by norm_num [Finset.sum_range_succ])
    (by norm_num [Finset.sum_range_succ])).2

theorem log_inverse_a_lower :
    (1126113038299293 : ℝ) / 10^14 ≤ Real.log (1/a) := by
  have h2 := log_two_precise
  simp only [div_one] at h2
  have hs := log_scale_two a ((257266483516 : ℝ) / 152587890625) (-17)
    (by norm_num) (by norm_num [a])
  rw [one_div, Real.log_inv, hs]
  norm_num
  linarith [log_a_reduced_upper, h2.1]

theorem pairOverlapLeadingNumerical_lower :
    (3484186894 : ℝ) / 10^7 ≤
      (pairOverlapB0 : ℝ) * (Real.log (1/a) + pairOverlapStudentConstant) +
        (pairOverlapV0 : ℝ) := by
  have hsum := add_le_add log_inverse_a_lower pairOverlapStudentConstant_lower
  have hb : 0 ≤ (pairOverlapB0 : ℝ) := by exact_mod_cast pairOverlapB0_pos.le
  have hm := mul_le_mul_of_nonneg_left hsum hb
  have hh := add_le_add_right hm (pairOverlapV0 : ℝ)
  refine le_trans ?_ (by simpa only [add_comm] using hh)
  rw [pairOverlapB0_exact, pairOverlapV0_exact]
  norm_num

end UnitDistance.Witness
