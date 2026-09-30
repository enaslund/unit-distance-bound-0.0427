module

public import UnitDistance.PairMassDegree12Data
public import UnitDistance.RationalPowerBounds

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
namespace UnitDistance.Witness

private theorem pairMassCenter_log_0_0 :
    (403326577010026101 : ℝ) / 1000000000000000000 ≤ Real.log ((784751987730939 : ℝ) / 524288000000000) ∧
    Real.log ((784751987730939 : ℝ) / 524288000000000) ≤ (403326577010026103 : ℝ) / 1000000000000000000 := by
  have hb : (40332657701002610183 : ℝ) / 100000000000000000000 ≤ Real.log ((59871825235819931 : ℝ) / 40000000000000000) ∧
      Real.log ((59871825235819931 : ℝ) / 40000000000000000) ≤ (5041582212625326273 : ℝ) / 12500000000000000000 := by
    apply log_enclosure ((59871825235819931 : ℝ) / 40000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (784751987730939 : ℝ) / 524288000000000) (l := (59871825235819931 : ℝ) / 40000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((784751987730939 : ℝ) / 524288000000000) ((784751987730939 : ℝ) / 524288000000000) (0) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_0_0 :
    (619416362959799 : ℝ) / 800000000000000 ≤ Real.log ((43380183144457 : ℝ) / 20000000000000) ∧
    Real.log ((43380183144457 : ℝ) / 20000000000000) ≤ (48391903356234297 : ℝ) / 62500000000000000 := by
  have hb : (8112327313980344141 : ℝ) / 100000000000000000000 ≤ Real.log ((43380183144457 : ℝ) / 40000000000000) ∧
      Real.log ((43380183144457 : ℝ) / 40000000000000) ≤ (4056163656990172071 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((43380183144457 : ℝ) / 40000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (43380183144457 : ℝ) / 40000000000000) (l := (43380183144457 : ℝ) / 40000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((43380183144457 : ℝ) / 20000000000000) ((43380183144457 : ℝ) / 40000000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_0_0 :
    pairMassCellCenter ⟨0, by decide⟩ ⟨0, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨0, by decide⟩ ⟨0, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (784751987730939 : ℝ) / 524288000000000)
    (by norm_num : 0 < (43380183144457 : ℝ) / 20000000000000) (by norm_num [p, increment])
    pairMassCenter_log_0_0.2 pairMassPowerUpper_log_0_0.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_0_1 :
    (680307579304502777 : ℝ) / 1000000000000000000 ≤ Real.log ((129399845653673 : ℝ) / 65536000000000) ∧
    Real.log ((129399845653673 : ℝ) / 65536000000000) ≤ (680307579304502779 : ℝ) / 1000000000000000000 := by
  have hb : (13606151586090055557 : ℝ) / 20000000000000000000 ≤ Real.log ((394896989909890747 : ℝ) / 200000000000000000) ∧
      Real.log ((394896989909890747 : ℝ) / 200000000000000000) ≤ (34015378965225138893 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((394896989909890747 : ℝ) / 200000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (129399845653673 : ℝ) / 65536000000000) (l := (394896989909890747 : ℝ) / 200000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((129399845653673 : ℝ) / 65536000000000) ((129399845653673 : ℝ) / 65536000000000) (0) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_0_1 :
    (326498480454945157 : ℝ) / 250000000000000000 ≤ Real.log ((369135619046167 : ℝ) / 100000000000000) ∧
    Real.log ((369135619046167 : ℝ) / 100000000000000) ≤ (130599392181978063 : ℝ) / 100000000000000000 := by
  have hb : (15321168531495882981 : ℝ) / 25000000000000000000 ≤ Real.log ((369135619046167 : ℝ) / 200000000000000) ∧
      Real.log ((369135619046167 : ℝ) / 200000000000000) ≤ (2451386965039341277 : ℝ) / 4000000000000000000 := by
    apply log_enclosure ((369135619046167 : ℝ) / 200000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (369135619046167 : ℝ) / 200000000000000) (l := (369135619046167 : ℝ) / 200000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((369135619046167 : ℝ) / 100000000000000) ((369135619046167 : ℝ) / 200000000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_0_1 :
    pairMassCellCenter ⟨0, by decide⟩ ⟨1, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (129399845653673 : ℝ) / 65536000000000)
    (by norm_num : 0 < (369135619046167 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_0_1.2 pairMassPowerUpper_log_0_1.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_0_2 :
    (445074816701449799 : ℝ) / 500000000000000000 ≤ Real.log ((6384501536296597 : ℝ) / 2621440000000000) ∧
    Real.log ((6384501536296597 : ℝ) / 2621440000000000) ≤ (2225374083507249 : ℝ) / 2500000000000000 := by
  have hb : (19700245284295428927 : ℝ) / 100000000000000000000 ≤ Real.log ((1217747027644462013 : ℝ) / 1000000000000000000) ∧
      Real.log ((1217747027644462013 : ℝ) / 1000000000000000000) ≤ (307816332567116077 : ℝ) / 1562500000000000000 := by
    apply log_enclosure ((1217747027644462013 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (6384501536296597 : ℝ) / 5242880000000000) (l := (1217747027644462013 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((6384501536296597 : ℝ) / 2621440000000000) ((6384501536296597 : ℝ) / 5242880000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_0_2 :
    (1708830014686558589 : ℝ) / 1000000000000000000 ≤ Real.log ((552249645662389 : ℝ) / 100000000000000) ∧
    Real.log ((552249645662389 : ℝ) / 100000000000000) ≤ (170883001468655859 : ℝ) / 100000000000000000 := by
  have hb : (32253565356666797029 : ℝ) / 100000000000000000000 ≤ Real.log ((552249645662389 : ℝ) / 400000000000000) ∧
      Real.log ((552249645662389 : ℝ) / 400000000000000) ≤ (3225356535666679703 : ℝ) / 10000000000000000000 := by
    apply log_enclosure ((552249645662389 : ℝ) / 400000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (552249645662389 : ℝ) / 400000000000000) (l := (552249645662389 : ℝ) / 400000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((552249645662389 : ℝ) / 100000000000000) ((552249645662389 : ℝ) / 400000000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_0_2 :
    pairMassCellCenter ⟨0, by decide⟩ ⟨2, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨0, by decide⟩ ⟨2, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (6384501536296597 : ℝ) / 2621440000000000)
    (by norm_num : 0 < (552249645662389 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_0_2.2 pairMassPowerUpper_log_0_2.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_0_3 :
    (1075562540554841109 : ℝ) / 1000000000000000000 ≤ Real.log ((12008004010203 : ℝ) / 4096000000000) ∧
    Real.log ((12008004010203 : ℝ) / 4096000000000) ≤ (107556254055484111 : ℝ) / 100000000000000000 := by
  have hb : (38241535999489579963 : ℝ) / 100000000000000000000 ≤ Real.log ((732910401013366699 : ℝ) / 500000000000000000) ∧
      Real.log ((732910401013366699 : ℝ) / 500000000000000000) ≤ (9560383999872394991 : ℝ) / 25000000000000000000 := by
    apply log_enclosure ((732910401013366699 : ℝ) / 500000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (12008004010203 : ℝ) / 8192000000000) (l := (732910401013366699 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((12008004010203 : ℝ) / 4096000000000) ((12008004010203 : ℝ) / 8192000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_0_3 :
    (2064769206213609721 : ℝ) / 1000000000000000000 ≤ Real.log ((788347822988837 : ℝ) / 100000000000000) ∧
    Real.log ((788347822988837 : ℝ) / 100000000000000) ≤ (2064769206213609723 : ℝ) / 1000000000000000000 := by
  have hb : (8480935563671488787 : ℝ) / 12500000000000000000 ≤ Real.log ((788347822988837 : ℝ) / 400000000000000) ∧
      Real.log ((788347822988837 : ℝ) / 400000000000000) ≤ (67847484509371910297 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((788347822988837 : ℝ) / 400000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (788347822988837 : ℝ) / 400000000000000) (l := (788347822988837 : ℝ) / 400000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((788347822988837 : ℝ) / 100000000000000) ((788347822988837 : ℝ) / 400000000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_0_3 :
    pairMassCellCenter ⟨0, by decide⟩ ⟨3, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨0, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (12008004010203 : ℝ) / 4096000000000)
    (by norm_num : 0 < (788347822988837 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_0_3.2 pairMassPowerUpper_log_0_3.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_0_4 :
    (1256967332552285043 : ℝ) / 1000000000000000000 ≤ Real.log ((9213696414273083 : ℝ) / 2621440000000000) ∧
    Real.log ((9213696414273083 : ℝ) / 2621440000000000) ≤ (314241833138071261 : ℝ) / 250000000000000000 := by
  have hb : (56382015199233973377 : ℝ) / 100000000000000000000 ≤ Real.log ((1757373125891319847 : ℝ) / 1000000000000000000) ∧
      Real.log ((1757373125891319847 : ℝ) / 1000000000000000000) ≤ (28191007599616986689 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((1757373125891319847 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (9213696414273083 : ℝ) / 5242880000000000) (l := (1757373125891319847 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((9213696414273083 : ℝ) / 2621440000000000) ((9213696414273083 : ℝ) / 5242880000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_0_4 :
    (2356458960074507 : ℝ) / 976562500000000 ≤ Real.log ((1116756924845453 : ℝ) / 100000000000000) ∧
    Real.log ((1116756924845453 : ℝ) / 100000000000000) ≤ (241301397511629517 : ℝ) / 100000000000000000 := by
  have hb : (33357243343645924027 : ℝ) / 100000000000000000000 ≤ Real.log ((1116756924845453 : ℝ) / 800000000000000) ∧
      Real.log ((1116756924845453 : ℝ) / 800000000000000) ≤ (8339310835911481007 : ℝ) / 25000000000000000000 := by
    apply log_enclosure ((1116756924845453 : ℝ) / 800000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (1116756924845453 : ℝ) / 800000000000000) (l := (1116756924845453 : ℝ) / 800000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1116756924845453 : ℝ) / 100000000000000) ((1116756924845453 : ℝ) / 800000000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_0_4 :
    pairMassCellCenter ⟨0, by decide⟩ ⟨4, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨0, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (9213696414273083 : ℝ) / 2621440000000000)
    (by norm_num : 0 < (1116756924845453 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_0_4.2 pairMassPowerUpper_log_0_4.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_0_5 :
    (1443767352212337757 : ℝ) / 1000000000000000000 ≤ Real.log ((277651564423807 : ℝ) / 65536000000000) ∧
    Real.log ((277651564423807 : ℝ) / 65536000000000) ≤ (1443767352212337759 : ℝ) / 1000000000000000000 := by
  have hb : (5747299109244713911 : ℝ) / 100000000000000000000 ≤ Real.log ((1059156663604000091 : ℝ) / 1000000000000000000) ∧
      Real.log ((1059156663604000091 : ℝ) / 1000000000000000000) ≤ (718412388655589239 : ℝ) / 12500000000000000000 := by
    apply log_enclosure ((1059156663604000091 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (277651564423807 : ℝ) / 262144000000000) (l := (1059156663604000091 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((277651564423807 : ℝ) / 65536000000000) ((277651564423807 : ℝ) / 262144000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_0_5 :
    (2771616021739456561 : ℝ) / 1000000000000000000 ≤ Real.log ((1598444435871133 : ℝ) / 100000000000000) ∧
    Real.log ((1598444435871133 : ℝ) / 100000000000000) ≤ (2771616021739456563 : ℝ) / 1000000000000000000 := by
  have hb : (17304362001490515833 : ℝ) / 25000000000000000000 ≤ Real.log ((1598444435871133 : ℝ) / 800000000000000) ∧
      Real.log ((1598444435871133 : ℝ) / 800000000000000) ≤ (69217448005962063333 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1598444435871133 : ℝ) / 800000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (1598444435871133 : ℝ) / 800000000000000) (l := (1598444435871133 : ℝ) / 800000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1598444435871133 : ℝ) / 100000000000000) ((1598444435871133 : ℝ) / 800000000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_0_5 :
    pairMassCellCenter ⟨0, by decide⟩ ⟨5, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨0, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (277651564423807 : ℝ) / 65536000000000)
    (by norm_num : 0 < (1598444435871133 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_0_5.2 pairMassPowerUpper_log_0_5.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_0_6 :
    (1638822227199824797 : ℝ) / 1000000000000000000 ≤ Real.log ((2699612110398741 : ℝ) / 524288000000000) ∧
    Real.log ((2699612110398741 : ℝ) / 524288000000000) ≤ (1638822227199824799 : ℝ) / 1000000000000000000 := by
  have hb : (1578299162999588619 : ℝ) / 6250000000000000000 ≤ Real.log ((257455073394655323 : ℝ) / 200000000000000000) ∧
      Real.log ((257455073394655323 : ℝ) / 200000000000000000) ≤ (5050557321598683581 : ℝ) / 20000000000000000000 := by
    apply log_enclosure ((257455073394655323 : ℝ) / 200000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (2699612110398741 : ℝ) / 2097152000000000) (l := (257455073394655323 : ℝ) / 200000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2699612110398741 : ℝ) / 524288000000000) ((2699612110398741 : ℝ) / 2097152000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_0_6 :
    (3146065004676560181 : ℝ) / 1000000000000000000 ≤ Real.log ((2324441770921147 : ℝ) / 100000000000000) ∧
    Real.log ((2324441770921147 : ℝ) / 100000000000000) ≤ (3146065004676560183 : ℝ) / 1000000000000000000 := by
  have hb : (37347628243677894427 : ℝ) / 100000000000000000000 ≤ Real.log ((2324441770921147 : ℝ) / 1600000000000000) ∧
      Real.log ((2324441770921147 : ℝ) / 1600000000000000) ≤ (9336907060919473607 : ℝ) / 25000000000000000000 := by
    apply log_enclosure ((2324441770921147 : ℝ) / 1600000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (2324441770921147 : ℝ) / 1600000000000000) (l := (2324441770921147 : ℝ) / 1600000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2324441770921147 : ℝ) / 100000000000000) ((2324441770921147 : ℝ) / 1600000000000000) (4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_0_6 :
    pairMassCellCenter ⟨0, by decide⟩ ⟨6, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨0, by decide⟩ ⟨6, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (2699612110398741 : ℝ) / 524288000000000)
    (by norm_num : 0 < (2324441770921147 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_0_6.2 pairMassPowerUpper_log_0_6.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_0_7 :
    (920591331428845189 : ℝ) / 500000000000000000 ≤ Real.log ((16138212731273 : ℝ) / 2560000000000) ∧
    Real.log ((16138212731273 : ℝ) / 2560000000000) ≤ (1841182662857690379 : ℝ) / 1000000000000000000 := by
  have hb : (5686103771722496991 : ℝ) / 12500000000000000000 ≤ Real.log ((787998668519189453 : ℝ) / 500000000000000000) ∧
      Real.log ((787998668519189453 : ℝ) / 500000000000000000) ≤ (45488830173779975929 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((787998668519189453 : ℝ) / 500000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (16138212731273 : ℝ) / 10240000000000) (l := (787998668519189453 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((16138212731273 : ℝ) / 2560000000000) ((16138212731273 : ℝ) / 10240000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_0_7 :
    (1767269276281146097 : ℝ) / 500000000000000000 ≤ Real.log ((3427919301828409 : ℝ) / 100000000000000) ∧
    Real.log ((3427919301828409 : ℝ) / 100000000000000) ≤ (883634638140573049 : ℝ) / 250000000000000000 := by
  have hb : (6880264976256564743 : ℝ) / 100000000000000000000 ≤ Real.log ((267806195455344453 : ℝ) / 250000000000000000) ∧
      Real.log ((267806195455344453 : ℝ) / 250000000000000000) ≤ (860033122032070593 : ℝ) / 12500000000000000000 := by
    apply log_enclosure ((267806195455344453 : ℝ) / 250000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (3427919301828409 : ℝ) / 3200000000000000) (l := (267806195455344453 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((3427919301828409 : ℝ) / 100000000000000) ((3427919301828409 : ℝ) / 3200000000000000) (5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_0_7 :
    pairMassCellCenter ⟨0, by decide⟩ ⟨7, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨0, by decide⟩ ⟨7, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (16138212731273 : ℝ) / 2560000000000)
    (by norm_num : 0 < (3427919301828409 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_0_7.2 pairMassPowerUpper_log_0_7.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

end UnitDistance.Witness
