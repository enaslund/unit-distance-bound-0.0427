module

public import UnitDistance.PairMassDegree12Data
public import UnitDistance.RationalPowerBounds

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
namespace UnitDistance.Witness

private theorem pairMassCenter_log_3_3 :
    (1524459113592535741 : ℝ) / 1000000000000000000 ≤ Real.log ((2407875892038483 : ℝ) / 524288000000000) ∧
    Real.log ((2407875892038483 : ℝ) / 524288000000000) ≤ (1524459113592535743 : ℝ) / 1000000000000000000 := by
  have hb : (6908237623632256153 : ℝ) / 50000000000000000000 ≤ Real.log ((22963293953308897 : ℝ) / 20000000000000000) ∧
      Real.log ((22963293953308897 : ℝ) / 20000000000000000) ≤ (13816475247264512307 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((22963293953308897 : ℝ) / 20000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (2407875892038483 : ℝ) / 2097152000000000) (l := (22963293953308897 : ℝ) / 20000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2407875892038483 : ℝ) / 524288000000000) ((2407875892038483 : ℝ) / 2097152000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_3_3 :
    (2926520881113809167 : ℝ) / 1000000000000000000 ≤ Real.log ((1866258805452037 : ℝ) / 100000000000000) ∧
    Real.log ((1866258805452037 : ℝ) / 100000000000000) ≤ (2926520881113809169 : ℝ) / 1000000000000000000 := by
  have hb : (1539321588740279299 : ℝ) / 10000000000000000000 ≤ Real.log ((1866258805452037 : ℝ) / 1600000000000000) ∧
      Real.log ((1866258805452037 : ℝ) / 1600000000000000) ≤ (15393215887402792991 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1866258805452037 : ℝ) / 1600000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (1866258805452037 : ℝ) / 1600000000000000) (l := (1866258805452037 : ℝ) / 1600000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1866258805452037 : ℝ) / 100000000000000) ((1866258805452037 : ℝ) / 1600000000000000) (4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_3_3 :
    pairMassCellCenter ⟨3, by decide⟩ ⟨3, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨3, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (2407875892038483 : ℝ) / 524288000000000)
    (by norm_num : 0 < (1866258805452037 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_3_3.2 pairMassPowerUpper_log_3_3.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_3_4 :
    (165872661014565049 : ℝ) / 100000000000000000 ≤ Real.log ((26893403922487 : ℝ) / 5120000000000) ∧
    Real.log ((26893403922487 : ℝ) / 5120000000000) ≤ (414681652536412623 : ℝ) / 250000000000000000 := by
  have hb : (13621612451287993603 : ℝ) / 50000000000000000000 ≤ Real.log ((656577244201342773 : ℝ) / 500000000000000000) ∧
      Real.log ((656577244201342773 : ℝ) / 500000000000000000) ≤ (27243224902575987207 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((656577244201342773 : ℝ) / 500000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (26893403922487 : ℝ) / 20480000000000) (l := (656577244201342773 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((26893403922487 : ℝ) / 5120000000000) ((26893403922487 : ℝ) / 20480000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_3_4 :
    (159213783346761793 : ℝ) / 50000000000000000 ≤ Real.log ((150936184862637 : ℝ) / 6250000000000) ∧
    Real.log ((150936184862637 : ℝ) / 6250000000000) ≤ (1592137833467617931 : ℝ) / 500000000000000000 := by
  have hb : (4116869446954546233 : ℝ) / 10000000000000000000 ≤ Real.log ((150936184862637 : ℝ) / 100000000000000) ∧
      Real.log ((150936184862637 : ℝ) / 100000000000000) ≤ (41168694469545462331 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((150936184862637 : ℝ) / 100000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (150936184862637 : ℝ) / 100000000000000) (l := (150936184862637 : ℝ) / 100000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((150936184862637 : ℝ) / 6250000000000) ((150936184862637 : ℝ) / 100000000000000) (4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_3_4 :
    pairMassCellCenter ⟨3, by decide⟩ ⟨4, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨3, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (26893403922487 : ℝ) / 5120000000000)
    (by norm_num : 0 < (150936184862637 : ℝ) / 6250000000000) (by norm_num [p, increment])
    pairMassCenter_log_3_4.2 pairMassPowerUpper_log_3_4.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_3_5 :
    (1798569899578543601 : ℝ) / 1000000000000000000 ≤ Real.log ((633444975971641 : ℝ) / 104857600000000) ∧
    Real.log ((633444975971641 : ℝ) / 104857600000000) ≤ (1798569899578543603 : ℝ) / 1000000000000000000 := by
  have hb : (322090264420822643 : ℝ) / 781250000000000000 ≤ Real.log ((377562627775455117 : ℝ) / 250000000000000000) ∧
      Real.log ((377562627775455117 : ℝ) / 250000000000000000) ≤ (8245510769173059661 : ℝ) / 20000000000000000000 := by
    apply log_enclosure ((377562627775455117 : ℝ) / 250000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (633444975971641 : ℝ) / 419430400000000) (l := (377562627775455117 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((633444975971641 : ℝ) / 104857600000000) ((633444975971641 : ℝ) / 419430400000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_3_5 :
    (863183590876258741 : ℝ) / 250000000000000000 ≤ Real.log ((3158664369945881 : ℝ) / 100000000000000) ∧
    Real.log ((3158664369945881 : ℝ) / 100000000000000) ≤ (690546872701006993 : ℝ) / 200000000000000000 := by
  have hb : (68014564126525372643 : ℝ) / 100000000000000000000 ≤ Real.log ((3158664369945881 : ℝ) / 1600000000000000) ∧
      Real.log ((3158664369945881 : ℝ) / 1600000000000000) ≤ (17003641031631343161 : ℝ) / 25000000000000000000 := by
    apply log_enclosure ((3158664369945881 : ℝ) / 1600000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (3158664369945881 : ℝ) / 1600000000000000) (l := (3158664369945881 : ℝ) / 1600000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((3158664369945881 : ℝ) / 100000000000000) ((3158664369945881 : ℝ) / 1600000000000000) (4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_3_5 :
    pairMassCellCenter ⟨3, by decide⟩ ⟨5, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨3, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (633444975971641 : ℝ) / 104857600000000)
    (by norm_num : 0 < (3158664369945881 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_3_5.2 pairMassPowerUpper_log_3_5.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_3_6 :
    (1946335771256202023 : ℝ) / 1000000000000000000 ≤ Real.log ((458947296594237 : ℝ) / 65536000000000) ∧
    Real.log ((458947296594237 : ℝ) / 65536000000000) ≤ (77853430850248081 : ℝ) / 40000000000000000 := by
  have hb : (28002070506815570251 : ℝ) / 50000000000000000000 ≤ Real.log ((1750744997384021759 : ℝ) / 1000000000000000000) ∧
      Real.log ((1750744997384021759 : ℝ) / 1000000000000000000) ≤ (56004141013631140503 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1750744997384021759 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (458947296594237 : ℝ) / 262144000000000) (l := (1750744997384021759 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((458947296594237 : ℝ) / 65536000000000) ((458947296594237 : ℝ) / 262144000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_3_6 :
    (149456085124300017 : ℝ) / 40000000000000000 ≤ Real.log ((4194679913552249 : ℝ) / 100000000000000) ∧
    Real.log ((4194679913552249 : ℝ) / 100000000000000) ≤ (3736402128107500427 : ℝ) / 1000000000000000000 := by
  have hb : (27066622530777387817 : ℝ) / 100000000000000000000 ≤ Real.log ((327709368246269453 : ℝ) / 250000000000000000) ∧
      Real.log ((327709368246269453 : ℝ) / 250000000000000000) ≤ (13533311265388693909 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((327709368246269453 : ℝ) / 250000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (4194679913552249 : ℝ) / 3200000000000000) (l := (327709368246269453 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((4194679913552249 : ℝ) / 100000000000000) ((4194679913552249 : ℝ) / 3200000000000000) (5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_3_6 :
    pairMassCellCenter ⟨3, by decide⟩ ⟨6, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨3, by decide⟩ ⟨6, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (458947296594237 : ℝ) / 65536000000000)
    (by norm_num : 0 < (4194679913552249 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_3_6.2 pairMassPowerUpper_log_3_6.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_3_7 :
    (84085876095710803 : ℝ) / 40000000000000000 ≤ Real.log ((21453132832392731 : ℝ) / 2621440000000000) ∧
    Real.log ((21453132832392731 : ℝ) / 2621440000000000) ≤ (2102146902392770077 : ℝ) / 1000000000000000000 := by
  have hb : (454107214258682937 : ℝ) / 20000000000000000000 ≤ Real.log ((1022965089435230779 : ℝ) / 1000000000000000000) ∧
      Real.log ((1022965089435230779 : ℝ) / 1000000000000000000) ≤ (1135268035646707343 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((1022965089435230779 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (21453132832392731 : ℝ) / 20971520000000000) (l := (1022965089435230779 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((21453132832392731 : ℝ) / 2621440000000000) ((21453132832392731 : ℝ) / 20971520000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_3_7 :
    (2017757232768093797 : ℝ) / 500000000000000000 ≤ Real.log ((1414300427653177 : ℝ) / 25000000000000) ∧
    Real.log ((1414300427653177 : ℝ) / 25000000000000) ≤ (1008878616384046899 : ℝ) / 250000000000000000 := by
  have hb : (28488928136823052389 : ℝ) / 50000000000000000000 ≤ Real.log ((1414300427653177 : ℝ) / 800000000000000) ∧
      Real.log ((1414300427653177 : ℝ) / 800000000000000) ≤ (56977856273646104779 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1414300427653177 : ℝ) / 800000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (1414300427653177 : ℝ) / 800000000000000) (l := (1414300427653177 : ℝ) / 800000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1414300427653177 : ℝ) / 25000000000000) ((1414300427653177 : ℝ) / 800000000000000) (5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_3_7 :
    pairMassCellCenter ⟨3, by decide⟩ ⟨7, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨3, by decide⟩ ⟨7, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (21453132832392731 : ℝ) / 2621440000000000)
    (by norm_num : 0 < (1414300427653177 : ℝ) / 25000000000000) (by norm_num [p, increment])
    pairMassCenter_log_3_7.2 pairMassPowerUpper_log_3_7.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

end UnitDistance.Witness
