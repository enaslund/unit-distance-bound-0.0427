module

public import UnitDistance.FiniteCertificates.LogEnclosureCompactRun20260920

@[expose] public section
set_option backward.privateInPublic true


namespace UnitDistance.Witness.FiniteCertificates

theorem power_bound_3_0 :
    (shellWeights ⟨3, by decide⟩ ⟨0, by decide⟩ : ℝ)^p ≤ powerUpper ⟨3, by decide⟩ ⟨0, by decide⟩ := by
  norm_num [shellWeights, powerUpper, Matrix.cons_val]

theorem weight_log_3_1 :
    (-84263407089833511 : ℝ) / 10000000000000000 ≤ Real.log ((5475537228781 : ℝ) / 25000000000000000) ∧
    Real.log ((5475537228781 : ℝ) / 25000000000000000) ≤ (-4213170354491675549 : ℝ) / 500000000000000000 := by
  have hb : (58457263829593792341 : ℝ) / 100000000000000000000 ≤ Real.log ((5475537228781 : ℝ) / 3051757812500) ∧
      Real.log ((5475537228781 : ℝ) / 3051757812500) ≤ (29228631914796896171 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((5475537228781 : ℚ) / 3051757812500) 25
      ((58457263829593792341 : ℚ) / 100000000000000000000)
      ((29228631914796896171 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (5475537228781 : ℝ) / 3051757812500) (l := (5475537228781 : ℝ) / 3051757812500)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((5475537228781 : ℝ) / 25000000000000000) ((5475537228781 : ℝ) / 3051757812500) (-13) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_3_1 :
    (-16176138681808001073 : ℝ) / 1000000000000000000 ≤ Real.log ((94360934225140269 : ℝ) / 1000000000000000000000000) ∧
    Real.log ((94360934225140269 : ℝ) / 1000000000000000000000000) ≤ (-16176138681808001071 : ℝ) / 1000000000000000000 := by
  have hb : (22969682581534317677 : ℝ) / 50000000000000000000 ≤ Real.log ((1583113775456970923 : ℝ) / 1000000000000000000) ∧
      Real.log ((1583113775456970923 : ℝ) / 1000000000000000000) ≤ (9187873032613727071 : ℝ) / 20000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1583113775456970923 : ℚ) / 1000000000000000000) 25
      ((22969682581534317677 : ℚ) / 50000000000000000000)
      ((9187873032613727071 : ℚ) / 20000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (94360934225140269 : ℝ) / 59604644775390625) (l := (1583113775456970923 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((94360934225140269 : ℝ) / 1000000000000000000000000) ((94360934225140269 : ℝ) / 59604644775390625) (-24) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_3_1 :
    (shellWeights ⟨3, by decide⟩ ⟨1, by decide⟩ : ℝ)^p ≤ powerUpper ⟨3, by decide⟩ ⟨1, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (5475537228781 : ℝ) / 25000000000000000)
    (by norm_num : 0 < (94360934225140269 : ℝ) / 1000000000000000000000000) witness_basic.2.2.1.le
    weight_log_3_1.2 power_upper_log_3_1.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_3_2 :
    (-17062571938586218329 : ℝ) / 1000000000000000000 ≤ Real.log ((243051987821 : ℝ) / 6250000000000000000) ∧
    Real.log ((243051987821 : ℝ) / 6250000000000000000) ≤ (-17062571938586218327 : ℝ) / 1000000000000000000 := by
  have hb : (26610757541241440663 : ℝ) / 100000000000000000000 ≤ Real.log ((1304875423648731627 : ℝ) / 1000000000000000000) ∧
      Real.log ((1304875423648731627 : ℝ) / 1000000000000000000) ≤ (3326344692655180083 : ℝ) / 12500000000000000000 := by
    have h := log_enclosure_of_rat
      ((1304875423648731627 : ℚ) / 1000000000000000000) 25
      ((26610757541241440663 : ℚ) / 100000000000000000000)
      ((3326344692655180083 : ℚ) / 12500000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (124442617764352 : ℝ) / 95367431640625) (l := (1304875423648731627 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((243051987821 : ℝ) / 6250000000000000000) ((124442617764352 : ℝ) / 95367431640625) (-25) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_3_2 :
    (-32755206498195070913 : ℝ) / 1000000000000000000 ≤ Real.log ((59510632240746513 : ℝ) / 10000000000000000000000000000000) ∧
    Real.log ((59510632240746513 : ℝ) / 10000000000000000000000000000000) ≤ (-32755206498195070911 : ℝ) / 1000000000000000000 := by
  have hb : (51585816868230393927 : ℝ) / 100000000000000000000 ≤ Real.log ((1675075382400053883 : ℝ) / 1000000000000000000) ∧
      Real.log ((1675075382400053883 : ℝ) / 1000000000000000000) ≤ (6448227108528799241 : ℝ) / 12500000000000000000 := by
    have h := log_enclosure_of_rat
      ((1675075382400053883 : ℚ) / 1000000000000000000) 25
      ((51585816868230393927 : ℚ) / 100000000000000000000)
      ((6448227108528799241 : ℚ) / 12500000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (7800177589059126951936 : ℝ) / 4656612873077392578125) (l := (1675075382400053883 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((59510632240746513 : ℝ) / 10000000000000000000000000000000) ((7800177589059126951936 : ℝ) / 4656612873077392578125) (-48) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_3_2 :
    (shellWeights ⟨3, by decide⟩ ⟨2, by decide⟩ : ℝ)^p ≤ powerUpper ⟨3, by decide⟩ ⟨2, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (243051987821 : ℝ) / 6250000000000000000)
    (by norm_num : 0 < (59510632240746513 : ℝ) / 10000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_3_2.2 power_upper_log_3_2.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_3_3 :
    (-30115736036664669903 : ℝ) / 1000000000000000000 ≤ Real.log ((83349312286089 : ℝ) / 1000000000000000000000000000) ∧
    Real.log ((83349312286089 : ℝ) / 1000000000000000000000000000) ≤ (-30115736036664669901 : ℝ) / 1000000000000000000 := by
  have hb : (765479815945847423 : ℝ) / 2000000000000000000 ≤ Real.log ((293259321682201191 : ℝ) / 200000000000000000) ∧
      Real.log ((293259321682201191 : ℝ) / 200000000000000000) ≤ (38273990797292371151 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((293259321682201191 : ℚ) / 200000000000000000) 25
      ((765479815945847423 : ℚ) / 2000000000000000000)
      ((38273990797292371151 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (10924761059962257408 : ℝ) / 7450580596923828125) (l := (293259321682201191 : ℝ) / 200000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((83349312286089 : ℝ) / 1000000000000000000000000000) ((10924761059962257408 : ℝ) / 7450580596923828125) (-44) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_3_3 :
    (-3613344299282054231 : ℝ) / 62500000000000000 ≤ Real.log ((38983619370861989 : ℝ) / 500000000000000000000000000000000000000000) ∧
    Real.log ((38983619370861989 : ℝ) / 500000000000000000000000000000000000000000) ≤ (-28906754394256433847 : ℝ) / 500000000000000000 := by
  have hb : (41085437852253829573 : ℝ) / 100000000000000000000 ≤ Real.log ((754052863991425033 : ℝ) / 500000000000000000) ∧
      Real.log ((754052863991425033 : ℝ) / 500000000000000000) ≤ (20542718926126914787 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((754052863991425033 : ℚ) / 500000000000000000) 25
      ((41085437852253829573 : ℚ) / 100000000000000000000)
      ((20542718926126914787 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (342903542328451764397080051712 : ℝ) / 227373675443232059478759765625) (l := (754052863991425033 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((38983619370861989 : ℝ) / 500000000000000000000000000000000000000000) ((342903542328451764397080051712 : ℝ) / 227373675443232059478759765625) (-84) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_3_3 :
    (shellWeights ⟨3, by decide⟩ ⟨3, by decide⟩ : ℝ)^p ≤ powerUpper ⟨3, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (83349312286089 : ℝ) / 1000000000000000000000000000)
    (by norm_num : 0 < (38983619370861989 : ℝ) / 500000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_3_3.2 power_upper_log_3_3.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_3_4 :
    (-5120206865429093317 : ℝ) / 125000000000000000 ≤ Real.log ((16239748423571 : ℝ) / 10000000000000000000000000000000) ∧
    Real.log ((16239748423571 : ℝ) / 10000000000000000000000000000000) ≤ (-20480827461716373267 : ℝ) / 500000000000000000 := by
  have hb : (1254351820327944059 : ℝ) / 2000000000000000000 ≤ Real.log ((1872315518694014859 : ℝ) / 1000000000000000000) ∧
      Real.log ((1872315518694014859 : ℝ) / 1000000000000000000) ≤ (62717591016397202951 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1872315518694014859 : ℚ) / 1000000000000000000) 25
      ((1254351820327944059 : ℚ) / 2000000000000000000)
      ((62717591016397202951 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (8718648546813125066752 : ℝ) / 4656612873077392578125) (l := (1872315518694014859 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((16239748423571 : ℝ) / 10000000000000000000000000000000) ((8718648546813125066752 : ℝ) / 4656612873077392578125) (-60) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_3_4 :
    (-78634538236913823577 : ℝ) / 1000000000000000000 ≤ Real.log ((35352811779034657 : ℝ) / 500000000000000000000000000000000000000000000000000) ∧
    Real.log ((35352811779034657 : ℝ) / 500000000000000000000000000000000000000000000000000) ≤ (-39317269118456911787 : ℝ) / 500000000000000000 := by
  have hb : (4803004336499271219 : ℝ) / 12500000000000000000 ≤ Real.log ((734249174162618801 : ℝ) / 500000000000000000) ∧
      Real.log ((734249174162618801 : ℝ) / 500000000000000000) ≤ (38424034691994169753 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((734249174162618801 : ℚ) / 500000000000000000) 25
      ((4803004336499271219 : ℚ) / 12500000000000000000)
      ((38424034691994169753 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (652144271173876789404295836794355712 : ℝ) / 444089209850062616169452667236328125) (l := (734249174162618801 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((35352811779034657 : ℝ) / 500000000000000000000000000000000000000000000000000) ((652144271173876789404295836794355712 : ℝ) / 444089209850062616169452667236328125) (-114) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_3_4 :
    (shellWeights ⟨3, by decide⟩ ⟨4, by decide⟩ : ℝ)^p ≤ powerUpper ⟨3, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (16239748423571 : ℝ) / 10000000000000000000000000000000)
    (by norm_num : 0 < (35352811779034657 : ℝ) / 500000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_3_4.2 power_upper_log_3_4.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_3_5 :
    (-12951880897763471611 : ℝ) / 250000000000000000 ≤ Real.log ((31643053340993 : ℝ) / 1000000000000000000000000000000000000) ∧
    Real.log ((31643053340993 : ℝ) / 1000000000000000000000000000000000000) ≤ (-51807523591053886441 : ℝ) / 1000000000000000000 := by
  have hb : (4462873773550294083 : ℝ) / 25000000000000000000 ≤ Real.log ((1195440756105293517 : ℝ) / 1000000000000000000) ∧
      Real.log ((1195440756105293517 : ℝ) / 1000000000000000000) ≤ (17851495094201176333 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1195440756105293517 : ℚ) / 1000000000000000000) 25
      ((4462873773550294083 : ℚ) / 25000000000000000000)
      ((17851495094201176333 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (17395952543379004309110784 : ℝ) / 14551915228366851806640625) (l := (1195440756105293517 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((31643053340993 : ℝ) / 1000000000000000000000000000000000000) ((17395952543379004309110784 : ℝ) / 14551915228366851806640625) (-75) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_3_5 :
    (-99455471279067585537 : ℝ) / 1000000000000000000 ≤ Real.log ((64126513507238997 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000) ∧
    Real.log ((64126513507238997 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000) ≤ (-49727735639533792767 : ℝ) / 500000000000000000 := by
  have hb : (17886136078226951013 : ℝ) / 50000000000000000000 ≤ Real.log ((357517259548767303 : ℝ) / 250000000000000000) ∧
      Real.log ((357517259548767303 : ℝ) / 250000000000000000) ≤ (35772272156453902027 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((357517259548767303 : ℚ) / 250000000000000000) 25
      ((17886136078226951013 : ℚ) / 50000000000000000000)
      ((35772272156453902027 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (1240387166412279887211236728786983743127552 : ℝ) / 867361737988403547205962240695953369140625) (l := (357517259548767303 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((64126513507238997 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000) ((1240387166412279887211236728786983743127552 : ℝ) / 867361737988403547205962240695953369140625) (-144) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_3_5 :
    (shellWeights ⟨3, by decide⟩ ⟨5, by decide⟩ : ℝ)^p ≤ powerUpper ⟨3, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (31643053340993 : ℝ) / 1000000000000000000000000000000000000)
    (by norm_num : 0 < (64126513507238997 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_3_5.2 power_upper_log_3_5.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem residue_log_3 :
    (389182029811062661 : ℝ) / 50000000000000000 ≤ Real.log ((2401 : ℝ) / 1) ∧
    Real.log ((2401 : ℝ) / 1) ≤ (3891820298110626611 : ℝ) / 500000000000000000 := by
  have hb : (15902161006185481683 : ℝ) / 100000000000000000000 ≤ Real.log ((2401 : ℝ) / 2048) ∧
      Real.log ((2401 : ℝ) / 2048) ≤ (3975540251546370421 : ℝ) / 25000000000000000000 := by
    have h := log_enclosure_of_rat
      ((2401 : ℚ) / 2048) 25
      ((15902161006185481683 : ℚ) / 100000000000000000000)
      ((3975540251546370421 : ℚ) / 25000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (2401 : ℝ) / 2048) (l := (2401 : ℝ) / 2048)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2401 : ℝ) / 1) ((2401 : ℝ) / 2048) (11) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem energy_log_3 :
    (219842256085367339 : ℝ) / 200000000000000000 ≤ Real.log ((375224689196293013 : ℝ) / 125000000000000000) ∧
    Real.log ((375224689196293013 : ℝ) / 125000000000000000) ≤ (1099211280426836697 : ℝ) / 1000000000000000000 := by
  have hb : (40606409986689138607 : ℝ) / 100000000000000000000 ≤ Real.log ((375224689196293013 : ℝ) / 250000000000000000) ∧
      Real.log ((375224689196293013 : ℝ) / 250000000000000000) ≤ (2537900624168071163 : ℝ) / 6250000000000000000 := by
    have h := log_enclosure_of_rat
      ((375224689196293013 : ℚ) / 250000000000000000) 25
      ((40606409986689138607 : ℚ) / 100000000000000000000)
      ((2537900624168071163 : ℚ) / 6250000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (375224689196293013 : ℝ) / 250000000000000000) (l := (375224689196293013 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((375224689196293013 : ℝ) / 125000000000000000) ((375224689196293013 : ℝ) / 250000000000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem mass_log_3 :
    (7077340224211 : ℝ) / 31250000000000000 ≤ Real.log ((500113250267274069 : ℝ) / 500000000000000000) ∧
    Real.log ((500113250267274069 : ℝ) / 500000000000000000) ≤ (113237443587377 : ℝ) / 500000000000000000 := by
  have hb : (22647488717475213 : ℝ) / 100000000000000000000 ≤ Real.log ((500113250267274069 : ℝ) / 500000000000000000) ∧
      Real.log ((500113250267274069 : ℝ) / 500000000000000000) ≤ (11323744358737607 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((500113250267274069 : ℚ) / 500000000000000000) 25
      ((22647488717475213 : ℚ) / 100000000000000000000)
      ((11323744358737607 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (500113250267274069 : ℝ) / 500000000000000000) (l := (500113250267274069 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((500113250267274069 : ℝ) / 500000000000000000) ((500113250267274069 : ℝ) / 500000000000000000) (0) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

end UnitDistance.Witness.FiniteCertificates
