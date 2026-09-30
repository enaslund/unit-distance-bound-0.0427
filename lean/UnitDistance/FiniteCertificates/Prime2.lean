module

public import UnitDistance.FiniteCertificates.LogEnclosureCompactRun20260920

@[expose] public section
set_option backward.privateInPublic true


namespace UnitDistance.Witness.FiniteCertificates

theorem power_bound_0_0 :
    (shellWeights ⟨0, by decide⟩ ⟨0, by decide⟩ : ℝ)^p ≤ powerUpper ⟨0, by decide⟩ ⟨0, by decide⟩ := by
  norm_num [shellWeights, powerUpper, Matrix.cons_val]

theorem weight_log_0_1 :
    (-2939293288061351497 : ℝ) / 1000000000000000000 ≤ Real.log ((26451551392391 : ℝ) / 500000000000000) ∧
    Real.log ((26451551392391 : ℝ) / 500000000000000) ≤ (-367411661007668937 : ℝ) / 125000000000000000 := by
  have hb : (13161065368459376253 : ℝ) / 25000000000000000000 ≤ Real.log ((26451551392391 : ℝ) / 15625000000000) ∧
      Real.log ((26451551392391 : ℝ) / 15625000000000) ≤ (52644261473837505013 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((26451551392391 : ℚ) / 15625000000000) 25
      ((13161065368459376253 : ℚ) / 25000000000000000000)
      ((52644261473837505013 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (26451551392391 : ℝ) / 15625000000000) (l := (26451551392391 : ℝ) / 15625000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((26451551392391 : ℝ) / 500000000000000) ((26451551392391 : ℝ) / 15625000000000) (-5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_0_1 :
    (-352662097761916893 : ℝ) / 62500000000000000 ≤ Real.log ((35436657529433493 : ℝ) / 10000000000000000000) ∧
    Real.log ((35436657529433493 : ℝ) / 10000000000000000000) ≤ (-2821296782095335143 : ℝ) / 500000000000000000 := by
  have hb : (59573106084883749777 : ℝ) / 100000000000000000000 ≤ Real.log ((1814356865506994841 : ℝ) / 1000000000000000000) ∧
      Real.log ((1814356865506994841 : ℝ) / 1000000000000000000) ≤ (29786553042441874889 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1814356865506994841 : ℚ) / 1000000000000000000) 25
      ((59573106084883749777 : ℚ) / 100000000000000000000)
      ((29786553042441874889 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (35436657529433493 : ℝ) / 19531250000000000) (l := (1814356865506994841 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((35436657529433493 : ℝ) / 10000000000000000000) ((35436657529433493 : ℝ) / 19531250000000000) (-9) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_0_1 :
    (shellWeights ⟨0, by decide⟩ ⟨1, by decide⟩ : ℝ)^p ≤ powerUpper ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (26451551392391 : ℝ) / 500000000000000)
    (by norm_num : 0 < (35436657529433493 : ℝ) / 10000000000000000000) witness_basic.2.2.1.le
    weight_log_0_1.2 power_upper_log_0_1.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_0_2 :
    (-6068001875054922609 : ℝ) / 1000000000000000000 ≤ Real.log ((5789489600511 : ℝ) / 2500000000000000) ∧
    Real.log ((5789489600511 : ℝ) / 2500000000000000) ≤ (-6068001875054922607 : ℝ) / 1000000000000000000 := by
  have hb : (2129034374807314709 : ℝ) / 12500000000000000000 ≤ Real.log ((5789489600511 : ℝ) / 4882812500000) ∧
      Real.log ((5789489600511 : ℝ) / 4882812500000) ≤ (17032274998458517673 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((5789489600511 : ℚ) / 4882812500000) 25
      ((2129034374807314709 : ℚ) / 12500000000000000000)
      ((17032274998458517673 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (5789489600511 : ℝ) / 4882812500000) (l := (5789489600511 : ℝ) / 4882812500000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((5789489600511 : ℝ) / 2500000000000000) ((5789489600511 : ℝ) / 4882812500000) (-9) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_0_2 :
    (-2912202438827148033 : ℝ) / 250000000000000000 ≤ Real.log ((87294363465773703 : ℝ) / 10000000000000000000000) ∧
    Real.log ((87294363465773703 : ℝ) / 10000000000000000000000) ≤ (-1164880975530859213 : ℝ) / 100000000000000000 := by
  have hb : (3367307855261953213 : ℝ) / 25000000000000000000 ≤ Real.log ((1144184680818589079 : ℝ) / 1000000000000000000) ∧
      Real.log ((1144184680818589079 : ℝ) / 1000000000000000000) ≤ (13469231421047812853 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1144184680818589079 : ℚ) / 1000000000000000000) 25
      ((3367307855261953213 : ℚ) / 25000000000000000000)
      ((13469231421047812853 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (87294363465773703 : ℝ) / 76293945312500000) (l := (1144184680818589079 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((87294363465773703 : ℝ) / 10000000000000000000000) ((87294363465773703 : ℝ) / 76293945312500000) (-17) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_0_2 :
    (shellWeights ⟨0, by decide⟩ ⟨2, by decide⟩ : ℝ)^p ≤ powerUpper ⟨0, by decide⟩ ⟨2, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (5789489600511 : ℝ) / 2500000000000000)
    (by norm_num : 0 < (87294363465773703 : ℝ) / 10000000000000000000000) witness_basic.2.2.1.le
    weight_log_0_2.2 power_upper_log_0_2.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_0_3 :
    (-57486466941836311 : ℝ) / 6250000000000000 ≤ Real.log ((5062920920247 : ℝ) / 50000000000000000) ∧
    Real.log ((5062920920247 : ℝ) / 50000000000000000) ≤ (-4598917355346904879 : ℝ) / 500000000000000000 := by
  have hb : (10124516342908491453 : ℝ) / 20000000000000000000 ≤ Real.log ((5062920920247 : ℝ) / 3051757812500) ∧
      Real.log ((5062920920247 : ℝ) / 3051757812500) ≤ (25311290857271228633 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((5062920920247 : ℚ) / 3051757812500) 25
      ((10124516342908491453 : ℚ) / 20000000000000000000)
      ((25311290857271228633 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (5062920920247 : ℝ) / 3051757812500) (l := (5062920920247 : ℝ) / 3051757812500)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((5062920920247 : ℝ) / 50000000000000000) ((5062920920247 : ℝ) / 3051757812500) (-14) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_0_3 :
    (-2207148022360255279 : ℝ) / 125000000000000000 ≤ Real.log ((21457659289358253 : ℝ) / 1000000000000000000000000) ∧
    Real.log ((21457659289358253 : ℝ) / 1000000000000000000000000) ≤ (-1765718417888204223 : ℝ) / 100000000000000000 := by
  have hb : (36464251567653581387 : ℝ) / 100000000000000000000 ≤ Real.log ((1439999139007879647 : ℝ) / 1000000000000000000) ∧
      Real.log ((1439999139007879647 : ℝ) / 1000000000000000000) ≤ (9116062891913395347 : ℝ) / 25000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1439999139007879647 : ℚ) / 1000000000000000000) 25
      ((36464251567653581387 : ℚ) / 100000000000000000000)
      ((9116062891913395347 : ℚ) / 25000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (85830637157433012 : ℝ) / 59604644775390625) (l := (1439999139007879647 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((21457659289358253 : ℝ) / 1000000000000000000000000) ((85830637157433012 : ℝ) / 59604644775390625) (-26) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_0_3 :
    (shellWeights ⟨0, by decide⟩ ⟨3, by decide⟩ : ℝ)^p ≤ powerUpper ⟨0, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (5062920920247 : ℝ) / 50000000000000000)
    (by norm_num : 0 < (21457659289358253 : ℝ) / 1000000000000000000000000) witness_basic.2.2.1.le
    weight_log_0_3.2 power_upper_log_0_3.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_0_4 :
    (-12313483111761261631 : ℝ) / 1000000000000000000 ≤ Real.log ((22453923355659 : ℝ) / 5000000000000000000) ∧
    Real.log ((22453923355659 : ℝ) / 5000000000000000000) ≤ (-12313483111761261629 : ℝ) / 1000000000000000000 := by
  have hb : (16316613831775393933 : ℝ) / 100000000000000000000 ≤ Real.log ((1177232256829174579 : ℝ) / 1000000000000000000) ∧
      Real.log ((1177232256829174579 : ℝ) / 1000000000000000000) ≤ (8158306915887696967 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1177232256829174579 : ℚ) / 1000000000000000000) 25
      ((16316613831775393933 : ℚ) / 100000000000000000000)
      ((8158306915887696967 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (22453923355659 : ℝ) / 19073486328125) (l := (1177232256829174579 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((22453923355659 : ℝ) / 5000000000000000000) ((22453923355659 : ℝ) / 19073486328125) (-18) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_0_4 :
    (-23638328587829338721 : ℝ) / 1000000000000000000 ≤ Real.log ((54200629788884563 : ℝ) / 1000000000000000000000000000) ∧
    Real.log ((54200629788884563 : ℝ) / 1000000000000000000000000000) ≤ (-23638328587829338719 : ℝ) / 1000000000000000000 := by
  have hb : (62182273176874710881 : ℝ) / 100000000000000000000 ≤ Real.log ((1862319458926900659 : ℝ) / 1000000000000000000) ∧
      Real.log ((1862319458926900659 : ℝ) / 1000000000000000000) ≤ (31091136588437355441 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1862319458926900659 : ℚ) / 1000000000000000000) 25
      ((62182273176874710881 : ℚ) / 100000000000000000000)
      ((31091136588437355441 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (13875361225954448128 : ℝ) / 7450580596923828125) (l := (1862319458926900659 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((54200629788884563 : ℝ) / 1000000000000000000000000000) ((13875361225954448128 : ℝ) / 7450580596923828125) (-35) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_0_4 :
    (shellWeights ⟨0, by decide⟩ ⟨4, by decide⟩ : ℝ)^p ≤ powerUpper ⟨0, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (22453923355659 : ℝ) / 5000000000000000000)
    (by norm_num : 0 < (54200629788884563 : ℝ) / 1000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_0_4.2 power_upper_log_0_4.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_0_5 :
    (-15417000481648019067 : ℝ) / 1000000000000000000 ≤ Real.log ((4031918631437 : ℝ) / 20000000000000000000) ∧
    Real.log ((4031918631437 : ℝ) / 20000000000000000000) ≤ (-3083400096329603813 : ℝ) / 200000000000000000 := by
  have hb : (52538467123072305007 : ℝ) / 100000000000000000000 ≤ Real.log ((422777311087768371 : ℝ) / 250000000000000000) ∧
      Real.log ((422777311087768371 : ℝ) / 250000000000000000) ≤ (3283654195192019063 : ℝ) / 6250000000000000000 := by
    have h := log_enclosure_of_rat
      ((422777311087768371 : ℚ) / 250000000000000000) 25
      ((52538467123072305007 : ℚ) / 100000000000000000000)
      ((3283654195192019063 : ℚ) / 6250000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (32255349051496 : ℝ) / 19073486328125) (l := (422777311087768371 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((4031918631437 : ℝ) / 20000000000000000000) ((32255349051496 : ℝ) / 19073486328125) (-23) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_0_5 :
    (-5919236984632413061 : ℝ) / 200000000000000000 ≤ Real.log ((2802658598961063 : ℝ) / 20000000000000000000000000000) ∧
    Real.log ((2802658598961063 : ℝ) / 20000000000000000000000000000) ≤ (-14798092461581032651 : ℝ) / 500000000000000000 := by
  have hb : (4182876818311660019 : ℝ) / 20000000000000000000 ≤ Real.log ((77038892956102049 : ℝ) / 62500000000000000) ∧
      Real.log ((77038892956102049 : ℝ) / 62500000000000000) ≤ (326787251430598439 : ℝ) / 1562500000000000000 := by
    have h := log_enclosure_of_rat
      ((77038892956102049 : ℚ) / 62500000000000000) 25
      ((4182876818311660019 : ℚ) / 20000000000000000000)
      ((326787251430598439 : ℚ) / 1562500000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (45918758485378056192 : ℝ) / 37252902984619140625) (l := (77038892956102049 : ℝ) / 62500000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2802658598961063 : ℝ) / 20000000000000000000000000000) ((45918758485378056192 : ℝ) / 37252902984619140625) (-43) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_0_5 :
    (shellWeights ⟨0, by decide⟩ ⟨5, by decide⟩ : ℝ)^p ≤ powerUpper ⟨0, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (4031918631437 : ℝ) / 20000000000000000000)
    (by norm_num : 0 < (2802658598961063 : ℝ) / 20000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_0_5.2 power_upper_log_0_5.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem residue_log_0 :
    (2772588722239781237 : ℝ) / 1000000000000000000 ≤ Real.log ((16 : ℝ) / 1) ∧
    Real.log ((16 : ℝ) / 1) ≤ (2772588722239781239 : ℝ) / 1000000000000000000 := by
  have hb : (0 : ℝ) / 1 ≤ Real.log ((1 : ℝ) / 1) ∧
      Real.log ((1 : ℝ) / 1) ≤ (0 : ℝ) / 1 := by
    have h := log_enclosure_of_rat
      ((1 : ℚ) / 1) 25
      ((0 : ℚ) / 1)
      ((0 : ℚ) / 1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (1 : ℝ) / 1) (l := (1 : ℝ) / 1)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((16 : ℝ) / 1) ((1 : ℝ) / 1) (4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem energy_log_0 :
    (1100514558076640253 : ℝ) / 500000000000000000 ≤ Real.log ((9034306067355708897 : ℝ) / 1000000000000000000) ∧
    Real.log ((9034306067355708897 : ℝ) / 1000000000000000000) ≤ (550257279038320127 : ℝ) / 250000000000000000 := by
  have hb : (243175148946889157 : ℝ) / 2000000000000000000 ≤ Real.log ((282322064604865903 : ℝ) / 250000000000000000) ∧
      Real.log ((282322064604865903 : ℝ) / 250000000000000000) ≤ (12158757447344457851 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((282322064604865903 : ℚ) / 250000000000000000) 25
      ((243175148946889157 : ℚ) / 2000000000000000000)
      ((12158757447344457851 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (9034306067355708897 : ℝ) / 8000000000000000000) (l := (282322064604865903 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((9034306067355708897 : ℝ) / 1000000000000000000) ((9034306067355708897 : ℝ) / 8000000000000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem mass_log_0 :
    (13464780074369581 : ℝ) / 250000000000000000 ≤ Real.log ((105533591627196963 : ℝ) / 100000000000000000) ∧
    Real.log ((105533591627196963 : ℝ) / 100000000000000000) ≤ (26929560148739163 : ℝ) / 500000000000000000 := by
  have hb : (5385912029747832453 : ℝ) / 100000000000000000000 ≤ Real.log ((105533591627196963 : ℝ) / 100000000000000000) ∧
      Real.log ((105533591627196963 : ℝ) / 100000000000000000) ≤ (2692956014873916227 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((105533591627196963 : ℚ) / 100000000000000000) 25
      ((5385912029747832453 : ℚ) / 100000000000000000000)
      ((2692956014873916227 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (105533591627196963 : ℝ) / 100000000000000000) (l := (105533591627196963 : ℝ) / 100000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((105533591627196963 : ℝ) / 100000000000000000) ((105533591627196963 : ℝ) / 100000000000000000) (0) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

end UnitDistance.Witness.FiniteCertificates
