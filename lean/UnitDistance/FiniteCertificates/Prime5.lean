module

public import UnitDistance.FiniteCertificates.LogEnclosureCompactRun20260920

@[expose] public section
set_option backward.privateInPublic true


namespace UnitDistance.Witness.FiniteCertificates

theorem power_bound_2_0 :
    (shellWeights ⟨2, by decide⟩ ⟨0, by decide⟩ : ℝ)^p ≤ powerUpper ⟨2, by decide⟩ ⟨0, by decide⟩ := by
  norm_num [shellWeights, powerUpper, Matrix.cons_val]

theorem weight_log_2_1 :
    (-43266065888208397 : ℝ) / 12500000000000000 ≤ Real.log ((15694696101781 : ℝ) / 500000000000000) ∧
    Real.log ((15694696101781 : ℝ) / 500000000000000) ≤ (-1730642635528335879 : ℝ) / 500000000000000000 := by
  have hb : (222531587152739371 : ℝ) / 50000000000000000000 ≤ Real.log ((15694696101781 : ℝ) / 15625000000000) ∧
      Real.log ((15694696101781 : ℝ) / 15625000000000) ≤ (445063174305478743 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((15694696101781 : ℚ) / 15625000000000) 25
      ((222531587152739371 : ℚ) / 50000000000000000000)
      ((445063174305478743 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (15694696101781 : ℝ) / 15625000000000) (l := (15694696101781 : ℝ) / 15625000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((15694696101781 : ℝ) / 500000000000000) ((15694696101781 : ℝ) / 15625000000000) (-5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_2_1 :
    (-830583412415015511 : ℝ) / 125000000000000000 ≤ Real.log ((13009411702814159 : ℝ) / 10000000000000000000) ∧
    Real.log ((13009411702814159 : ℝ) / 10000000000000000000) ≤ (-3322333649660062043 : ℝ) / 500000000000000000 := by
  have hb : (28680450627932900713 : ℝ) / 100000000000000000000 ≤ Real.log ((1332163758368169881 : ℝ) / 1000000000000000000) ∧
      Real.log ((1332163758368169881 : ℝ) / 1000000000000000000) ≤ (14340225313966450357 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1332163758368169881 : ℚ) / 1000000000000000000) 25
      ((28680450627932900713 : ℚ) / 100000000000000000000)
      ((14340225313966450357 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (13009411702814159 : ℝ) / 9765625000000000) (l := (1332163758368169881 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((13009411702814159 : ℝ) / 10000000000000000000) ((13009411702814159 : ℝ) / 9765625000000000) (-10) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_2_1 :
    (shellWeights ⟨2, by decide⟩ ⟨1, by decide⟩ : ℝ)^p ≤ powerUpper ⟨2, by decide⟩ ⟨1, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (15694696101781 : ℝ) / 500000000000000)
    (by norm_num : 0 < (13009411702814159 : ℝ) / 10000000000000000000) witness_basic.2.2.1.le
    weight_log_2_1.2 power_upper_log_2_1.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_2_2 :
    (-1418019643778148169 : ℝ) / 200000000000000000 ≤ Real.log ((20832887856541 : ℝ) / 25000000000000000) ∧
    Real.log ((20832887856541 : ℝ) / 25000000000000000) ≤ (-1772524554722685211 : ℝ) / 250000000000000000 := by
  have hb : (53452076726865755879 : ℝ) / 100000000000000000000 ≤ Real.log ((20832887856541 : ℝ) / 12207031250000) ∧
      Real.log ((20832887856541 : ℝ) / 12207031250000) ≤ (1336301918171643897 : ℝ) / 2500000000000000000 := by
    have h := log_enclosure_of_rat
      ((20832887856541 : ℚ) / 12207031250000) 25
      ((53452076726865755879 : ℚ) / 100000000000000000000)
      ((1336301918171643897 : ℚ) / 2500000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (20832887856541 : ℝ) / 12207031250000) (l := (20832887856541 : ℝ) / 12207031250000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((20832887856541 : ℝ) / 25000000000000000) ((20832887856541 : ℝ) / 12207031250000) (-11) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_2_2 :
    (-13610939317246517763 : ℝ) / 1000000000000000000 ≤ Real.log ((6134994325060029 : ℝ) / 5000000000000000000000) ∧
    Real.log ((6134994325060029 : ℝ) / 5000000000000000000000) ≤ (-13610939317246517761 : ℝ) / 1000000000000000000 := by
  have hb : (2520042939523884261 : ℝ) / 10000000000000000000 ≤ Real.log ((1286601561878828993 : ℝ) / 1000000000000000000) ∧
      Real.log ((1286601561878828993 : ℝ) / 1000000000000000000) ≤ (25200429395238842611 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1286601561878828993 : ℚ) / 1000000000000000000) 25
      ((2520042939523884261 : ℚ) / 10000000000000000000)
      ((25200429395238842611 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (6134994325060029 : ℝ) / 4768371582031250) (l := (1286601561878828993 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((6134994325060029 : ℝ) / 5000000000000000000000) ((6134994325060029 : ℝ) / 4768371582031250) (-20) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_2_2 :
    (shellWeights ⟨2, by decide⟩ ⟨2, by decide⟩ : ℝ)^p ≤ powerUpper ⟨2, by decide⟩ ⟨2, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (20832887856541 : ℝ) / 25000000000000000)
    (by norm_num : 0 < (6134994325060029 : ℝ) / 5000000000000000000000) witness_basic.2.2.1.le
    weight_log_2_2.2 power_upper_log_2_2.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_2_3 :
    (-2678378585315159871 : ℝ) / 250000000000000000 ≤ Real.log ((22242307460119 : ℝ) / 1000000000000000000) ∧
    Real.log ((22242307460119 : ℝ) / 1000000000000000000) ≤ (-10713514341260639483 : ℝ) / 1000000000000000000 := by
  have hb : (7536810953969709337 : ℝ) / 20000000000000000000 ≤ Real.log ((22242307460119 : ℝ) / 15258789062500) ∧
      Real.log ((22242307460119 : ℝ) / 15258789062500) ≤ (18842027384924273343 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((22242307460119 : ℚ) / 15258789062500) 25
      ((7536810953969709337 : ℚ) / 20000000000000000000)
      ((18842027384924273343 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (22242307460119 : ℝ) / 15258789062500) (l := (22242307460119 : ℝ) / 15258789062500)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((22242307460119 : ℝ) / 1000000000000000000) ((22242307460119 : ℝ) / 15258789062500) (-16) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_2_3 :
    (-1285428186883453311 : ℝ) / 62500000000000000 ≤ Real.log ((11693111875031823 : ℝ) / 10000000000000000000000000) ∧
    Real.log ((11693111875031823 : ℝ) / 10000000000000000000000000) ≤ (-10283425495067626487 : ℝ) / 500000000000000000 := by
  have hb : (22756442666310630699 : ℝ) / 100000000000000000000 ≤ Real.log ((156942290911659121 : ℝ) / 125000000000000000) ∧
      Real.log ((156942290911659121 : ℝ) / 125000000000000000) ≤ (227564426663106307 : ℝ) / 1000000000000000000 := by
    have h := log_enclosure_of_rat
      ((156942290911659121 : ℚ) / 125000000000000000) 25
      ((22756442666310630699 : ℚ) / 100000000000000000000)
      ((227564426663106307 : ℚ) / 1000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (374179580001018336 : ℝ) / 298023223876953125) (l := (156942290911659121 : ℝ) / 125000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((11693111875031823 : ℝ) / 10000000000000000000000000) ((374179580001018336 : ℝ) / 298023223876953125) (-30) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_2_3 :
    (shellWeights ⟨2, by decide⟩ ⟨3, by decide⟩ : ℝ)^p ≤ powerUpper ⟨2, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (22242307460119 : ℝ) / 1000000000000000000)
    (by norm_num : 0 < (11693111875031823 : ℝ) / 10000000000000000000000000) witness_basic.2.2.1.le
    weight_log_2_3.2 power_upper_log_2_3.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_2_4 :
    (-14317965333926062359 : ℝ) / 1000000000000000000 ≤ Real.log ((60504358878881 : ℝ) / 100000000000000000000) ∧
    Real.log ((60504358878881 : ℝ) / 100000000000000000000) ≤ (-14317965333926062357 : ℝ) / 1000000000000000000 := by
  have hb : (11906272891639456961 : ℝ) / 50000000000000000000 ≤ Real.log ((1268868372315630469 : ℝ) / 1000000000000000000) ∧
      Real.log ((1268868372315630469 : ℝ) / 1000000000000000000) ≤ (23812545783278913923 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1268868372315630469 : ℚ) / 1000000000000000000) 25
      ((11906272891639456961 : ℚ) / 50000000000000000000)
      ((23812545783278913923 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (121008717757762 : ℝ) / 95367431640625) (l := (1268868372315630469 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((60504358878881 : ℝ) / 100000000000000000000) ((121008717757762 : ℝ) / 95367431640625) (-21) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_2_4 :
    (-13743177547757379479 : ℝ) / 500000000000000000 ≤ Real.log ((2311307082234433 : ℝ) / 2000000000000000000000000000) ∧
    Real.log ((2311307082234433 : ℝ) / 2000000000000000000000000000) ≤ (-6871588773878689739 : ℝ) / 250000000000000000 := by
  have hb : (5988303172076335487 : ℝ) / 25000000000000000000 ≤ Real.log ((1270654506138889259 : ℝ) / 1000000000000000000) ∧
      Real.log ((1270654506138889259 : ℝ) / 1000000000000000000) ≤ (23953212688305341949 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1270654506138889259 : ℚ) / 1000000000000000000) 25
      ((5988303172076335487 : ℚ) / 25000000000000000000)
      ((23953212688305341949 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (9467113808832237568 : ℝ) / 7450580596923828125) (l := (1270654506138889259 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2311307082234433 : ℝ) / 2000000000000000000000000000) ((9467113808832237568 : ℝ) / 7450580596923828125) (-40) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_2_4 :
    (shellWeights ⟨2, by decide⟩ ⟨4, by decide⟩ : ℝ)^p ≤ powerUpper ⟨2, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (60504358878881 : ℝ) / 100000000000000000000)
    (by norm_num : 0 < (2311307082234433 : ℝ) / 2000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_2_4.2 power_upper_log_2_4.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_2_5 :
    (-8952800751612279949 : ℝ) / 500000000000000000 ≤ Real.log ((16737711273851 : ℝ) / 1000000000000000000000) ∧
    Real.log ((16737711273851 : ℝ) / 1000000000000000000000) ≤ (-2238200187903069987 : ℝ) / 125000000000000000 := by
  have hb : (11622519133401814769 : ℝ) / 100000000000000000000 ≤ Real.log ((224649757909626703 : ℝ) / 200000000000000000) ∧
      Real.log ((224649757909626703 : ℝ) / 200000000000000000) ≤ (1162251913340181477 : ℝ) / 10000000000000000000 := by
    have h := log_enclosure_of_rat
      ((224649757909626703 : ℚ) / 200000000000000000) 25
      ((11622519133401814769 : ℚ) / 100000000000000000000)
      ((1162251913340181477 : ℚ) / 10000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (535606760763232 : ℝ) / 476837158203125) (l := (224649757909626703 : ℝ) / 200000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((16737711273851 : ℝ) / 1000000000000000000000) ((535606760763232 : ℝ) / 476837158203125) (-26) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_2_5 :
    (-429669745000580899 : ℝ) / 12500000000000000 ≤ Real.log ((1179625240059437 : ℝ) / 1000000000000000000000000000000) ∧
    Real.log ((1179625240059437 : ℝ) / 1000000000000000000000000000000) ≤ (-34373579600046471917 : ℝ) / 1000000000000000000 := by
  have hb : (28377942795079355197 : ℝ) / 100000000000000000000 ≤ Real.log ((132813994789212809 : ℝ) / 100000000000000000) ∧
      Real.log ((132813994789212809 : ℝ) / 100000000000000000) ≤ (14188971397539677599 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((132813994789212809 : ℚ) / 100000000000000000) 25
      ((28377942795079355197 : ℚ) / 100000000000000000000)
      ((14188971397539677599 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (1236926715720564211712 : ℝ) / 931322574615478515625) (l := (132813994789212809 : ℝ) / 100000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1179625240059437 : ℝ) / 1000000000000000000000000000000) ((1236926715720564211712 : ℝ) / 931322574615478515625) (-50) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_2_5 :
    (shellWeights ⟨2, by decide⟩ ⟨5, by decide⟩ : ℝ)^p ≤ powerUpper ⟨2, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (16737711273851 : ℝ) / 1000000000000000000000)
    (by norm_num : 0 < (1179625240059437 : ℝ) / 1000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_2_5.2 power_upper_log_2_5.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem residue_log_2 :
    (3218875824868200749 : ℝ) / 1000000000000000000 ≤ Real.log ((25 : ℝ) / 1) ∧
    Real.log ((25 : ℝ) / 1) ≤ (12875503299472803 : ℝ) / 4000000000000000 := by
  have hb : (44628710262841951153 : ℝ) / 100000000000000000000 ≤ Real.log ((25 : ℝ) / 16) ∧
      Real.log ((25 : ℝ) / 16) ≤ (22314355131420975577 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((25 : ℚ) / 16) 25
      ((44628710262841951153 : ℚ) / 100000000000000000000)
      ((22314355131420975577 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (25 : ℝ) / 16) (l := (25 : ℝ) / 16)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((25 : ℝ) / 1) ((25 : ℝ) / 16) (4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem energy_log_2 :
    (504523225214088207 : ℝ) / 250000000000000000 ≤ Real.log ((7523962300472236593 : ℝ) / 1000000000000000000) ∧
    Real.log ((7523962300472236593 : ℝ) / 1000000000000000000) ≤ (201809290085635283 : ℝ) / 100000000000000000 := by
  have hb : (12635970794729244201 : ℝ) / 20000000000000000000 ≤ Real.log ((470247643779514787 : ℝ) / 250000000000000000) ∧
      Real.log ((470247643779514787 : ℝ) / 250000000000000000) ≤ (31589926986823110503 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((470247643779514787 : ℚ) / 250000000000000000) 25
      ((12635970794729244201 : ℚ) / 20000000000000000000)
      ((31589926986823110503 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (7523962300472236593 : ℝ) / 4000000000000000000) (l := (470247643779514787 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((7523962300472236593 : ℝ) / 1000000000000000000) ((7523962300472236593 : ℝ) / 4000000000000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem mass_log_2 :
    (3934519821522407 : ℝ) / 125000000000000000 ≤ Real.log ((515988385751319139 : ℝ) / 500000000000000000) ∧
    Real.log ((515988385751319139 : ℝ) / 500000000000000000) ≤ (15738079286089629 : ℝ) / 500000000000000000 := by
  have hb : (3147615857217925621 : ℝ) / 100000000000000000000 ≤ Real.log ((515988385751319139 : ℝ) / 500000000000000000) ∧
      Real.log ((515988385751319139 : ℝ) / 500000000000000000) ≤ (1573807928608962811 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((515988385751319139 : ℚ) / 500000000000000000) 25
      ((3147615857217925621 : ℚ) / 100000000000000000000)
      ((1573807928608962811 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (515988385751319139 : ℝ) / 500000000000000000) (l := (515988385751319139 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((515988385751319139 : ℝ) / 500000000000000000) ((515988385751319139 : ℝ) / 500000000000000000) (0) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

end UnitDistance.Witness.FiniteCertificates
