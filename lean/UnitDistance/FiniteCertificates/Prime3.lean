module

public import UnitDistance.FiniteCertificates.LogEnclosureCompactRun20260920

@[expose] public section
set_option backward.privateInPublic true


namespace UnitDistance.Witness.FiniteCertificates

theorem power_bound_1_0 :
    (shellWeights ⟨1, by decide⟩ ⟨0, by decide⟩ : ℝ)^p ≤ powerUpper ⟨1, by decide⟩ ⟨0, by decide⟩ := by
  norm_num [shellWeights, powerUpper, Matrix.cons_val]

theorem weight_log_1_1 :
    (-578495479330081467 : ℝ) / 250000000000000000 ≤ Real.log ((98866787345973 : ℝ) / 1000000000000000) ∧
    Real.log ((98866787345973 : ℝ) / 1000000000000000) ≤ (-1156990958660162933 : ℝ) / 500000000000000000 := by
  have hb : (45860680491945537057 : ℝ) / 100000000000000000000 ≤ Real.log ((98866787345973 : ℝ) / 62500000000000) ∧
      Real.log ((98866787345973 : ℝ) / 62500000000000) ≤ (22930340245972768529 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((98866787345973 : ℚ) / 62500000000000) 25
      ((45860680491945537057 : ℚ) / 100000000000000000000)
      ((22930340245972768529 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (98866787345973 : ℝ) / 62500000000000) (l := (98866787345973 : ℝ) / 62500000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((98866787345973 : ℝ) / 1000000000000000) ((98866787345973 : ℝ) / 62500000000000) (-4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_1_1 :
    (-4442176467166029129 : ℝ) / 1000000000000000000 ≤ Real.log ((11770292965347987 : ℝ) / 1000000000000000000) ∧
    Real.log ((11770292965347987 : ℝ) / 1000000000000000000) ≤ (-555272058395753641 : ℝ) / 125000000000000000 := by
  have hb : (8197075935071760741 : ℝ) / 20000000000000000000 ≤ Real.log ((11770292965347987 : ℝ) / 7812500000000000) ∧
      Real.log ((11770292965347987 : ℝ) / 7812500000000000) ≤ (20492689837679401853 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((11770292965347987 : ℚ) / 7812500000000000) 25
      ((8197075935071760741 : ℚ) / 20000000000000000000)
      ((20492689837679401853 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (11770292965347987 : ℝ) / 7812500000000000) (l := (11770292965347987 : ℝ) / 7812500000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((11770292965347987 : ℝ) / 1000000000000000000) ((11770292965347987 : ℝ) / 7812500000000000) (-7) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_1_1 :
    (shellWeights ⟨1, by decide⟩ ⟨1, by decide⟩ : ℝ)^p ≤ powerUpper ⟨1, by decide⟩ ⟨1, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (98866787345973 : ℝ) / 1000000000000000)
    (by norm_num : 0 < (11770292965347987 : ℝ) / 1000000000000000000) witness_basic.2.2.1.le
    weight_log_1_1.2 power_upper_log_1_1.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_1_2 :
    (-600475157649500939 : ℝ) / 125000000000000000 ≤ Real.log ((81985230138641 : ℝ) / 10000000000000000) ∧
    Real.log ((81985230138641 : ℝ) / 10000000000000000) ≤ (-480380126119600751 : ℝ) / 100000000000000000 := by
  have hb : (192916010894438617 : ℝ) / 4000000000000000000 ≤ Real.log ((81985230138641 : ℝ) / 78125000000000) ∧
      Real.log ((81985230138641 : ℝ) / 78125000000000) ≤ (2411450136180482713 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((81985230138641 : ℚ) / 78125000000000) 25
      ((192916010894438617 : ℚ) / 4000000000000000000)
      ((2411450136180482713 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (81985230138641 : ℝ) / 78125000000000) (l := (81985230138641 : ℝ) / 78125000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((81985230138641 : ℝ) / 10000000000000000) ((81985230138641 : ℝ) / 78125000000000) (-7) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_1_2 :
    (-461095498536552057 : ℝ) / 50000000000000000 ≤ Real.log ((49424853584417673 : ℝ) / 500000000000000000000) ∧
    Real.log ((49424853584417673 : ℝ) / 500000000000000000000) ≤ (-4610954985365520569 : ℝ) / 500000000000000000 := by
  have hb : (48215055710819319237 : ℝ) / 100000000000000000000 ≤ Real.log ((404888400563549577 : ℝ) / 250000000000000000) ∧
      Real.log ((404888400563549577 : ℝ) / 250000000000000000) ≤ (24107527855409659619 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((404888400563549577 : ℚ) / 250000000000000000) 25
      ((48215055710819319237 : ℚ) / 100000000000000000000)
      ((24107527855409659619 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (49424853584417673 : ℝ) / 30517578125000000) (l := (404888400563549577 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((49424853584417673 : ℝ) / 500000000000000000000) ((49424853584417673 : ℝ) / 30517578125000000) (-14) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_1_2 :
    (shellWeights ⟨1, by decide⟩ ⟨2, by decide⟩ : ℝ)^p ≤ powerUpper ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (81985230138641 : ℝ) / 10000000000000000)
    (by norm_num : 0 < (49424853584417673 : ℝ) / 500000000000000000000) witness_basic.2.2.1.le
    weight_log_1_2.2 power_upper_log_1_2.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_1_3 :
    (-1824096277804529599 : ℝ) / 250000000000000000 ≤ Real.log ((33899259591601 : ℝ) / 50000000000000000) ∧
    Real.log ((33899259591601 : ℝ) / 50000000000000000) ≤ (-3648192555609059197 : ℝ) / 500000000000000000 := by
  have hb : (1641169374706400043 : ℝ) / 5000000000000000000 ≤ Real.log ((33899259591601 : ℝ) / 24414062500000) ∧
      Real.log ((33899259591601 : ℝ) / 24414062500000) ≤ (32823387494128000861 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((33899259591601 : ℚ) / 24414062500000) 25
      ((1641169374706400043 : ℚ) / 5000000000000000000)
      ((32823387494128000861 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (33899259591601 : ℝ) / 24414062500000) (l := (33899259591601 : ℝ) / 24414062500000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((33899259591601 : ℝ) / 50000000000000000) ((33899259591601 : ℝ) / 24414062500000) (-11) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_1_3 :
    (-2801390105413466409 : ℝ) / 200000000000000000 ≤ Real.log ((41288459764202843 : ℝ) / 50000000000000000000000) ∧
    Real.log ((41288459764202843 : ℝ) / 50000000000000000000000) ≤ (-14006950527067332043 : ℝ) / 1000000000000000000 := by
  have hb : (54914026469151945381 : ℝ) / 100000000000000000000 ≤ Real.log ((432940879857087603 : ℝ) / 250000000000000000) ∧
      Real.log ((432940879857087603 : ℝ) / 250000000000000000) ≤ (27457013234575972691 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((432940879857087603 : ℚ) / 250000000000000000) 25
      ((54914026469151945381 : ℚ) / 100000000000000000000)
      ((27457013234575972691 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (41288459764202843 : ℝ) / 23841857910156250) (l := (432940879857087603 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((41288459764202843 : ℝ) / 50000000000000000000000) ((41288459764202843 : ℝ) / 23841857910156250) (-21) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_1_3 :
    (shellWeights ⟨1, by decide⟩ ⟨3, by decide⟩ : ℝ)^p ≤ powerUpper ⟨1, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (33899259591601 : ℝ) / 50000000000000000)
    (by norm_num : 0 < (41288459764202843 : ℝ) / 50000000000000000000000) witness_basic.2.2.1.le
    weight_log_1_3.2 power_upper_log_1_3.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_1_4 :
    (-4889843247626689439 : ℝ) / 500000000000000000 ≤ Real.log ((7073691794287 : ℝ) / 125000000000000000) ∧
    Real.log ((7073691794287 : ℝ) / 125000000000000000) ≤ (-9779686495253378877 : ℝ) / 1000000000000000000 := by
  have hb : (964876895540313693 : ℝ) / 1562500000000000000 ≤ Real.log ((7073691794287 : ℝ) / 3814697265625) ∧
      Real.log ((7073691794287 : ℝ) / 3814697265625) ≤ (61752121314580076353 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((7073691794287 : ℚ) / 3814697265625) 25
      ((964876895540313693 : ℚ) / 1562500000000000000)
      ((61752121314580076353 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (7073691794287 : ℝ) / 3814697265625) (l := (7073691794287 : ℝ) / 3814697265625)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((7073691794287 : ℝ) / 125000000000000000) ((7073691794287 : ℝ) / 3814697265625) (-15) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_1_4 :
    (-18774171431635640361 : ℝ) / 1000000000000000000 ≤ Real.log ((70223253196937081 : ℝ) / 10000000000000000000000000) ∧
    Real.log ((70223253196937081 : ℝ) / 10000000000000000000000000) ≤ (-469354285790891009 : ℝ) / 25000000000000000 := by
  have hb : (31697481202141415141 : ℝ) / 50000000000000000000 ≤ Real.log ((942520549686163157 : ℝ) / 500000000000000000) ∧
      Real.log ((942520549686163157 : ℝ) / 500000000000000000) ≤ (63394962404282830283 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((942520549686163157 : ℚ) / 500000000000000000) 25
      ((31697481202141415141 : ℚ) / 50000000000000000000)
      ((63394962404282830283 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (561786025575496648 : ℝ) / 298023223876953125) (l := (942520549686163157 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((70223253196937081 : ℝ) / 10000000000000000000000000) ((561786025575496648 : ℝ) / 298023223876953125) (-28) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_1_4 :
    (shellWeights ⟨1, by decide⟩ ⟨4, by decide⟩ : ℝ)^p ≤ powerUpper ⟨1, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (7073691794287 : ℝ) / 125000000000000000)
    (by norm_num : 0 < (70223253196937081 : ℝ) / 10000000000000000000000000) witness_basic.2.2.1.le
    weight_log_1_4.2 power_upper_log_1_4.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_1_5 :
    (-3064570426132110303 : ℝ) / 250000000000000000 ≤ Real.log ((11864130273063 : ℝ) / 2500000000000000000) ∧
    Real.log ((11864130273063 : ℝ) / 2500000000000000000) ≤ (-1225828170452844121 : ℝ) / 100000000000000000 := by
  have hb : (21836754555057435813 : ℝ) / 100000000000000000000 ≤ Real.log ((311011056630182707 : ℝ) / 250000000000000000) ∧
      Real.log ((311011056630182707 : ℝ) / 250000000000000000) ≤ (10918377277528717907 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((311011056630182707 : ℚ) / 250000000000000000) 25
      ((21836754555057435813 : ℚ) / 100000000000000000000)
      ((10918377277528717907 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (23728260546126 : ℝ) / 19073486328125) (l := (311011056630182707 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((11864130273063 : ℝ) / 2500000000000000000) ((23728260546126 : ℝ) / 19073486328125) (-18) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_1_5 :
    (-4706471568179596301 : ℝ) / 200000000000000000 ≤ Real.log ((60259683113283281 : ℝ) / 1000000000000000000000000000) ∧
    Real.log ((60259683113283281 : ℝ) / 1000000000000000000000000000) ≤ (-11766178920448990751 : ℝ) / 500000000000000000 := by
  have hb : (3464629814015901609 : ℝ) / 100000000000000000000 ≤ Real.log ((51762673647775031 : ℝ) / 50000000000000000) ∧
      Real.log ((51762673647775031 : ℝ) / 50000000000000000) ≤ (346462981401590161 : ℝ) / 10000000000000000000 := by
    have h := log_enclosure_of_rat
      ((51762673647775031 : ℚ) / 50000000000000000) 25
      ((3464629814015901609 : ℚ) / 100000000000000000000)
      ((346462981401590161 : ℚ) / 10000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (7713239438500259968 : ℝ) / 7450580596923828125) (l := (51762673647775031 : ℝ) / 50000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((60259683113283281 : ℝ) / 1000000000000000000000000000) ((7713239438500259968 : ℝ) / 7450580596923828125) (-34) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_1_5 :
    (shellWeights ⟨1, by decide⟩ ⟨5, by decide⟩ : ℝ)^p ≤ powerUpper ⟨1, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (11864130273063 : ℝ) / 2500000000000000000)
    (by norm_num : 0 < (60259683113283281 : ℝ) / 1000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_1_5.2 power_upper_log_1_5.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem residue_log_1 :
    (1098612288668109691 : ℝ) / 500000000000000000 ≤ Real.log ((9 : ℝ) / 1) ∧
    Real.log ((9 : ℝ) / 1) ≤ (274653072167027423 : ℝ) / 125000000000000000 := by
  have hb : (11778303565638345453 : ℝ) / 100000000000000000000 ≤ Real.log ((9 : ℝ) / 8) ∧
      Real.log ((9 : ℝ) / 8) ≤ (5889151782819172727 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((9 : ℚ) / 8) 25
      ((11778303565638345453 : ℚ) / 100000000000000000000)
      ((5889151782819172727 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (9 : ℝ) / 8) (l := (9 : ℝ) / 8)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((9 : ℝ) / 1) ((9 : ℝ) / 8) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem energy_log_1 :
    (2518205691434532483 : ℝ) / 1000000000000000000 ≤ Real.log ((12406315921368458027 : ℝ) / 1000000000000000000) ∧
    Real.log ((12406315921368458027 : ℝ) / 1000000000000000000) ≤ (629551422858633121 : ℝ) / 250000000000000000 := by
  have hb : (43876414975469655493 : ℝ) / 100000000000000000000 ≤ Real.log ((1550789490171057253 : ℝ) / 1000000000000000000) ∧
      Real.log ((1550789490171057253 : ℝ) / 1000000000000000000) ≤ (21938207487734827747 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1550789490171057253 : ℚ) / 1000000000000000000) 25
      ((43876414975469655493 : ℚ) / 100000000000000000000)
      ((21938207487734827747 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (12406315921368458027 : ℝ) / 8000000000000000000) (l := (1550789490171057253 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((12406315921368458027 : ℝ) / 1000000000000000000) ((12406315921368458027 : ℝ) / 8000000000000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem mass_log_1 :
    (48499257876375429 : ℝ) / 500000000000000000 ≤ Real.log ((550929369094497907 : ℝ) / 500000000000000000) ∧
    Real.log ((550929369094497907 : ℝ) / 500000000000000000) ≤ (4849925787637543 : ℝ) / 50000000000000000 := by
  have hb : (9699851575275085847 : ℝ) / 100000000000000000000 ≤ Real.log ((550929369094497907 : ℝ) / 500000000000000000) ∧
      Real.log ((550929369094497907 : ℝ) / 500000000000000000) ≤ (1212481446909385731 : ℝ) / 12500000000000000000 := by
    have h := log_enclosure_of_rat
      ((550929369094497907 : ℚ) / 500000000000000000) 25
      ((9699851575275085847 : ℚ) / 100000000000000000000)
      ((1212481446909385731 : ℚ) / 12500000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (550929369094497907 : ℝ) / 500000000000000000) (l := (550929369094497907 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((550929369094497907 : ℝ) / 500000000000000000) ((550929369094497907 : ℝ) / 500000000000000000) (0) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

end UnitDistance.Witness.FiniteCertificates
