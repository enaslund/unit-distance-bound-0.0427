module

public import UnitDistance.FiniteCertificates.LogEnclosureCompactRun20260920

@[expose] public section
set_option backward.privateInPublic true


namespace UnitDistance.Witness.FiniteCertificates

theorem power_bound_4_0 :
    (shellWeights ⟨4, by decide⟩ ⟨0, by decide⟩ : ℝ)^p ≤ powerUpper ⟨4, by decide⟩ ⟨0, by decide⟩ := by
  norm_num [shellWeights, powerUpper, Matrix.cons_val]

theorem weight_log_4_1 :
    (-2680359148890383763 : ℝ) / 250000000000000000 ≤ Real.log ((882671775669 : ℝ) / 40000000000000000) ∧
    Real.log ((882671775669 : ℝ) / 40000000000000000) ≤ (-214428731911230701 : ℝ) / 20000000000000000 := by
  have hb : (7378365867951797981 : ℝ) / 20000000000000000000 ≤ Real.log ((882671775669 : ℝ) / 610351562500) ∧
      Real.log ((882671775669 : ℝ) / 610351562500) ≤ (18445914669879494953 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((882671775669 : ℚ) / 610351562500) 25
      ((7378365867951797981 : ℚ) / 20000000000000000000)
      ((18445914669879494953 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (882671775669 : ℝ) / 610351562500) (l := (882671775669 : ℝ) / 610351562500)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((882671775669 : ℝ) / 40000000000000000) ((882671775669 : ℝ) / 610351562500) (-16) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_4_1 :
    (-20582059428610475639 : ℝ) / 1000000000000000000 ≤ Real.log ((11516623361598563 : ℝ) / 10000000000000000000000000) ∧
    Real.log ((11516623361598563 : ℝ) / 10000000000000000000000000) ≤ (-20582059428610475637 : ℝ) / 1000000000000000000 := by
  have hb : (5308899704697091103 : ℝ) / 25000000000000000000 ≤ Real.log ((1236588017460385259 : ℝ) / 1000000000000000000) ∧
      Real.log ((1236588017460385259 : ℝ) / 1000000000000000000) ≤ (21235598818788364413 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1236588017460385259 : ℚ) / 1000000000000000000) 25
      ((5308899704697091103 : ℚ) / 25000000000000000000)
      ((21235598818788364413 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (368531947571154016 : ℝ) / 298023223876953125) (l := (1236588017460385259 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((11516623361598563 : ℝ) / 10000000000000000000000000) ((368531947571154016 : ℝ) / 298023223876953125) (-30) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_4_1 :
    (shellWeights ⟨4, by decide⟩ ⟨1, by decide⟩ : ℝ)^p ≤ powerUpper ⟨4, by decide⟩ ⟨1, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (882671775669 : ℝ) / 40000000000000000)
    (by norm_num : 0 < (11516623361598563 : ℝ) / 10000000000000000000000000) witness_basic.2.2.1.le
    weight_log_4_1.2 power_upper_log_4_1.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_4_2 :
    (-5340040100506946757 : ℝ) / 250000000000000000 ≤ Real.log ((52893244151477 : ℝ) / 100000000000000000000000) ∧
    Real.log ((52893244151477 : ℝ) / 100000000000000000000000) ≤ (-854406416081111481 : ℝ) / 40000000000000000 := by
  have hb : (6370109766525878247 : ℝ) / 50000000000000000000 ≤ Real.log ((45434950761987397 : ℝ) / 40000000000000000) ∧
      Real.log ((45434950761987397 : ℝ) / 40000000000000000) ≤ (2548043906610351299 : ℝ) / 20000000000000000000 := by
    have h := log_enclosure_of_rat
      ((45434950761987397 : ℚ) / 40000000000000000) 25
      ((6370109766525878247 : ℚ) / 50000000000000000000)
      ((2548043906610351299 : ℚ) / 20000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (13540670502778112 : ℝ) / 11920928955078125) (l := (45434950761987397 : ℝ) / 40000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((52893244151477 : ℝ) / 100000000000000000000000) ((13540670502778112 : ℝ) / 11920928955078125) (-31) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_4_2 :
    (-20502667104387388967 : ℝ) / 500000000000000000 ≤ Real.log ((1943209556149493 : ℝ) / 1250000000000000000000000000000000) ∧
    Real.log ((1943209556149493 : ℝ) / 1250000000000000000000000000000000) ≤ (-10251333552193694483 : ℝ) / 250000000000000000 := by
  have hb : (58349662482194063181 : ℝ) / 100000000000000000000 ≤ Real.log ((1792294468193821409 : ℝ) / 1000000000000000000) ∧
      Real.log ((1792294468193821409 : ℝ) / 1000000000000000000) ≤ (29174831241097031591 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1792294468193821409 : ℚ) / 1000000000000000000) 25
      ((58349662482194063181 : ℚ) / 100000000000000000000)
      ((29174831241097031591 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (1043252686617093515247616 : ℝ) / 582076609134674072265625) (l := (1792294468193821409 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1943209556149493 : ℝ) / 1250000000000000000000000000000000) ((1043252686617093515247616 : ℝ) / 582076609134674072265625) (-60) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_4_2 :
    (shellWeights ⟨4, by decide⟩ ⟨2, by decide⟩ : ℝ)^p ≤ powerUpper ⟨4, by decide⟩ ⟨2, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (52893244151477 : ℝ) / 100000000000000000000000)
    (by norm_num : 0 < (1943209556149493 : ℝ) / 1250000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_4_2.2 power_upper_log_4_2.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_4_3 :
    (-35667284898658658263 : ℝ) / 1000000000000000000 ≤ Real.log ((32351541879579 : ℝ) / 100000000000000000000000000000) ∧
    Real.log ((32351541879579 : ℝ) / 100000000000000000000000000000) ≤ (-35667284898658658261 : ℝ) / 1000000000000000000 := by
  have hb : (1505473961833991309 : ℝ) / 4000000000000000000 ≤ Real.log ((1456983919537329801 : ℝ) / 1000000000000000000) ∧
      Real.log ((1456983919537329801 : ℝ) / 1000000000000000000) ≤ (18818424522924891363 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1456983919537329801 : ℚ) / 1000000000000000000) 25
      ((1505473961833991309 : ℚ) / 4000000000000000000)
      ((18818424522924891363 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (271384403023371436032 : ℝ) / 186264514923095703125) (l := (1456983919537329801 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((32351541879579 : ℝ) / 100000000000000000000000000000) ((271384403023371436032 : ℝ) / 186264514923095703125) (-52) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_4_3 :
    (-34235439015014161381 : ℝ) / 500000000000000000 ≤ Real.log ((18343216860571769 : ℝ) / 10000000000000000000000000000000000000000000000) ∧
    Real.log ((18343216860571769 : ℝ) / 10000000000000000000000000000000000000000000000) ≤ (-68470878030028322759 : ℝ) / 1000000000000000000 := by
  have hb : (3013856908125257427 : ℝ) / 20000000000000000000 ≤ Real.log ((290659873292754759 : ℝ) / 250000000000000000) ∧
      Real.log ((290659873292754759 : ℝ) / 250000000000000000) ≤ (470915141894571473 : ℝ) / 3125000000000000000 := by
    have h := log_enclosure_of_rat
      ((290659873292754759 : ℚ) / 250000000000000000) 25
      ((3013856908125257427 : ℚ) / 20000000000000000000)
      ((470915141894571473 : ℚ) / 3125000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (165221009236094436698209122254848 : ℝ) / 142108547152020037174224853515625) (l := (290659873292754759 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((18343216860571769 : ℝ) / 10000000000000000000000000000000000000000000000) ((165221009236094436698209122254848 : ℝ) / 142108547152020037174224853515625) (-99) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_4_3 :
    (shellWeights ⟨4, by decide⟩ ⟨3, by decide⟩ : ℝ)^p ≤ powerUpper ⟨4, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (32351541879579 : ℝ) / 100000000000000000000000000000)
    (by norm_num : 0 < (18343216860571769 : ℝ) / 10000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_4_3.2 power_upper_log_4_3.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_4_4 :
    (-6017657215116805719 : ℝ) / 125000000000000000 ≤ Real.log ((3093552057317 : ℝ) / 2500000000000000000000000000000000) ∧
    Real.log ((3093552057317 : ℝ) / 2500000000000000000000000000000000) ≤ (-192565030883737783 : ℝ) / 4000000000000000 := by
  have hb : (37904491826172590749 : ℝ) / 100000000000000000000 ≤ Real.log ((730444327424311819 : ℝ) / 500000000000000000) ∧
      Real.log ((730444327424311819 : ℝ) / 500000000000000000) ≤ (151617967304690363 : ℝ) / 400000000000000000 := by
    have h := log_enclosure_of_rat
      ((730444327424311819 : ℚ) / 500000000000000000) 25
      ((37904491826172590749 : ℚ) / 100000000000000000000)
      ((151617967304690363 : ℚ) / 400000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (850349114537602080309248 : ℝ) / 582076609134674072265625) (l := (730444327424311819 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((3093552057317 : ℝ) / 2500000000000000000000000000000000) ((850349114537602080309248 : ℝ) / 582076609134674072265625) (-70) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_4_4 :
    (-92417300475434454403 : ℝ) / 1000000000000000000 ≤ Real.log ((73059445399869837 : ℝ) / 1000000000000000000000000000000000000000000000000000000000) ∧
    Real.log ((73059445399869837 : ℝ) / 1000000000000000000000000000000000000000000000000000000000) ≤ (-28880406398573267 : ℝ) / 312500000000000 := by
  have hb : (46442171959821705961 : ℝ) / 100000000000000000000 ≤ Real.log ((1591093824422321767 : ℝ) / 1000000000000000000) ∧
      Real.log ((1591093824422321767 : ℝ) / 1000000000000000000) ≤ (23221085979910852981 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1591093824422321767 : ℚ) / 1000000000000000000) 25
      ((46442171959821705961 : ℚ) / 100000000000000000000)
      ((23221085979910852981 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (11040431238828486477404303442190390001664 : ℝ) / 6938893903907228377647697925567626953125) (l := (1591093824422321767 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((73059445399869837 : ℝ) / 1000000000000000000000000000000000000000000000000000000000) ((11040431238828486477404303442190390001664 : ℝ) / 6938893903907228377647697925567626953125) (-134) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_4_4 :
    (shellWeights ⟨4, by decide⟩ ⟨4, by decide⟩ : ℝ)^p ≤ powerUpper ⟨4, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (3093552057317 : ℝ) / 2500000000000000000000000000000000)
    (by norm_num : 0 < (73059445399869837 : ℝ) / 1000000000000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_4_4.2 power_upper_log_4_4.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_4_5 :
    (-60615222011127506659 : ℝ) / 1000000000000000000 ≤ Real.log ((23665384530683 : ℝ) / 5000000000000000000000000000000000000000) ∧
    Real.log ((23665384530683 : ℝ) / 5000000000000000000000000000000000000000) ≤ (-1894225687847734583 : ℝ) / 31250000000000000 := by
  have hb : (38172987814768057039 : ℝ) / 100000000000000000000 ≤ Real.log ((732408176390433591 : ℝ) / 500000000000000000) ∧
      Real.log ((732408176390433591 : ℝ) / 500000000000000000) ≤ (477162347684600713 : ℝ) / 1250000000000000000 := by
    have h := log_enclosure_of_rat
      ((732408176390433591 : ℚ) / 500000000000000000) 25
      ((38172987814768057039 : ℚ) / 100000000000000000000)
      ((477162347684600713 : ℚ) / 1250000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (13322427119245432395290116096 : ℝ) / 9094947017729282379150390625) (l := (732408176390433591 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((23665384530683 : ℝ) / 5000000000000000000000000000000000000000) ((13322427119245432395290116096 : ℝ) / 9094947017729282379150390625) (-88) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_4_5 :
    (-116363706541707793213 : ℝ) / 1000000000000000000 ≤ Real.log ((1818713843254993 : ℝ) / 625000000000000000000000000000000000000000000000000000000000000000) ∧
    Real.log ((1818713843254993 : ℝ) / 625000000000000000000000000000000000000000000000000000000000000000) ≤ (-11636370654170779321 : ℝ) / 100000000000000000 := by
  have hb : (4250989618150938479 : ℝ) / 50000000000000000000 ≤ Real.log ((1088738615195054651 : ℝ) / 1000000000000000000) ∧
      Real.log ((1088738615195054651 : ℝ) / 1000000000000000000) ≤ (8501979236301876959 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1088738615195054651 : ℚ) / 1000000000000000000) 25
      ((4250989618150938479 : ℚ) / 50000000000000000000)
      ((8501979236301876959 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (73775798241458617644340990024180865933326155776 : ℝ) / 67762635780344027125465800054371356964111328125) (l := (1088738615195054651 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1818713843254993 : ℝ) / 625000000000000000000000000000000000000000000000000000000000000000) ((73775798241458617644340990024180865933326155776 : ℝ) / 67762635780344027125465800054371356964111328125) (-168) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_4_5 :
    (shellWeights ⟨4, by decide⟩ ⟨5, by decide⟩ : ℝ)^p ≤ powerUpper ⟨4, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (23665384530683 : ℝ) / 5000000000000000000000000000000000000000)
    (by norm_num : 0 < (1818713843254993 : ℝ) / 625000000000000000000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_4_5.2 power_upper_log_4_5.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem residue_log_4 :
    (149868454549898159 : ℝ) / 15625000000000000 ≤ Real.log ((14641 : ℝ) / 1) ∧
    Real.log ((14641 : ℝ) / 1) ≤ (9591581091193482177 : ℝ) / 1000000000000000000 := by
  have hb : (29033387195709657691 : ℝ) / 50000000000000000000 ≤ Real.log ((14641 : ℝ) / 8192) ∧
      Real.log ((14641 : ℝ) / 8192) ≤ (58066774391419315383 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((14641 : ℚ) / 8192) 25
      ((29033387195709657691 : ℚ) / 50000000000000000000)
      ((58066774391419315383 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (14641 : ℝ) / 8192) (l := (14641 : ℝ) / 8192)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((14641 : ℝ) / 1) ((14641 : ℝ) / 8192) (13) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem energy_log_4 :
    (549330360630729517 : ℝ) / 500000000000000000 ≤ Real.log ((3000145301298678983 : ℝ) / 1000000000000000000) ∧
    Real.log ((3000145301298678983 : ℝ) / 1000000000000000000) ≤ (274665180315364759 : ℝ) / 250000000000000000 := by
  have hb : (8110270814030274499 : ℝ) / 20000000000000000000 ≤ Real.log ((1500072650649339491 : ℝ) / 1000000000000000000) ∧
      Real.log ((1500072650649339491 : ℝ) / 1000000000000000000) ≤ (2534459629384460781 : ℝ) / 6250000000000000000 := by
    have h := log_enclosure_of_rat
      ((1500072650649339491 : ℚ) / 1000000000000000000) 25
      ((8110270814030274499 : ℚ) / 20000000000000000000)
      ((2534459629384460781 : ℚ) / 6250000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (3000145301298678983 : ℝ) / 2000000000000000000) (l := (1500072650649339491 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((3000145301298678983 : ℝ) / 1000000000000000000) ((3000145301298678983 : ℝ) / 2000000000000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem mass_log_4 :
    (16860527674511 : ℝ) / 1000000000000000000 ≤ Real.log ((1000016860669814007 : ℝ) / 1000000000000000000) ∧
    Real.log ((1000016860669814007 : ℝ) / 1000000000000000000) ≤ (16860527674513 : ℝ) / 1000000000000000000 := by
  have hb : (843026383725571 : ℝ) / 50000000000000000000 ≤ Real.log ((1000016860669814007 : ℝ) / 1000000000000000000) ∧
      Real.log ((1000016860669814007 : ℝ) / 1000000000000000000) ≤ (1686052767451143 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1000016860669814007 : ℚ) / 1000000000000000000) 25
      ((843026383725571 : ℚ) / 50000000000000000000)
      ((1686052767451143 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (1000016860669814007 : ℝ) / 1000000000000000000) (l := (1000016860669814007 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1000016860669814007 : ℝ) / 1000000000000000000) ((1000016860669814007 : ℝ) / 1000000000000000000) (0) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

end UnitDistance.Witness.FiniteCertificates
