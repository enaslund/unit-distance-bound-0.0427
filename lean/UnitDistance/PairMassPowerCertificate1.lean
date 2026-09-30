module

public import UnitDistance.PairMassDegree12Data
public import UnitDistance.RationalPowerBounds

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
namespace UnitDistance.Witness

private theorem pairMassCenter_log_1_1 :
    (226263960247185977 : ℝ) / 250000000000000000 ≤ Real.log ((6480383081275047 : ℝ) / 2621440000000000) ∧
    Real.log ((6480383081275047 : ℝ) / 2621440000000000) ≤ (90505584098874391 : ℝ) / 100000000000000000 := by
  have hb : (21190866042879859941 : ℝ) / 100000000000000000000 ≤ Real.log ((38626093156785053 : ℝ) / 31250000000000000) ∧
      Real.log ((38626093156785053 : ℝ) / 31250000000000000) ≤ (10595433021439929971 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((38626093156785053 : ℝ) / 31250000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (6480383081275047 : ℝ) / 5242880000000000) (l := (38626093156785053 : ℝ) / 31250000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((6480383081275047 : ℝ) / 2621440000000000) ((6480383081275047 : ℝ) / 5242880000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_1_1 :
    (3474891249770217 : ℝ) / 2000000000000000 ≤ Real.log ((568280884170107 : ℝ) / 100000000000000) ∧
    Real.log ((568280884170107 : ℝ) / 100000000000000) ≤ (868722812442554251 : ℝ) / 500000000000000000 := by
  have hb : (4389390797065223523 : ℝ) / 12500000000000000000 ≤ Real.log ((568280884170107 : ℝ) / 400000000000000) ∧
      Real.log ((568280884170107 : ℝ) / 400000000000000) ≤ (7023025275304357637 : ℝ) / 20000000000000000000 := by
    apply log_enclosure ((568280884170107 : ℝ) / 400000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (568280884170107 : ℝ) / 400000000000000) (l := (568280884170107 : ℝ) / 400000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((568280884170107 : ℝ) / 100000000000000) ((568280884170107 : ℝ) / 400000000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_1_1 :
    pairMassCellCenter ⟨1, by decide⟩ ⟨1, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨1, by decide⟩ ⟨1, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (6480383081275047 : ℝ) / 2621440000000000)
    (by norm_num : 0 < (568280884170107 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_1_1.2 pairMassPowerUpper_log_1_1.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_1_2 :
    (271035995832997301 : ℝ) / 250000000000000000 ≤ Real.log ((48445973674453 : ℝ) / 16384000000000) ∧
    Real.log ((48445973674453 : ℝ) / 16384000000000) ≤ (216828796666397841 : ℝ) / 200000000000000000 := by
  have hb : (39099680277204389477 : ℝ) / 100000000000000000000 ≤ Real.log ((184806723306476593 : ℝ) / 125000000000000000) ∧
      Real.log ((184806723306476593 : ℝ) / 125000000000000000) ≤ (19549840138602194739 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((184806723306476593 : ℝ) / 125000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (48445973674453 : ℝ) / 32768000000000) (l := (184806723306476593 : ℝ) / 125000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((48445973674453 : ℝ) / 16384000000000) ((48445973674453 : ℝ) / 32768000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_1_2 :
    (2081243096036882177 : ℝ) / 1000000000000000000 ≤ Real.log ((160288508500969 : ℝ) / 20000000000000) ∧
    Real.log ((160288508500969 : ℝ) / 20000000000000) ≤ (2081243096036882179 : ℝ) / 1000000000000000000 := by
  have hb : (90077717852312469 : ℝ) / 50000000000000000000 ≤ Real.log ((160288508500969 : ℝ) / 160000000000000) ∧
      Real.log ((160288508500969 : ℝ) / 160000000000000) ≤ (180155435704624939 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((160288508500969 : ℝ) / 160000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (160288508500969 : ℝ) / 160000000000000) (l := (160288508500969 : ℝ) / 160000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((160288508500969 : ℝ) / 20000000000000) ((160288508500969 : ℝ) / 160000000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_1_2 :
    pairMassCellCenter ⟨1, by decide⟩ ⟨2, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (48445973674453 : ℝ) / 16384000000000)
    (by norm_num : 0 < (160288508500969 : ℝ) / 20000000000000) (by norm_num [p, increment])
    pairMassCenter_log_1_2.2 pairMassPowerUpper_log_1_2.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_1_3 :
    (249253500417632827 : ℝ) / 200000000000000000 ≤ Real.log ((364625478797789 : ℝ) / 104857600000000) ∧
    Real.log ((364625478797789 : ℝ) / 104857600000000) ≤ (1246267502088164137 : ℝ) / 1000000000000000000 := by
  have hb : (27656016076410941317 : ℝ) / 50000000000000000000 ≤ Real.log ((869334885591957569 : ℝ) / 500000000000000000) ∧
      Real.log ((869334885591957569 : ℝ) / 500000000000000000) ≤ (11062406430564376527 : ℝ) / 20000000000000000000 := by
    apply log_enclosure ((869334885591957569 : ℝ) / 500000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (364625478797789 : ℝ) / 209715200000000) (l := (869334885591957569 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((364625478797789 : ℝ) / 104857600000000) ((364625478797789 : ℝ) / 209715200000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_1_3 :
    (1196236696607596907 : ℝ) / 500000000000000000 ≤ Real.log ((13675650893817 : ℝ) / 1250000000000) ∧
    Real.log ((13675650893817 : ℝ) / 1250000000000) ≤ (299059174151899227 : ℝ) / 125000000000000000 := by
  have hb : (31303185153535788643 : ℝ) / 100000000000000000000 ≤ Real.log ((13675650893817 : ℝ) / 10000000000000) ∧
      Real.log ((13675650893817 : ℝ) / 10000000000000) ≤ (7825796288383947161 : ℝ) / 25000000000000000000 := by
    apply log_enclosure ((13675650893817 : ℝ) / 10000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (13675650893817 : ℝ) / 10000000000000) (l := (13675650893817 : ℝ) / 10000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((13675650893817 : ℝ) / 1250000000000) ((13675650893817 : ℝ) / 10000000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_1_3 :
    pairMassCellCenter ⟨1, by decide⟩ ⟨3, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨1, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (364625478797789 : ℝ) / 104857600000000)
    (by norm_num : 0 < (13675650893817 : ℝ) / 1250000000000) (by norm_num [p, increment])
    pairMassCenter_log_1_3.2 pairMassPowerUpper_log_1_3.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_1_4 :
    (1406515437774779319 : ℝ) / 1000000000000000000 ≤ Real.log ((1337493956407161 : ℝ) / 327680000000000) ∧
    Real.log ((1337493956407161 : ℝ) / 327680000000000) ≤ (1406515437774779321 : ℝ) / 1000000000000000000 := by
  have hb : (1011053832744435029 : ℝ) / 50000000000000000000 ≤ Real.log ((1020426907659272003 : ℝ) / 1000000000000000000) ∧
      Real.log ((1020426907659272003 : ℝ) / 1000000000000000000) ≤ (2022107665488870059 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1020426907659272003 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (1337493956407161 : ℝ) / 1310720000000000) (l := (1020426907659272003 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1337493956407161 : ℝ) / 327680000000000) ((1337493956407161 : ℝ) / 1310720000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_1_4 :
    (1350051556501441847 : ℝ) / 500000000000000000 ≤ Real.log ((1488126609779863 : ℝ) / 100000000000000) ∧
    Real.log ((1488126609779863 : ℝ) / 100000000000000) ≤ (168756444562680231 : ℝ) / 62500000000000000 := by
  have hb : (31033078566152388331 : ℝ) / 50000000000000000000 ≤ Real.log ((1488126609779863 : ℝ) / 800000000000000) ∧
      Real.log ((1488126609779863 : ℝ) / 800000000000000) ≤ (62066157132304776663 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1488126609779863 : ℝ) / 800000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (1488126609779863 : ℝ) / 800000000000000) (l := (1488126609779863 : ℝ) / 800000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1488126609779863 : ℝ) / 100000000000000) ((1488126609779863 : ℝ) / 800000000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_1_4 :
    pairMassCellCenter ⟨1, by decide⟩ ⟨4, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨1, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (1337493956407161 : ℝ) / 327680000000000)
    (by norm_num : 0 < (1488126609779863 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_1_4.2 pairMassPowerUpper_log_1_4.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_1_5 :
    (786216146258524137 : ℝ) / 500000000000000000 ≤ Real.log ((505240994229427 : ℝ) / 104857600000000) ∧
    Real.log ((505240994229427 : ℝ) / 104857600000000) ≤ (393108073129262069 : ℝ) / 250000000000000000 := by
  have hb : (9306896569857882799 : ℝ) / 50000000000000000000 ≤ Real.log ((602294199740203619 : ℝ) / 500000000000000000) ∧
      Real.log ((602294199740203619 : ℝ) / 500000000000000000) ≤ (18613793139715765599 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((602294199740203619 : ℝ) / 500000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (505240994229427 : ℝ) / 419430400000000) (l := (602294199740203619 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((505240994229427 : ℝ) / 104857600000000) ((505240994229427 : ℝ) / 419430400000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_1_5 :
    (3018615518880210643 : ℝ) / 1000000000000000000 ≤ Real.log ((2046294150740677 : ℝ) / 100000000000000) ∧
    Real.log ((2046294150740677 : ℝ) / 100000000000000) ≤ (603723103776042129 : ℝ) / 200000000000000000 := by
  have hb : (24602679664042940633 : ℝ) / 100000000000000000000 ≤ Real.log ((2046294150740677 : ℝ) / 1600000000000000) ∧
      Real.log ((2046294150740677 : ℝ) / 1600000000000000) ≤ (12301339832021470317 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((2046294150740677 : ℝ) / 1600000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (2046294150740677 : ℝ) / 1600000000000000) (l := (2046294150740677 : ℝ) / 1600000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2046294150740677 : ℝ) / 100000000000000) ((2046294150740677 : ℝ) / 1600000000000000) (4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_1_5 :
    pairMassCellCenter ⟨1, by decide⟩ ⟨5, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨1, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (505240994229427 : ℝ) / 104857600000000)
    (by norm_num : 0 < (2046294150740677 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_1_5.2 pairMassPowerUpper_log_1_5.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_1_6 :
    (1746695714139577769 : ℝ) / 1000000000000000000 ≤ Real.log ((939723850454087 : ℝ) / 163840000000000) ∧
    Real.log ((939723850454087 : ℝ) / 163840000000000) ≤ (1746695714139577771 : ℝ) / 1000000000000000000 := by
  have hb : (36040135301968715097 : ℝ) / 100000000000000000000 ≤ Real.log ((1433904801107920837 : ℝ) / 1000000000000000000) ∧
      Real.log ((1433904801107920837 : ℝ) / 1000000000000000000) ≤ (18020067650984357549 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((1433904801107920837 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (939723850454087 : ℝ) / 655360000000000) (l := (1433904801107920837 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((939723850454087 : ℝ) / 163840000000000) ((939723850454087 : ℝ) / 655360000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_1_6 :
    (419143865093170283 : ℝ) / 125000000000000000 ≤ Real.log ((17870428211937 : ℝ) / 625000000000) ∧
    Real.log ((17870428211937 : ℝ) / 625000000000) ≤ (1676575460372681133 : ℝ) / 500000000000000000 := by
  have hb : (58056219850558102697 : ℝ) / 100000000000000000000 ≤ Real.log ((17870428211937 : ℝ) / 10000000000000) ∧
      Real.log ((17870428211937 : ℝ) / 10000000000000) ≤ (29028109925279051349 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((17870428211937 : ℝ) / 10000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (17870428211937 : ℝ) / 10000000000000) (l := (17870428211937 : ℝ) / 10000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((17870428211937 : ℝ) / 625000000000) ((17870428211937 : ℝ) / 10000000000000) (4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_1_6 :
    pairMassCellCenter ⟨1, by decide⟩ ⟨6, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨1, by decide⟩ ⟨6, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (939723850454087 : ℝ) / 163840000000000)
    (by norm_num : 0 < (17870428211937 : ℝ) / 625000000000) (by norm_num [p, increment])
    pairMassCenter_log_1_6.2 pairMassPowerUpper_log_1_6.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_1_7 :
    (964443480239454453 : ℝ) / 500000000000000000 ≤ Real.log ((3608069385946389 : ℝ) / 524288000000000) ∧
    Real.log ((3608069385946389 : ℝ) / 524288000000000) ≤ (482221740119727227 : ℝ) / 250000000000000000 := by
  have hb : (54259259935901828767 : ℝ) / 100000000000000000000 ≤ Real.log ((344092310518874073 : ℝ) / 200000000000000000) ∧
      Real.log ((344092310518874073 : ℝ) / 200000000000000000) ≤ (1695601872996932149 : ℝ) / 3125000000000000000 := by
    apply log_enclosure ((344092310518874073 : ℝ) / 200000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (3608069385946389 : ℝ) / 2097152000000000) (l := (344092310518874073 : ℝ) / 200000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((3608069385946389 : ℝ) / 524288000000000) ((3608069385946389 : ℝ) / 2097152000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_1_7 :
    (1851452727337124863 : ℝ) / 500000000000000000 ≤ Real.log ((4056499305637683 : ℝ) / 100000000000000) ∧
    Real.log ((4056499305637683 : ℝ) / 100000000000000) ≤ (1808059304040161 : ℝ) / 488281250000000 := by
  have hb : (23716955187452317979 : ℝ) / 100000000000000000000 ≤ Real.log ((1267656033011775937 : ℝ) / 1000000000000000000) ∧
      Real.log ((1267656033011775937 : ℝ) / 1000000000000000000) ≤ (1185847759372615899 : ℝ) / 5000000000000000000 := by
    apply log_enclosure ((1267656033011775937 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (4056499305637683 : ℝ) / 3200000000000000) (l := (1267656033011775937 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((4056499305637683 : ℝ) / 100000000000000) ((4056499305637683 : ℝ) / 3200000000000000) (5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_1_7 :
    pairMassCellCenter ⟨1, by decide⟩ ⟨7, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨1, by decide⟩ ⟨7, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (3608069385946389 : ℝ) / 524288000000000)
    (by norm_num : 0 < (4056499305637683 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_1_7.2 pairMassPowerUpper_log_1_7.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

end UnitDistance.Witness
