module

public import UnitDistance.PairMassDegree12Data
public import UnitDistance.RationalPowerBounds

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
namespace UnitDistance.Witness

private theorem pairMassCenter_log_4_4 :
    (71302308232272447 : ℝ) / 40000000000000000 ≤ Real.log ((623382905170263 : ℝ) / 104857600000000) ∧
    Real.log ((623382905170263 : ℝ) / 104857600000000) ≤ (1782557705806811177 : ℝ) / 1000000000000000000 := by
  have hb : (9906583617173013919 : ℝ) / 25000000000000000000 ≤ Real.log ((743130332434490919 : ℝ) / 500000000000000000) ∧
      Real.log ((743130332434490919 : ℝ) / 500000000000000000) ≤ (39626334468692055677 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((743130332434490919 : ℝ) / 500000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (623382905170263 : ℝ) / 419430400000000) (l := (743130332434490919 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((623382905170263 : ℝ) / 104857600000000) ((623382905170263 : ℝ) / 419430400000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_4_4 :
    (684399115898925837 : ℝ) / 200000000000000000 ≤ Real.log ((1531523981410149 : ℝ) / 50000000000000) ∧
    Real.log ((1531523981410149 : ℝ) / 50000000000000) ≤ (1710997789747314593 : ℝ) / 500000000000000000 := by
  have hb : (64940685725484794769 : ℝ) / 100000000000000000000 ≤ Real.log ((1531523981410149 : ℝ) / 800000000000000) ∧
      Real.log ((1531523981410149 : ℝ) / 800000000000000) ≤ (6494068572548479477 : ℝ) / 10000000000000000000 := by
    apply log_enclosure ((1531523981410149 : ℝ) / 800000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (1531523981410149 : ℝ) / 800000000000000) (l := (1531523981410149 : ℝ) / 800000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1531523981410149 : ℝ) / 50000000000000) ((1531523981410149 : ℝ) / 800000000000000) (4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_4_4 :
    pairMassCellCenter ⟨4, by decide⟩ ⟨4, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨4, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (623382905170263 : ℝ) / 104857600000000)
    (by norm_num : 0 < (1531523981410149 : ℝ) / 50000000000000) (by norm_num [p, increment])
    pairMassCenter_log_4_4.2 pairMassPowerUpper_log_4_4.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_4_5 :
    (239021348325522527 : ℝ) / 125000000000000000 ≤ Real.log ((2217660984882191 : ℝ) / 327680000000000) ∧
    Real.log ((2217660984882191 : ℝ) / 327680000000000) ≤ (1912170786604180217 : ℝ) / 1000000000000000000 := by
  have hb : (52587642548428959729 : ℝ) / 100000000000000000000 ≤ Real.log ((845970529511333847 : ℝ) / 500000000000000000) ∧
      Real.log ((845970529511333847 : ℝ) / 500000000000000000) ≤ (5258764254842895973 : ℝ) / 10000000000000000000 := by
    apply log_enclosure ((845970529511333847 : ℝ) / 500000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (2217660984882191 : ℝ) / 1310720000000000) (l := (845970529511333847 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2217660984882191 : ℝ) / 327680000000000) ((2217660984882191 : ℝ) / 1310720000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_4_5 :
    (3670815232338645521 : ℝ) / 1000000000000000000 ≤ Real.log ((3928391833034273 : ℝ) / 100000000000000) ∧
    Real.log ((3928391833034273 : ℝ) / 100000000000000) ≤ (1835407616169322761 : ℝ) / 500000000000000000 := by
  have hb : (10253966476945948701 : ℝ) / 50000000000000000000 ≤ Real.log ((153452805977901289 : ℝ) / 125000000000000000) ∧
      Real.log ((153452805977901289 : ℝ) / 125000000000000000) ≤ (20507932953891897403 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((153452805977901289 : ℝ) / 125000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (3928391833034273 : ℝ) / 3200000000000000) (l := (153452805977901289 : ℝ) / 125000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((3928391833034273 : ℝ) / 100000000000000) ((3928391833034273 : ℝ) / 3200000000000000) (5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_4_5 :
    pairMassCellCenter ⟨4, by decide⟩ ⟨5, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨4, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (2217660984882191 : ℝ) / 327680000000000)
    (by norm_num : 0 < (3928391833034273 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_4_5.2 pairMassPowerUpper_log_4_5.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_4_6 :
    (2049629104933004743 : ℝ) / 1000000000000000000 ≤ Real.log ((20355535508151893 : ℝ) / 2621440000000000) ∧
    Real.log ((20355535508151893 : ℝ) / 2621440000000000) ≤ (256203638116625593 : ℝ) / 125000000000000000 := by
  have hb : (6633347438131141243 : ℝ) / 10000000000000000000 ≤ Real.log ((15166055789703051 : ℝ) / 7812500000000000) ∧
      Real.log ((15166055789703051 : ℝ) / 7812500000000000) ≤ (66333474381311412431 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((15166055789703051 : ℝ) / 7812500000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (20355535508151893 : ℝ) / 10485760000000000) (l := (15166055789703051 : ℝ) / 7812500000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((20355535508151893 : ℝ) / 2621440000000000) ((20355535508151893 : ℝ) / 10485760000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_4_6 :
    (983673868430211491 : ℝ) / 250000000000000000 ≤ Real.log ((639332151369373 : ℝ) / 12500000000000) ∧
    Real.log ((639332151369373 : ℝ) / 12500000000000) ≤ (1967347736860422983 : ℝ) / 500000000000000000 := by
  have hb : (46895957092111941777 : ℝ) / 100000000000000000000 ≤ Real.log ((639332151369373 : ℝ) / 400000000000000) ∧
      Real.log ((639332151369373 : ℝ) / 400000000000000) ≤ (23447978546055970889 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((639332151369373 : ℝ) / 400000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (639332151369373 : ℝ) / 400000000000000) (l := (639332151369373 : ℝ) / 400000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((639332151369373 : ℝ) / 12500000000000) ((639332151369373 : ℝ) / 400000000000000) (5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_4_6 :
    pairMassCellCenter ⟨4, by decide⟩ ⟨6, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨4, by decide⟩ ⟨6, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (20355535508151893 : ℝ) / 2621440000000000)
    (by norm_num : 0 < (639332151369373 : ℝ) / 12500000000000) (by norm_num [p, increment])
    pairMassCenter_log_4_6.2 pairMassPowerUpper_log_4_6.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_4_7 :
    (2195116749099706831 : ℝ) / 1000000000000000000 ≤ Real.log ((36786378854649 : ℝ) / 4096000000000) ∧
    Real.log ((36786378854649 : ℝ) / 4096000000000) ≤ (2195116749099706833 : ℝ) / 1000000000000000000 := by
  have hb : (2313504148397418063 : ℝ) / 20000000000000000000 ≤ Real.log ((280657797658149719 : ℝ) / 250000000000000000) ∧
      Real.log ((280657797658149719 : ℝ) / 250000000000000000) ≤ (2891880185496772579 : ℝ) / 25000000000000000000 := by
    apply log_enclosure ((280657797658149719 : ℝ) / 250000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (36786378854649 : ℝ) / 32768000000000) (l := (280657797658149719 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((36786378854649 : ℝ) / 4096000000000) ((36786378854649 : ℝ) / 32768000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_4_7 :
    (4213989699982208019 : ℝ) / 1000000000000000000 ≤ Real.log ((676258089902413 : ℝ) / 10000000000000) ∧
    Real.log ((676258089902413 : ℝ) / 10000000000000) ≤ (4213989699982208021 : ℝ) / 1000000000000000000 := by
  have hb : (551066166225361633 : ℝ) / 10000000000000000000 ≤ Real.log ((132081658184065039 : ℝ) / 125000000000000000) ∧
      Real.log ((132081658184065039 : ℝ) / 125000000000000000) ≤ (5510661662253616331 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((132081658184065039 : ℝ) / 125000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (676258089902413 : ℝ) / 640000000000000) (l := (132081658184065039 : ℝ) / 125000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((676258089902413 : ℝ) / 10000000000000) ((676258089902413 : ℝ) / 640000000000000) (6) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_4_7 :
    pairMassCellCenter ⟨4, by decide⟩ ⟨7, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨4, by decide⟩ ⟨7, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (36786378854649 : ℝ) / 4096000000000)
    (by norm_num : 0 < (676258089902413 : ℝ) / 10000000000000) (by norm_num [p, increment])
    pairMassCenter_log_4_7.2 pairMassPowerUpper_log_4_7.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

end UnitDistance.Witness
