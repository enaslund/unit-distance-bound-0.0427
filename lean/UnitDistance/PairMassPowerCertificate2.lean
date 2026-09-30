module

public import UnitDistance.PairMassDegree12Data
public import UnitDistance.RationalPowerBounds

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
namespace UnitDistance.Witness

private theorem pairMassCenter_log_2_2 :
    (621830034001447829 : ℝ) / 500000000000000000 ≤ Real.log ((9091899507783007 : ℝ) / 2621440000000000) ∧
    Real.log ((9091899507783007 : ℝ) / 2621440000000000) ≤ (62183003400144783 : ℝ) / 50000000000000000 := by
  have hb : (550512887442950349 : ℝ) / 1000000000000000000 ≤ Real.log ((173414220958385601 : ℝ) / 100000000000000000) ∧
      Real.log ((173414220958385601 : ℝ) / 100000000000000000) ≤ (55051288744295034901 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((173414220958385601 : ℝ) / 100000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (9091899507783007 : ℝ) / 5242880000000000) (l := (173414220958385601 : ℝ) / 100000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((9091899507783007 : ℝ) / 2621440000000000) ((9091899507783007 : ℝ) / 5242880000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_2_2 :
    (2387467873402541331 : ℝ) / 1000000000000000000 ≤ Real.log ((544294727604003 : ℝ) / 50000000000000) ∧
    Real.log ((544294727604003 : ℝ) / 50000000000000) ≤ (2387467873402541333 : ℝ) / 1000000000000000000 := by
  have hb : (30802633172270540353 : ℝ) / 100000000000000000000 ≤ Real.log ((544294727604003 : ℝ) / 400000000000000) ∧
      Real.log ((544294727604003 : ℝ) / 400000000000000) ≤ (15401316586135270177 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((544294727604003 : ℝ) / 400000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (544294727604003 : ℝ) / 400000000000000) (l := (544294727604003 : ℝ) / 400000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((544294727604003 : ℝ) / 50000000000000) ((544294727604003 : ℝ) / 400000000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_2_2 :
    pairMassCellCenter ⟨2, by decide⟩ ⟨2, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨2, by decide⟩ ⟨2, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (9091899507783007 : ℝ) / 2621440000000000)
    (by norm_num : 0 < (544294727604003 : ℝ) / 50000000000000) (by norm_num [p, increment])
    pairMassCenter_log_2_2.2 pairMassPowerUpper_log_2_2.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_2_3 :
    (1390275333791466481 : ℝ) / 1000000000000000000 ≤ Real.log ((1315948340535527 : ℝ) / 327680000000000) ∧
    Real.log ((1315948340535527 : ℝ) / 327680000000000) ≤ (1390275333791466483 : ℝ) / 1000000000000000000 := by
  have hb : (79619453431517251 : ℝ) / 20000000000000000000 ≤ Real.log ((1003988907268926239 : ℝ) / 1000000000000000000) ∧
      Real.log ((1003988907268926239 : ℝ) / 1000000000000000000) ≤ (24881079197349141 : ℝ) / 6250000000000000000 := by
    apply log_enclosure ((1003988907268926239 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (1315948340535527 : ℝ) / 1310720000000000) (l := (1003988907268926239 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1315948340535527 : ℝ) / 327680000000000) ((1315948340535527 : ℝ) / 1310720000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_2_3 :
    (1334463403629757733 : ℝ) / 500000000000000000 ≤ Real.log ((721224031764133 : ℝ) / 50000000000000) ∧
    Real.log ((721224031764133 : ℝ) / 50000000000000) ≤ (667231701814878867 : ℝ) / 250000000000000000 := by
  have hb : (11789705311593590771 : ℝ) / 20000000000000000000 ≤ Real.log ((721224031764133 : ℝ) / 400000000000000) ∧
      Real.log ((721224031764133 : ℝ) / 400000000000000) ≤ (921070727468249279 : ℝ) / 1562500000000000000 := by
    apply log_enclosure ((721224031764133 : ℝ) / 400000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (721224031764133 : ℝ) / 400000000000000) (l := (721224031764133 : ℝ) / 400000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((721224031764133 : ℝ) / 50000000000000) ((721224031764133 : ℝ) / 400000000000000) (3) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_2_3 :
    pairMassCellCenter ⟨2, by decide⟩ ⟨3, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨2, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (1315948340535527 : ℝ) / 327680000000000)
    (by norm_num : 0 < (721224031764133 : ℝ) / 50000000000000) (by norm_num [p, increment])
    pairMassCenter_log_2_3.2 pairMassPowerUpper_log_2_3.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_2_4 :
    (1536060924226653183 : ℝ) / 1000000000000000000 ≤ Real.log ((2435974293158429 : ℝ) / 524288000000000) ∧
    Real.log ((2435974293158429 : ℝ) / 524288000000000) ≤ (307212184845330637 : ℝ) / 200000000000000000 := by
  have hb : (3744164077669064127 : ℝ) / 25000000000000000000 ≤ Real.log ((580781529702765703 : ℝ) / 500000000000000000) ∧
      Real.log ((580781529702765703 : ℝ) / 500000000000000000) ≤ (14976656310676256509 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((580781529702765703 : ℝ) / 500000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (2435974293158429 : ℝ) / 2097152000000000) (l := (580781529702765703 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2435974293158429 : ℝ) / 524288000000000) ((2435974293158429 : ℝ) / 2097152000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_2_4 :
    (147439650212022833 : ℝ) / 50000000000000000 ≤ Real.log ((954145341732451 : ℝ) / 50000000000000) ∧
    Real.log ((954145341732451 : ℝ) / 50000000000000) ≤ (1474396502120228331 : ℝ) / 500000000000000000 := by
  have hb : (17620428200067542331 : ℝ) / 100000000000000000000 ≤ Real.log ((954145341732451 : ℝ) / 800000000000000) ∧
      Real.log ((954145341732451 : ℝ) / 800000000000000) ≤ (4405107050016885583 : ℝ) / 25000000000000000000 := by
    apply log_enclosure ((954145341732451 : ℝ) / 800000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (954145341732451 : ℝ) / 800000000000000) (l := (954145341732451 : ℝ) / 800000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((954145341732451 : ℝ) / 50000000000000) ((954145341732451 : ℝ) / 800000000000000) (4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_2_4 :
    pairMassCellCenter ⟨2, by decide⟩ ⟨4, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨2, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (2435974293158429 : ℝ) / 524288000000000)
    (by norm_num : 0 < (954145341732451 : ℝ) / 50000000000000) (by norm_num [p, increment])
    pairMassCenter_log_2_4.2 pairMassPowerUpper_log_2_4.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_2_5 :
    (843708965248197793 : ℝ) / 500000000000000000 ≤ Real.log ((885637985042677 : ℝ) / 163840000000000) ∧
    Real.log ((885637985042677 : ℝ) / 163840000000000) ≤ (421854482624098897 : ℝ) / 250000000000000000 := by
  have hb : (15056178468825248391 : ℝ) / 50000000000000000000 ≤ Real.log ((16892203999379673 : ℝ) / 12500000000000000) ∧
      Real.log ((16892203999379673 : ℝ) / 12500000000000000) ≤ (30112356937650496783 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((16892203999379673 : ℝ) / 12500000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (885637985042677 : ℝ) / 655360000000000) (l := (16892203999379673 : ℝ) / 12500000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((885637985042677 : ℝ) / 163840000000000) ((885637985042677 : ℝ) / 655360000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_2_5 :
    (809838677327011697 : ℝ) / 250000000000000000 ≤ Real.log ((2551725038935559 : ℝ) / 100000000000000) ∧
    Real.log ((2551725038935559 : ℝ) / 100000000000000) ≤ (3239354709308046789 : ℝ) / 1000000000000000000 := by
  have hb : (9335319741365311013 : ℝ) / 20000000000000000000 ≤ Real.log ((2551725038935559 : ℝ) / 1600000000000000) ∧
      Real.log ((2551725038935559 : ℝ) / 1600000000000000) ≤ (23338299353413277533 : ℝ) / 50000000000000000000 := by
    apply log_enclosure ((2551725038935559 : ℝ) / 1600000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (2551725038935559 : ℝ) / 1600000000000000) (l := (2551725038935559 : ℝ) / 1600000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2551725038935559 : ℝ) / 100000000000000) ((2551725038935559 : ℝ) / 1600000000000000) (4) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_2_5 :
    pairMassCellCenter ⟨2, by decide⟩ ⟨5, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨2, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (885637985042677 : ℝ) / 163840000000000)
    (by norm_num : 0 < (2551725038935559 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_2_5.2 pairMassPowerUpper_log_2_5.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_2_6 :
    (923442995458240393 : ℝ) / 500000000000000000 ≤ Real.log ((3324009927466463 : ℝ) / 524288000000000) ∧
    Real.log ((3324009927466463 : ℝ) / 524288000000000) ≤ (461721497729120197 : ℝ) / 250000000000000000 := by
  have hb : (46059162979659016771 : ℝ) / 100000000000000000000 ≤ Real.log ((1585011447652083873 : ℝ) / 1000000000000000000) ∧
      Real.log ((1585011447652083873 : ℝ) / 1000000000000000000) ≤ (11514790744914754193 : ℝ) / 25000000000000000000 := by
    apply log_enclosure ((1585011447652083873 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (3324009927466463 : ℝ) / 2097152000000000) (l := (1585011447652083873 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((3324009927466463 : ℝ) / 524288000000000) ((3324009927466463 : ℝ) / 2097152000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_2_6 :
    (709097458798532013 : ℝ) / 200000000000000000 ≤ Real.log ((1732828458309733 : ℝ) / 50000000000000) ∧
    Real.log ((1732828458309733 : ℝ) / 50000000000000) ≤ (1772743646996330033 : ℝ) / 500000000000000000 := by
  have hb : (1993784779823337949 : ℝ) / 25000000000000000000 ≤ Real.log ((1732828458309733 : ℝ) / 1600000000000000) ∧
      Real.log ((1732828458309733 : ℝ) / 1600000000000000) ≤ (7975139119293351797 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1732828458309733 : ℝ) / 1600000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (1732828458309733 : ℝ) / 1600000000000000) (l := (1732828458309733 : ℝ) / 1600000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1732828458309733 : ℝ) / 50000000000000) ((1732828458309733 : ℝ) / 1600000000000000) (5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_2_6 :
    pairMassCellCenter ⟨2, by decide⟩ ⟨6, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨2, by decide⟩ ⟨6, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (3324009927466463 : ℝ) / 524288000000000)
    (by norm_num : 0 < (1732828458309733 : ℝ) / 50000000000000) (by norm_num [p, increment])
    pairMassCenter_log_2_6.2 pairMassPowerUpper_log_2_6.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

private theorem pairMassCenter_log_2_7 :
    (100719843323642939 : ℝ) / 50000000000000000 ≤ Real.log ((2456356390514579 : ℝ) / 327680000000000) ∧
    Real.log ((2456356390514579 : ℝ) / 327680000000000) ≤ (2014396866472858781 : ℝ) / 1000000000000000000 := by
  have hb : (392564065845605101 : ℝ) / 625000000000000000 ≤ Real.log ((1874051201259291839 : ℝ) / 1000000000000000000) ∧
      Real.log ((1874051201259291839 : ℝ) / 1000000000000000000) ≤ (62810250535296816161 : ℝ) / 100000000000000000000 := by
    apply log_enclosure ((1874051201259291839 : ℝ) / 1000000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (2456356390514579 : ℝ) / 1310720000000000) (l := (1874051201259291839 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2456356390514579 : ℝ) / 327680000000000) ((2456356390514579 : ℝ) / 1310720000000000) (2) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

private theorem pairMassPowerUpper_log_2_7 :
    (773411951822111499 : ℝ) / 200000000000000000 ≤ Real.log ((4780163094533189 : ℝ) / 100000000000000) ∧
    Real.log ((4780163094533189 : ℝ) / 100000000000000) ≤ (3867059759110557497 : ℝ) / 1000000000000000000 := by
  have hb : (10033096407770773711 : ℝ) / 25000000000000000000 ≤ Real.log ((746900483520810781 : ℝ) / 500000000000000000) ∧
      Real.log ((746900483520810781 : ℝ) / 500000000000000000) ≤ (8026477126216618969 : ℝ) / 20000000000000000000 := by
    apply log_enclosure ((746900483520810781 : ℝ) / 500000000000000000) 25 (by norm_num)
    · norm_num [Finset.sum_range_succ]
    · norm_num [Finset.sum_range_succ]
  have hr := log_bounds_of_lower (x := (4780163094533189 : ℝ) / 3200000000000000) (l := (746900483520810781 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((4780163094533189 : ℝ) / 100000000000000) ((4780163094533189 : ℝ) / 3200000000000000) (5) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem pairMassCenter_power_le_2_7 :
    pairMassCellCenter ⟨2, by decide⟩ ⟨7, by decide⟩ ^ p ≤
      pairMassCenterPowerUpper ⟨2, by decide⟩ ⟨7, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (2456356390514579 : ℝ) / 327680000000000)
    (by norm_num : 0 < (4780163094533189 : ℝ) / 100000000000000) (by norm_num [p, increment])
    pairMassCenter_log_2_7.2 pairMassPowerUpper_log_2_7.1
    (by norm_num [p, increment])
  norm_num [pairMassCellCenter, pairMassCellLower, pairMassCellUpper,
    polynomial, bernstein3, bernsteinCoefficients, Nat.choose,
    pairMassCenterPowerUpper, Matrix.cons_val, Fin.sum_univ_succ] at h ⊢
  exact h

end UnitDistance.Witness
