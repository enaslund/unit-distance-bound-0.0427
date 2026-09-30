module

public import UnitDistance.PairMassPowerCertificate0
public import UnitDistance.PairMassPowerCertificate1
public import UnitDistance.PairMassPowerCertificate2
public import UnitDistance.PairMassPowerCertificate3
public import UnitDistance.PairMassPowerCertificate4
public import UnitDistance.PairMassPowerCertificate5
public import UnitDistance.PairMassPowerCertificate6
public import UnitDistance.PairMassPowerCertificate7

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
namespace UnitDistance.Witness

theorem pairMassCellCenter_comm (i j : Fin 8) :
    pairMassCellCenter i j = pairMassCellCenter j i := by
  unfold pairMassCellCenter pairMassCellLower pairMassCellUpper
  rw [polynomial_comm ((i : ℝ) / 8) ((j : ℝ) / 8),
    polynomial_comm (((i : ℕ) + 1 : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8)]

theorem pairMassCenterPowerUpper_comm (i j : Fin 8) :
    pairMassCenterPowerUpper i j = pairMassCenterPowerUpper j i := by
  fin_cases i <;> fin_cases j <;> norm_num [pairMassCenterPowerUpper, Matrix.cons_val]

theorem pairMassCellCenter_power_le (i j : Fin 8) :
    pairMassCellCenter i j ^ p ≤ pairMassCenterPowerUpper i j := by
  fin_cases i <;> fin_cases j
  · exact pairMassCenter_power_le_0_0
  · exact pairMassCenter_power_le_0_1
  · exact pairMassCenter_power_le_0_2
  · exact pairMassCenter_power_le_0_3
  · exact pairMassCenter_power_le_0_4
  · exact pairMassCenter_power_le_0_5
  · exact pairMassCenter_power_le_0_6
  · exact pairMassCenter_power_le_0_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_0_1
  · exact pairMassCenter_power_le_1_1
  · exact pairMassCenter_power_le_1_2
  · exact pairMassCenter_power_le_1_3
  · exact pairMassCenter_power_le_1_4
  · exact pairMassCenter_power_le_1_5
  · exact pairMassCenter_power_le_1_6
  · exact pairMassCenter_power_le_1_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_0_2
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_1_2
  · exact pairMassCenter_power_le_2_2
  · exact pairMassCenter_power_le_2_3
  · exact pairMassCenter_power_le_2_4
  · exact pairMassCenter_power_le_2_5
  · exact pairMassCenter_power_le_2_6
  · exact pairMassCenter_power_le_2_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_0_3
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_1_3
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_2_3
  · exact pairMassCenter_power_le_3_3
  · exact pairMassCenter_power_le_3_4
  · exact pairMassCenter_power_le_3_5
  · exact pairMassCenter_power_le_3_6
  · exact pairMassCenter_power_le_3_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_0_4
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_1_4
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_2_4
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_3_4
  · exact pairMassCenter_power_le_4_4
  · exact pairMassCenter_power_le_4_5
  · exact pairMassCenter_power_le_4_6
  · exact pairMassCenter_power_le_4_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_0_5
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_1_5
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_2_5
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_3_5
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_4_5
  · exact pairMassCenter_power_le_5_5
  · exact pairMassCenter_power_le_5_6
  · exact pairMassCenter_power_le_5_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_0_6
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_1_6
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_2_6
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_3_6
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_4_6
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_5_6
  · exact pairMassCenter_power_le_6_6
  · exact pairMassCenter_power_le_6_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_0_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_1_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_2_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_3_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_4_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_5_7
  · rw [pairMassCellCenter_comm, pairMassCenterPowerUpper_comm]
    exact pairMassCenter_power_le_6_7
  · exact pairMassCenter_power_le_7_7

end UnitDistance.Witness
