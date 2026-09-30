module

public import UnitDistance.PairMassDegree3Data
public import UnitDistance.PairMassDegree3Certificate
public import UnitDistance.PairMassPowerCertificate
public import UnitDistance.PairMassNormalization

@[expose] public section
set_option backward.privateInPublic true


/-! Summing the 64 certified cell majorants over the literal beta square. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped BigOperators
namespace UnitDistance.Witness

def pairMassBetaIntegrand (t u : ℝ) : ℝ :=
  betaDensity (6/5:ℝ) t * betaDensity (6/5:ℝ) u * (polynomial t u)^p

theorem continuous_pairMassBetaIntegrand : Continuous pairMassBetaIntegrand.uncurry := by
  have hpol : Continuous (fun tu : ℝ × ℝ => polynomial tu.1 tu.2) := by
    unfold polynomial bernstein3
    fun_prop
  have hp : 0 ≤ p := by norm_num [p, increment]
  have hr : Continuous (fun tu : ℝ × ℝ => (polynomial tu.1 tu.2)^p) :=
    hpol.rpow_const (fun _ => Or.inr hp)
  have hd : Continuous (fun x : ℝ => betaDensity (6/5:ℝ) x) := by
    unfold betaDensity
    exact continuous_const.mul (Real.continuous_rpow_const (by norm_num))
  exact ((hd.comp continuous_fst).mul (hd.comp continuous_snd)).mul hr

theorem integral_Icc_eq_sum_eighths {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ t in Icc (0:ℝ) 1, f t) =
      ∑ i : Fin 8, ∫ t in Icc ((i:ℝ)/8) (((i:ℕ)+1:ℝ)/8), f t := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n:ℝ)/8) (n := 8) (μ := (volume : Measure ℝ))
    (f := f) (fun k _ => hf.intervalIntegrable ((k:ℝ)/8) (((k+1:ℕ):ℝ)/8))
  have hle (k : ℕ) : (k:ℝ)/8 ≤ ((k+1:ℕ):ℝ)/8 := by push_cast; linarith
  simp_rw [intervalIntegral.integral_of_le (hle _), ← integral_Icc_eq_integral_Ioc] at h
  rw [intervalIntegral.integral_of_le (by norm_num)] at h
  norm_num only [Nat.cast_zero, zero_div, Nat.cast_ofNat, div_self (by norm_num : (8:ℝ) ≠ 0),
    ← integral_Icc_eq_integral_Ioc] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h.symm

theorem pairMassBetaIntegral_eq_sum_cells :
    pairMassBetaIntegral = ∑ i : Fin 8, ∑ j : Fin 8,
      ∫ t in Icc ((i:ℝ)/8) (((i:ℕ)+1:ℝ)/8),
        ∫ u in Icc ((j:ℝ)/8) (((j:ℕ)+1:ℝ)/8), pairMassBetaIntegrand t u := by
  have hcont := continuous_pairMassBetaIntegrand
  have houter : Continuous (fun t => ∫ u in Icc (0:ℝ) 1, pairMassBetaIntegrand t u) :=
    continuous_parametric_integral_of_continuous hcont isCompact_Icc
  have hinner (t : ℝ) : Continuous (pairMassBetaIntegrand t) := by
    exact hcont.comp (continuous_const.prodMk continuous_id)
  rw [pairMassBetaIntegral_eq_explicit]
  simp_rw [show (1/5:ℝ) = (6/5)-1 by norm_num]
  change (∫ t in Icc (0:ℝ) 1, ∫ u in Icc (0:ℝ) 1,
    pairMassBetaIntegrand t u) = _
  rw [integral_Icc_eq_sum_eighths houter]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [integral_Icc_eq_sum_eighths (hinner _)]
  apply integral_finset_sum
  intro j _
  exact (continuous_parametric_integral_of_continuous hcont isCompact_Icc).continuousOn.integrableOn_compact isCompact_Icc

theorem pairMassContractionUpper3_nonneg (i j : Fin 8) :
    0 ≤ pairMassContractionUpper3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [pairMassContractionUpper3]

theorem pairMassBetaIntegral_le_of_degree3_contraction_bounds
    (hc : ∀ i j, pairMassCellContraction3 i j ≤ pairMassContractionUpper3 i j) :
    pairMassBetaIntegral ≤ (389689:ℝ)/10000 := by
  rw [pairMassBetaIntegral_eq_sum_cells]
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
    pairMass_outward_sum3.le
  exact (pairMass_cell_integral_le3 i j).trans
    (mul_le_mul (hc i j) (pairMassCellCenter_power_le i j)
      (Real.rpow_nonneg (pairMassCellCenter_pos i j).le p)
      (pairMassContractionUpper3_nonneg i j))

end UnitDistance.Witness
