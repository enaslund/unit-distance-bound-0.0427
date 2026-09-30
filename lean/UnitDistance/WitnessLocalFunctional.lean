module

public import UnitDistance.FiniteFunctionalArithmetic
public import UnitDistance.LocalOperator
public import UnitDistance.LocalProduct

@[expose] public section
set_option backward.privateInPublic true


/-! # The published finite expression is the actual local integral functional

The six rational weights are extended by zero to natural shell indices. The
finite-index sums are identified exactly, then the existing local integration
theorems evaluate the actual profile. The measured ball system and reciprocal
steps are ordinary local geometric inputs, not a unit-distance construction.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace UnitDistance.Witness

/-- The published six coefficients, with zero weight beyond shell five. -/
def shellWeightNat (v : Fin 11) (i : ℕ) : ℝ :=
  if h : i < 6 then (shellWeights v ⟨i, h⟩ : ℝ) else 0

@[simp] theorem shellWeightNat_fin (v : Fin 11) (i : Fin 6) :
    shellWeightNat v i = (shellWeights v i : ℝ) := by
  simp [shellWeightNat, i.isLt]

theorem shellWeightNat_nonneg (v : Fin 11) (i : ℕ) : 0 ≤ shellWeightNat v i := by
  unfold shellWeightNat
  split_ifs with hi
  · exact_mod_cast (shellWeights_pos v ⟨i, hi⟩).le
  · exact le_rfl

theorem shellSquareMass_witness (v : Fin 11) :
    Local.shellSquareMass (residueCard v) (Finset.range 6) (shellWeightNat v) =
      finiteSecond v := by
  unfold Local.shellSquareMass finiteSecond
  rw [Finset.sum_range]
  simp only [shellWeightNat_fin]

theorem shellInteraction_witness (v : Fin 11) :
    Local.shellInteraction (residueCard v) (Finset.range 6) (shellWeightNat v) =
      finiteTransition v := by
  unfold Local.shellInteraction finiteTransition
  simp_rw [Finset.sum_range, shellWeightNat_fin]

theorem shellLpMass_witness (v : Fin 11) :
    Local.shellLpMass (residueCard v) p (Finset.range 6) (shellWeightNat v) = finiteLp v := by
  unfold Local.shellLpMass finiteLp
  rw [Finset.sum_range]
  simp only [shellWeightNat_fin]

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    {μ : Measure G} (v : Fin 11) (B : Local.BallSystem G μ (residueCard v))

/-- The actual two-coordinate shell profile of the published witness. -/
def localShellProfile : G × G → ℝ :=
  B.shellProfile (periodPower v) (Finset.range 6 ×ˢ Finset.range 6)
    (fun ij => shellWeightNat v ij.1 * shellWeightNat v ij.2)

theorem localShellProfile_moment [SFinite μ] :
    (∫ x, localShellProfile v B x ^ p ∂μ.prod μ) =
      residueCard v ^ periodPower v * finiteLp v ^ 2 := by
  rw [localShellProfile, B.shellProfile_moment (lt_trans zero_lt_one (residueCard_gt_one v))
    _ _ _ (ne_of_gt witness_basic.2.2.1),
    Local.product_shell_moment _ _ _ _ _ _
      (fun i _ => shellWeightNat_nonneg v i) (fun i _ => shellWeightNat_nonneg v i),
    shellLpMass_witness]
  ring

variable {U : Type*} [MeasurableSpace U] (S : B.ReciprocalSteps U)
    (ν : Measure U) [IsProbabilityMeasure ν]

theorem localShellProfile_energy [MeasurableAdd₂ G] [SFinite μ] [μ.IsAddRightInvariant]
    (hs : ∀ n, Measurable (S.step n)) :
    (∫ x, localShellProfile v B x *
      B.displacementOperator S ν (localShellProfile v B) x ∂μ.prod μ) =
      residueCard v ^ periodPower v *
        (((periodPower v : ℝ) + 1) * finiteSecond v ^ 2 +
          2 * finiteSecond v * finiteTransition v) := by
  rw [localShellProfile, B.shellProfile_operator_eq S ν
    (lt_trans zero_lt_one (residueCard_gt_one v)) hs,
    Local.symmetric_product_shell_energy, shellSquareMass_witness, shellInteraction_witness]

/-- Positivity refers to the actual integral quotient, so the subsequent
logarithm identity does not use a zero-integral convention. -/
theorem localWeightedFunctional_pos [MeasurableAdd₂ G] [SFinite μ] [μ.IsAddRightInvariant]
    (hs : ∀ n, Measurable (S.step n)) :
    0 < B.weightedFunctional S ν increment (localShellProfile v B) := by
  have hQ : 0 < residueCard v ^ periodPower v :=
    pow_pos (lt_trans zero_lt_one (residueCard_gt_one v)) _
  have hE : 0 < ((periodPower v : ℝ) + 1) * finiteSecond v ^ 2 +
      2 * finiteSecond v * finiteTransition v :=
    (energyLower_pos v).trans_le (energyLower_le v)
  unfold Local.BallSystem.weightedFunctional
  change 0 < (∫ x, localShellProfile v B x *
    B.displacementOperator S ν (localShellProfile v B) x ∂μ.prod μ) /
    (∫ x, localShellProfile v B x ^ p ∂μ.prod μ) ^ (1 + increment)
  rw [localShellProfile_energy v B S ν hs, localShellProfile_moment]
  exact div_pos (mul_pos hQ hE)
    (Real.rpow_pos_of_pos (mul_pos hQ (sq_pos_of_pos (finiteLp_pos v))) _)

/-- The witness logarithm is the logarithm of the actual weighted local
functional, with the exact period normalization and real-power exponent. -/
theorem finiteLogFunctional_eq_log_weightedFunctional
    [MeasurableAdd₂ G] [SFinite μ] [μ.IsAddRightInvariant]
    (hs : ∀ n, Measurable (S.step n)) :
    finiteLogFunctional v =
      Real.log (B.weightedFunctional S ν increment (localShellProfile v B)) := by
  have hQ : 0 < residueCard v ^ periodPower v :=
    pow_pos (lt_trans zero_lt_one (residueCard_gt_one v)) _
  have hL : 0 < finiteLp v ^ 2 := sq_pos_of_pos (finiteLp_pos v)
  have hE : 0 < ((periodPower v : ℝ) + 1) * finiteSecond v ^ 2 +
      2 * finiteSecond v * finiteTransition v :=
    (energyLower_pos v).trans_le (energyLower_le v)
  unfold Local.BallSystem.weightedFunctional
  change finiteLogFunctional v = Real.log
    ((∫ x, localShellProfile v B x *
      B.displacementOperator S ν (localShellProfile v B) x ∂μ.prod μ) /
      (∫ x, localShellProfile v B x ^ p ∂μ.prod μ) ^ (1 + increment))
  rw [localShellProfile_energy v B S ν hs, localShellProfile_moment,
    Real.log_div (mul_pos hQ hE).ne' (Real.rpow_pos_of_pos (mul_pos hQ hL) _).ne',
    Real.log_rpow (mul_pos hQ hL), Real.log_mul hQ.ne' hE.ne',
    Real.log_mul hQ.ne' hL.ne']
  simp only [Real.log_pow]
  unfold finiteLogFunctional
  ring

end UnitDistance.Witness
