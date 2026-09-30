module

public import UnitDistance.HeckeSignedMellinTotal
public import UnitDistance.HeckeSignedNormalization

@[expose] public section
set_option backward.privateInPublic true


/-! Recombination of the positive and negative character masses, with the
exact archimedean and discriminant normalization. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Real Classical nonZeroDivisors NNReal ENNReal
namespace UnitDistance.NumberFieldAnalysis

/-- Reconstruct an absolutely summable real family from its two nonnegative masses. -/
theorem tsum_ofReal_pos_sub_neg {ι : Type*} (f : ι → ℝ) (hf : Summable f) :
    (∑' i, ENNReal.ofReal (f i)).toReal - (∑' i, ENNReal.ofReal (-f i)).toReal = ∑' i, f i := by
  have hp : Summable (fun i => max (f i) 0) := hf.abs.of_nonneg_of_le
    (fun i => le_max_right _ _) (fun i => max_le (le_abs_self _) (abs_nonneg _))
  have hn : Summable (fun i => max (-f i) 0) := hf.neg.abs.of_nonneg_of_le
    (fun i => le_max_right _ _) (fun i => max_le (le_abs_self _) (abs_nonneg _))
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top),
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal']
  rw [← hp.tsum_sub hn]
  exact tsum_congr (fun i => max_zero_sub_max_neg_zero_eq_self (f i))

variable (K : Type*) [Field K] [NumberField K]

theorem heckeSignedGammaMass_toReal {σ : ℝ} (hσ : 0 < σ) :
    (heckeSignedGammaMass K σ).toReal = ((heckeJacobian K : ℝ≥0) : ℝ) *
      ∏ w : InfinitePlace K, Real.pi^(-((mult w:ℝ)*σ+heckeRealHalfShift K w))*
        Real.Gamma ((mult w:ℝ)*σ+heckeRealHalfShift K w) := by
  rw [heckeSignedGammaMass, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (by
      apply Finset.prod_nonneg
      intro w _
      apply mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      apply (Real.Gamma_pos_of_pos _).le
      have hm : (0:ℝ) < mult w := by exact_mod_cast mult_pos (w:=w)
      exact add_pos_of_pos_of_nonneg (mul_pos hm hσ) (heckeRealHalfShift_nonneg K w))]

theorem positive_chiFourIdealWeight_difference {σ : ℝ} (hσ : 1 < 2*σ) :
    (∑' I : (Ideal (𝓞 K))⁰,
      ENNReal.ofReal (chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K)))) *
        ENNReal.ofReal (((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^2)^(-σ))).toReal -
    (∑' I : (Ideal (𝓞 K))⁰,
      ENNReal.ofReal (-chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K)))) *
        ENNReal.ofReal (((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^2)^(-σ))).toReal =
      ∑' I : (Ideal (𝓞 K))⁰, chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K))) *
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^(-(2*σ)) := by
  have hpow (n : ℕ) : ((n:ℝ)^2)^(-σ) = (n:ℝ)^(-(2*σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  simp_rw [hpow, ← ENNReal.ofReal_mul' (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hf : Summable (fun I : (Ideal (𝓞 K))⁰ => chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K))) *
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^(-(2*σ))) := by
    simpa only [one_mul] using summable_real_chiFourIdealSeries K 1 hσ
  simpa only [neg_mul] using tsum_ofReal_pos_sub_neg _ hf

/-- Difference of the exact total component masses is the full real character series. -/
theorem heckeOddSignedTotalMass_difference (r : K) (hr : r^2=7)
    {σ : ℝ} (hσ : 1 < 2*σ) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedTotalMass K 1 t).toReal -
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedTotalMass K (-1) t).toReal =
      (heckeBeta K)^(-σ)*(heckeSignedGammaMass K σ).toReal *
        ∑' I : (Ideal (𝓞 K))⁰, chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K))) *
          (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^(-(2*σ)) := by
  have hs : 0 < σ := by linarith
  rw [lintegral_mellin_heckeOddSignedTotalMass K r hr 1 hs,
    lintegral_mellin_heckeOddSignedTotalMass K r hr (-1) hs]
  simp only [one_mul, neg_one_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (heckeBeta_pos K).le _)]
  rw [← mul_sub, positive_chiFourIdealWeight_difference K hσ]

/-- Complex normalization of the reconstructed total character mass. -/
theorem heckeOddSignedTotalMass_difference_complex (r : K) (hr : r^2=7)
    {s : ℝ} (hs : 1 < s) :
    (((∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(s/2-1))*heckeOddSignedTotalMass K 1 t).toReal -
      (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(s/2-1))*heckeOddSignedTotalMass K (-1) t).toReal : ℝ) : ℂ) =
      (heckeAdjust K : ℂ)*signedHeckePrefactor K (s : ℂ)*chiFourIdealSeries K (s : ℂ) := by
  have hσ : 1 < 2*(s/2) := by linarith
  rw [heckeOddSignedTotalMass_difference K r hr hσ, mul_div_cancel₀ s (by norm_num : (2:ℝ) ≠ 0),
    heckeSignedGammaMass_toReal K (by linarith : 0 < s/2), Complex.ofReal_mul,
    signedGamma_normalization K s, ← chiFourIdealSeries_real K hs]

end UnitDistance.NumberFieldAnalysis
