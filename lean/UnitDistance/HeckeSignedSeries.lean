module

public import UnitDistance.HeckeSignedArithmetic

@[expose] public section
set_option backward.privateInPublic true


/-! The ordinary mod-four character series over actual nonzero integral ideals,
with absolute convergence proved on the right half-plane. -/
noncomputable section
open NumberField DedekindResidue
open scoped Real Classical nonZeroDivisors NNReal ENNReal
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- The literal ideal-norm character Dirichlet series. -/
def chiFourIdealSeries (s : ℂ) : ℂ :=
  ∑' I : (Ideal (𝓞 K))⁰, chiFourComplex (Ideal.absNorm (I : Ideal (𝓞 K))) *
    (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)^(-s)

theorem summable_chiFourIdealSeries {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : (Ideal (𝓞 K))⁰ => chiFourComplex (Ideal.absNorm (I : Ideal (𝓞 K))) *
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)^(-s)) := by
  apply Summable.of_norm_bounded (summable_ideal_norm_rpow K hs)
  intro I
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos
    (Ideal.absNorm_pos_of_nonZeroDivisors I), Complex.neg_re]
  exact (mul_le_mul_of_nonneg_right (norm_chiFourComplex_le_one _) (by positivity)).trans_eq (one_mul _)

theorem summable_real_chiFourIdealSeries (delta : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun I : (Ideal (𝓞 K))⁰ =>
      delta*chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K))) *
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^(-s)) := by
  apply Summable.of_norm_bounded ((summable_ideal_norm_rpow K hs).mul_left |delta|)
  intro I
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  calc
    _ ≤ (|delta| * 1) * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^(-s) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (abs_chiFourReal_le_one _) (abs_nonneg _)) (by positivity)
    _ = _ := by rw [mul_one]

theorem chiFourIdealSeries_real {s : ℝ} (hs : 1 < s) :
    chiFourIdealSeries K (s : ℂ) =
      ((∑' I : (Ideal (𝓞 K))⁰, chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K))) *
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^(-s) : ℝ) : ℂ) := by
  unfold chiFourIdealSeries
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro I
  rw [Complex.ofReal_mul, chiFourComplex_eq_ofReal, Complex.ofReal_cpow (by positivity)]
  simp only [Complex.ofReal_natCast, Complex.ofReal_neg]

theorem tsum_positive_chiFourIdealWeight_ne_top (delta : ℝ) {σ : ℝ} (hσ : 1 < 2*σ) :
    (∑' I : (Ideal (𝓞 K))⁰,
      ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K)))) *
        ENNReal.ofReal (((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^2)^(-σ))) ≠ ⊤ := by
  have hreal : Summable (fun I : (Ideal (𝓞 K))⁰ =>
      delta*chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K))) *
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^2)^(-σ)) := by
    convert summable_real_chiFourIdealSeries K delta hσ using 1
    ext I
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 2
    norm_num
  convert hreal.tsum_ofReal_ne_top using 1
  congr 1
  ext I
  exact (ENNReal.ofReal_mul' (Real.rpow_nonneg (sq_nonneg _) _)).symm

end UnitDistance.NumberFieldAnalysis
