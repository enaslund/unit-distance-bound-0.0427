module

public import UnitDistance.StudentFourierRegularization
public import UnitDistance.GaussianProfiles
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section
set_option backward.privateInPublic true


/-!
# Uniform Fourier constants for the actual archimedean witness

The constants are certified from the original exact parameters. One complex
Gaussian coordinate costs a factor two; a two-coordinate Student block costs
at most four. Both estimates have exponential rate one in the sum of the
ordinary complex-coordinate norms.
-/

open MeasureTheory FourierTransform

namespace UnitDistance.Witness

/-- The certified Student tube gives a Fourier rate at least one. -/
theorem one_le_studentFourierSigma : 1 ≤ studentFourierSigma := by
  have ha := witness_basic.2.1
  have hs : Real.sqrt a ≤ (3/500 : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · norm_num [a]
  unfold studentFourierSigma
  apply (le_div_iff₀ (Real.sqrt_pos.mpr ha)).mpr
  nlinarith [Real.pi_gt_three]

/-- A small rational enlargement of the certified tube loss gives the
uniform per-pair factor four, with no numerical hypotheses. -/
theorem fourierTubeConstant_le_four : fourierTubeConstant ≤ 4 := by
  have hq0 : (0 : ℝ) ≤ (fourierTubeLoss : ℝ) := by
    exact_mod_cast fourierTubeLoss_nonneg
  have hq : (fourierTubeLoss : ℝ) ≤ 13/500 := by
    have h := (Rat.cast_le (K := ℝ)).mpr fourierTubeLoss_lt.le
    norm_num at h ⊢
    exact h
  have hp : p ≤ 2 := by norm_num [p, increment]
  have he : (-5 : ℝ) ≤ -2*s*p := by norm_num [s, p, increment]
  have hden : (1-(1/1000:ℝ)^2)^(-2*s*p) ≤ 2 := by
    calc
      _ ≤ (1-(1/1000:ℝ)^2)^(-5:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) he
      _ = ((1-(1/1000:ℝ)^2)^5)⁻¹ := by
        norm_num [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 1-(1/1000:ℝ)^2)]
      _ ≤ 2 := by norm_num
  have hpoly : (1+(fourierTubeLoss:ℝ))^p ≤ 2 := by
    calc
      _ ≤ (1+(fourierTubeLoss:ℝ))^(2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hp
      _ = (1+(fourierTubeLoss:ℝ))^2 := Real.rpow_natCast _ 2
      _ ≤ (1+(13/500:ℝ))^2 := by gcongr
      _ ≤ 2 := by norm_num
  unfold fourierTubeConstant
  exact (mul_le_mul hden hpoly (Real.rpow_nonneg (by linarith) _) (by norm_num)).trans
    (by norm_num)

/-- The actual Student power has a dimension-uniform rate-one envelope. -/
theorem pairProfile_fourier_envelope_one (ξ : WithLp 2 (ℂ × ℂ)) :
    ‖𝓕 (fun x : WithLp 2 (ℂ × ℂ) => ((pairProfile (WithLp.ofLp x)^p:ℝ):ℂ)) ξ‖ ≤
      (4*pairMass)*Real.exp (-(‖(WithLp.ofLp ξ).1‖+‖(WithLp.ofLp ξ).2‖)) := by
  refine (pairProfile_fourier_envelope ξ).trans ?_
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right fourierTubeConstant_le_four pairMass_pos.le
  · apply Real.exp_le_exp.mpr
    nlinarith [one_le_studentFourierSigma,
      norm_nonneg (WithLp.ofLp ξ).1, norm_nonneg (WithLp.ofLp ξ).2]
  · positivity
  · positivity [pairMass_pos]

/-- Exact Fourier transform of the compact-place p-th power. -/
theorem compactProfile_fourier_eq (ξ : ℂ) :
    𝓕 (fun z : ℂ => ((compactProfile z^p:ℝ):ℂ)) ξ =
      ((compactMass * Real.exp (-Real.pi^2*‖ξ‖^2/(2*increment*p)) : ℝ) : ℂ) := by
  have hpos : 0 < 2*increment*p := by positivity [increment_pos, witness_basic.2.2.1]
  have h := fourier_gaussian_innerProductSpace (V := ℂ)
    (b := ((2*increment*p:ℝ):ℂ)) hpos ξ
  convert! h using 1
  · apply congrArg (fun f : ℂ → ℂ => 𝓕 f ξ)
    funext z
    rw [compactProfile_gaussian, complexGaussian_power]
    simp only [complexGaussian, Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_pow]
  · rw [compactMass_eq]
    simp [Complex.finrank_real_complex, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow]

/-- A single ordinary complex Gaussian coordinate has factor two and rate one. -/
theorem compactProfile_fourier_envelope_one (ξ : ℂ) :
    ‖𝓕 (fun z : ℂ => ((compactProfile z^p:ℝ):ℂ)) ξ‖ ≤
      (2*compactMass)*Real.exp (-‖ξ‖) := by
  have hb : 0 < 2*increment*p := by positivity [increment_pos, witness_basic.2.2.1]
  have hb1 : 2*increment*p ≤ 1 := by norm_num [p, increment]
  have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hq : 1 ≤ Real.pi^2/(2*increment*p) := (le_div_iff₀ hb).mpr (by linarith)
  have hexp : Real.exp (1/2 : ℝ) ≤ 2 := by
    convert Real.exp_bound_div_one_sub_of_interval (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1) using 1
    norm_num
  have hbound : Real.exp (-Real.pi^2*‖ξ‖^2/(2*increment*p)) ≤
      2*Real.exp (-‖ξ‖) := by
    calc
      _ ≤ Real.exp ((1/2:ℝ)-‖ξ‖) := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right hq (sq_nonneg ‖ξ‖)
        have hform : -Real.pi^2*‖ξ‖^2/(2*increment*p) =
            -(Real.pi^2/(2*increment*p)*‖ξ‖^2) := by ring
        rw [hform]
        nlinarith [sq_nonneg (‖ξ‖-1/2)]
      _ = Real.exp (1/2:ℝ)*Real.exp (-‖ξ‖) := by rw [← Real.exp_add]; congr 1
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
  rw [compactProfile_fourier_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos compactMass_pos (Real.exp_pos _))]
  nlinarith [mul_le_mul_of_nonneg_left hbound compactMass_pos.le]

/-- The compact p-th power is a temperate multiplier, supplied by its actual
Gaussian Schwartz realization. -/
theorem temperateGrowth_compactProfile_rpow :
    (fun z : ℂ => compactProfile z^p).HasTemperateGrowth := by
  have hpos : 0 < 2*increment*p := by positivity [increment_pos, witness_basic.2.2.1]
  convert (gaussianSchwartz (V := ℂ) (2*increment*p) hpos).hasTemperateGrowth using 1
  funext z
  rw [compactProfile_gaussian, complexGaussian_power]
  rfl

end UnitDistance.Witness
