module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! The manuscript's sufficient Fourier/packing inequality, with exact constants. -/
namespace UnitDistance.Packing

/-- The shell ratio dictated by dimension 2d and separation d*mu. -/
noncomputable def coefficientRatio (d : ℕ) (μ σ : ℝ) : ℝ :=
  (5:ℝ)^(2*d) * Real.exp (-σ*((d:ℝ)*μ))

theorem coefficientRatio_pos (d : ℕ) (μ σ : ℝ) : 0 < coefficientRatio d μ σ := by
  unfold coefficientRatio
  positivity

/-- The published inequality forces a strict nonzero-tail bound even after
the product Fourier-envelope prefactor M^d is included. -/
theorem coefficientRatio_bounds (d : ℕ) (hd : 1 ≤ d) (M μ σ : ℝ) (hM : 1 ≤ M)
    (hgap : Real.log M + 2*Real.log 5 + 2 ≤ σ*μ) :
    coefficientRatio d μ σ < 1 ∧
      M^d * coefficientRatio d μ σ/(1-coefficientRatio d μ σ) < 1 := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hMpow : (1:ℝ) ≤ M^d := one_le_pow₀ hM
  have hqpos := coefficientRatio_pos d μ σ
  have hid : M^d * coefficientRatio d μ σ =
      Real.exp ((d:ℝ)*(Real.log M+2*Real.log 5-σ*μ)) := by
    unfold coefficientRatio
    rw [show M^d = Real.exp ((d:ℝ)*Real.log M) by
      rw [Real.exp_nat_mul, Real.exp_log hMp],
      show (5:ℝ)^(2*d) = Real.exp (((2*d:ℕ):ℝ)*Real.log 5) by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<5)]]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hbound : M^d * coefficientRatio d μ σ ≤ Real.exp (-2*(d:ℝ)) := by
    rw [hid]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hqbound : coefficientRatio d μ σ ≤ Real.exp (-2*(d:ℝ)) := by
    calc
      _ ≤ M^d*coefficientRatio d μ σ := by nlinarith
      _ ≤ _ := hbound
  have hexp : 2*Real.exp (-2*(d:ℝ)) < 1 := by
    have hlin := Real.add_one_lt_exp (by linarith : (2*(d:ℝ)) ≠ 0)
    have htwo : (2:ℝ) < Real.exp (2*(d:ℝ)) := by linarith
    rw [show -2*(d:ℝ) = -(2*(d:ℝ)) by ring, Real.exp_neg]
    exact (mul_inv_lt_iff₀ (Real.exp_pos _)).mpr (by simpa using htwo)
  have hq : coefficientRatio d μ σ < 1 := by nlinarith [Real.exp_pos (-2*(d:ℝ))]
  refine ⟨hq, ?_⟩
  apply (div_lt_iff₀ (sub_pos.mpr hq)).mpr
  nlinarith

end UnitDistance.Packing
