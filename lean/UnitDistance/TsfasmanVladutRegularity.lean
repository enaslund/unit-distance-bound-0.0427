module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic
public import UnitDistance.TsfasmanVladutHalfProfile
public import UnitDistance.TsfasmanVladutKernel

@[expose] public section
set_option backward.privateInPublic true


/-!
# Regularity tools for the unconditional test function

A bounded Lipschitz function has a bounded divided difference at the origin
and a square-integrable divided difference on the whole real line. The
majorant below is an explicit multiple of `1/(1+x²)`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace UnitDistance.NumberFieldAnalysis

theorem lipschitzWith_of_halfLines {f : ℝ → ℂ} {C : ℝ≥0}
    (hn : LipschitzOnWith C f (Iic 0)) (hp : LipschitzOnWith C f (Ici 0)) :
    LipschitzWith C f := by
  have hcross : ∀ x y : ℝ, x ≤ 0 → 0 ≤ y → dist (f x) (f y) ≤ C*dist x y := by
    intro x y hx hy
    calc dist (f x) (f y) ≤ dist (f x) (f 0) + dist (f 0) (f y) := dist_triangle _ _ _
      _ ≤ C*dist x 0 + C*dist 0 y :=
        add_le_add (hn.dist_le_mul x hx 0 (by simp)) (hp.dist_le_mul 0 (by simp) y hy)
      _ = C*dist x y := by
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, zero_sub, abs_neg,
          abs_of_nonpos hx, abs_of_nonneg hy, abs_of_nonpos (by linarith : x-y≤0)]
        ring
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · exact hn.dist_le_mul x hx y hy
  · exact hcross x y hx hy
  · simpa only [dist_comm] using hcross y x hy hx
  · exact hp.dist_le_mul x hx y hy

/-- The divided difference with the value at the origin subtracted. -/
def originDiffQuot (f : ℝ → ℂ) (x : ℝ) : ℂ := (f 0-f x)/(x:ℂ)

theorem norm_originDiffQuot_le {f : ℝ → ℂ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (x : ℝ) : ‖originDiffQuot f x‖ ≤ C := by
  by_cases hx : x=0
  · simp [originDiffQuot, hx]
  have h := hf.dist_le_mul 0 x
  rw [dist_eq_norm, Real.dist_eq, zero_sub, abs_neg] at h
  unfold originDiffQuot
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (abs_pos.mpr hx)]
  exact h

theorem measurable_originDiffQuot {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (originDiffQuot f) := by
  unfold originDiffQuot
  exact (measurable_const.sub hf).div Complex.continuous_ofReal.measurable

theorem norm_originDiffQuot_mul_abs_le {f : ℝ → ℂ} {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (x : ℝ) :
    ‖originDiffQuot f x‖*|x| ≤ 2*M := by
  by_cases hx : x=0
  · simp only [hx, abs_zero, mul_zero]
    have := (norm_nonneg (f 0)).trans (hM 0)
    positivity
  unfold originDiffQuot
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_mul_cancel₀ _ (abs_ne_zero.mpr hx)]
  calc ‖f 0-f x‖ ≤ ‖f 0‖+‖f x‖ := norm_sub_le _ _
    _ ≤ M+M := add_le_add (hM 0) (hM x)
    _ = 2*M := by ring

theorem norm_originDiffQuot_sq_le {f : ℝ → ℂ} {C : ℝ≥0} {M : ℝ}
    (hf : LipschitzWith C f) (hM : ∀ x, ‖f x‖ ≤ M) (x : ℝ) :
    ‖originDiffQuot f x‖^2 ≤ ((C:ℝ)^2+4*M^2)/(1+x^2) := by
  have h₁ := pow_le_pow_left₀ (norm_nonneg (originDiffQuot f x))
    (norm_originDiffQuot_le hf x) 2
  have h₂ := pow_le_pow_left₀
    (mul_nonneg (norm_nonneg (originDiffQuot f x)) (abs_nonneg x))
    (norm_originDiffQuot_mul_abs_le hM x) 2
  rw [mul_pow, sq_abs] at h₂
  rw [le_div_iff₀ (by positivity : (0:ℝ)<1+x^2)]
  nlinarith

/-- The full-line `L²` requirement in the Weil formula follows from actual
boundedness and Lipschitz regularity, with no transform hypothesis. -/
theorem memLp_two_originDiffQuot {f : ℝ → ℂ} {C : ℝ≥0} {M : ℝ}
    (hf : LipschitzWith C f) (hM : ∀ x, ‖f x‖ ≤ M) :
    MemLp (originDiffQuot f) 2 (volume : Measure ℝ) := by
  have hm := measurable_originDiffQuot hf.continuous.measurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  refine (integrable_inv_one_add_sq.const_mul ((C:ℝ)^2+4*M^2)).mono' ?_ ?_
  · exact (hm.norm.pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [div_eq_mul_inv] using norm_originDiffQuot_sq_le hf hM x

theorem integrableOn_originDiffQuot_window {f : ℝ → ℂ} {C : ℝ≥0} {M : ℝ}
    (hf : LipschitzWith C f) (hM : ∀ x, ‖f x‖ ≤ M) :
    IntegrableOn (originDiffQuot f) (Ioc (-1) 1) := by
  have h := (memLp_two_originDiffQuot hf hM).restrict (Ioc (-1) 1)
  exact h.integrable (by norm_num : (1:ℝ≥0∞)≤2)


/-- Exponential weights occurring on the two sides of the Weil contour. -/
def tvWeighted (e c x : ℝ) : ℂ := tvKernel e x * (Real.exp (c*x) : ℂ)

theorem tvWeighted_of_nonneg (e c : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    tvWeighted e c x = (tvHalfProfile (e-c) x : ℂ) := by
  unfold tvWeighted tvKernel tvHalfProfile
  rw [abs_of_nonneg hx, ← Complex.ofReal_mul]
  congr 1
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

theorem tvWeighted_of_nonpos (e c : ℝ) {x : ℝ} (hx : x ≤ 0) :
    tvWeighted e c x = (tvHalfProfile (e+c) (-x) : ℂ) := by
  unfold tvWeighted tvKernel tvHalfProfile
  rw [abs_of_nonpos hx, ← Complex.ofReal_mul]
  congr 1
  rw [div_mul_eq_mul_div, ← Real.exp_add, neg_div, Real.cosh_neg]
  congr 2
  ring

def tvLipschitzConstant (e c : ℝ) : ℝ≥0 := ⟨2*(|e|+|c|+1/2), by positivity⟩

theorem lipschitzOnWith_tvHalfProfile {b : ℝ} (hb : 0 ≤ b+1/2)
    {C : ℝ≥0} (hC : 2*(|b|+1/2) ≤ C) :
    LipschitzOnWith C (tvHalfProfile b) (Ici 0) := by
  apply (convex_Ici (0:ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_tvHalfProfile b x).hasDerivWithinAt)
  intro x hx
  change 0 ≤ x at hx
  change ‖tvHalfDeriv b x‖ ≤ (C:ℝ)
  rw [Real.norm_eq_abs]
  have he : Real.exp (-(b+1/2)*x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc
    |tvHalfDeriv b x| ≤ (|b|+1/2)*(2*Real.exp (-(b+1/2)*x)) := abs_tvHalfDeriv_bound b hx
    _ ≤ 2*(|b|+1/2) := by nlinarith [abs_nonneg b]
    _ ≤ C := hC

theorem lipschitzWith_tvWeighted {e c : ℝ} (hc : |c| ≤ e+1/2) :
    LipschitzWith (tvLipschitzConstant e c) (tvWeighted e c) := by
  have hminus : LipschitzOnWith (tvLipschitzConstant e c)
      (tvHalfProfile (e-c)) (Ici 0) := by
    apply lipschitzOnWith_tvHalfProfile
    · linarith [le_abs_self c]
    · change 2*(|e-c|+1/2) ≤ 2*(|e|+|c|+1/2)
      linarith [abs_sub e c]
  have hplus : LipschitzOnWith (tvLipschitzConstant e c)
      (tvHalfProfile (e+c)) (Ici 0) := by
    apply lipschitzOnWith_tvHalfProfile
    · linarith [neg_abs_le c]
    · change 2*(|e+c|+1/2) ≤ 2*(|e|+|c|+1/2)
      linarith [abs_add_le e c]
  apply lipschitzWith_of_halfLines
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change x ≤ 0 at hx
    change y ≤ 0 at hy
    rw [tvWeighted_of_nonpos e c hx, tvWeighted_of_nonpos e c hy,
      Complex.isometry_ofReal.dist_eq]
    simpa only [dist_neg_neg] using hplus.dist_le_mul (-x) (by exact neg_nonneg.mpr hx)
      (-y) (by exact neg_nonneg.mpr hy)
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [tvWeighted_of_nonneg e c hx, tvWeighted_of_nonneg e c hy,
      Complex.isometry_ofReal.dist_eq]
    exact hminus.dist_le_mul x hx y hy

theorem norm_tvWeighted_le_two {e c : ℝ} (hc : |c| ≤ e+1/2) (x : ℝ) :
    ‖tvWeighted e c x‖ ≤ 2 := by
  have hh : ∀ b y : ℝ, 0 ≤ b+1/2 → 0 ≤ y → |tvHalfProfile b y| ≤ 2 := by
    intro b y hb hy
    rw [abs_of_pos (tvHalfProfile_pos b y)]
    calc tvHalfProfile b y ≤ 2*Real.exp (-(b+1/2)*y) := tvHalfProfile_bound b hy
      _ ≤ 2 := by
        have := Real.exp_le_one_iff.mpr (show -(b+1/2)*y ≤ 0 by nlinarith)
        linarith
  rcases le_total 0 x with hx | hx
  · rw [tvWeighted_of_nonneg e c hx, Complex.norm_real, Real.norm_eq_abs]
    exact hh (e-c) x (by linarith [le_abs_self c]) hx
  · rw [tvWeighted_of_nonpos e c hx, Complex.norm_real, Real.norm_eq_abs]
    exact hh (e+c) (-x) (by linarith [neg_abs_le c]) (neg_nonneg.mpr hx)

@[simp] theorem tvWeighted_zero (e : ℝ) : tvWeighted e 0 = tvKernel e := by
  funext x
  simp [tvWeighted]

theorem lipschitzWith_tvKernel {e : ℝ} (he : 0 ≤ e) :
    LipschitzWith (tvLipschitzConstant e 0) (tvKernel e) := by
  simpa using lipschitzWith_tvWeighted (e := e) (c := 0) (by simpa using (show 0 ≤ e+1/2 by linarith))

theorem norm_tvKernel_le_two {e : ℝ} (he : 0 ≤ e) (x : ℝ) : ‖tvKernel e x‖ ≤ 2 := by
  simpa using norm_tvWeighted_le_two (e := e) (c := 0) (by simpa using (show 0 ≤ e+1/2 by linarith)) x

theorem memLp_two_tvKernel_diffQuot {e : ℝ} (he : 0 ≤ e) :
    MemLp (originDiffQuot (tvKernel e)) 2 (volume : Measure ℝ) :=
  memLp_two_originDiffQuot (lipschitzWith_tvKernel he) (norm_tvKernel_le_two he)

theorem integrableOn_tvKernel_diffQuot_window {e : ℝ} (he : 0 ≤ e) :
    IntegrableOn (originDiffQuot (tvKernel e)) (Ioc (-1) 1) :=
  integrableOn_originDiffQuot_window (lipschitzWith_tvKernel he) (norm_tvKernel_le_two he)

end UnitDistance.NumberFieldAnalysis
