module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section
set_option backward.privateInPublic true


/-! Smooth half-line branches of the actual Tsfasman–Vlăduţ kernel.
The derivative estimates give both bounded variation and Fourier decay. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace UnitDistance.NumberFieldAnalysis

def tvHalfProfile (b x : ℝ) : ℝ := Real.exp (-b*x)/Real.cosh (x/2)
def tvHalfSlope (x : ℝ) : ℝ := Real.sinh (x/2)/Real.cosh (x/2)
def tvHalfDeriv (b x : ℝ) : ℝ := (-b-tvHalfSlope x/2)*tvHalfProfile b x
def tvHalfSecond (b x : ℝ) : ℝ :=
  ((b+tvHalfSlope x/2)^2-(1-tvHalfSlope x^2)/4)*tvHalfProfile b x

@[simp] theorem tvHalfProfile_zero (b : ℝ) : tvHalfProfile b 0 = 1 := by
  simp [tvHalfProfile]
@[simp] theorem tvHalfSlope_zero : tvHalfSlope 0 = 0 := by simp [tvHalfSlope]
@[simp] theorem tvHalfDeriv_zero (b : ℝ) : tvHalfDeriv b 0 = -b := by
  simp [tvHalfDeriv]

theorem tvHalfProfile_pos (b x : ℝ) : 0 < tvHalfProfile b x :=
  div_pos (Real.exp_pos _) (Real.cosh_pos _)

theorem abs_tvHalfSlope_le_one (x : ℝ) : |tvHalfSlope x| ≤ 1 := by
  have h := Real.cosh_sq_sub_sinh_sq (x/2)
  have hc := Real.cosh_pos (x/2)
  have ha : |Real.sinh (x/2)| ≤ Real.cosh (x/2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (Real.cosh (x/2)+Real.sinh (x/2)),
      sq_nonneg (Real.cosh (x/2)-Real.sinh (x/2))]
  rw [tvHalfSlope, abs_div, abs_of_pos hc]
  exact (div_le_one hc).mpr ha

theorem hasDerivAt_tvHalfProfile (b x : ℝ) :
    HasDerivAt (tvHalfProfile b) (tvHalfDeriv b x) x := by
  have h := (((hasDerivAt_id x).const_mul (-b)).exp).div
    (((hasDerivAt_id x).div_const 2).cosh) (Real.cosh_pos (x/2)).ne'
  convert! h using 1
  dsimp [tvHalfDeriv, tvHalfSlope, tvHalfProfile]
  field_simp

theorem hasDerivAt_tvHalfSlope (x : ℝ) :
    HasDerivAt tvHalfSlope ((1-tvHalfSlope x^2)/2) x := by
  have h := (((hasDerivAt_id x).div_const 2).sinh).div
    (((hasDerivAt_id x).div_const 2).cosh) (Real.cosh_pos (x/2)).ne'
  convert! h using 1
  dsimp [tvHalfSlope]
  have hc := (Real.cosh_pos (x/2)).ne'
  field_simp

theorem hasDerivAt_tvHalfDeriv (b x : ℝ) :
    HasDerivAt (tvHalfDeriv b) (tvHalfSecond b x) x := by
  have h := ((hasDerivAt_const x (-b)).sub ((hasDerivAt_tvHalfSlope x).div_const 2)).mul
    (hasDerivAt_tvHalfProfile b x)
  convert! h using 1
  dsimp [tvHalfSecond, tvHalfDeriv]
  ring

theorem continuous_tvHalfProfile (b : ℝ) : Continuous (tvHalfProfile b) :=
  Differentiable.continuous (fun x => (hasDerivAt_tvHalfProfile b x).differentiableAt)

theorem continuous_tvHalfDeriv (b : ℝ) : Continuous (tvHalfDeriv b) :=
  Differentiable.continuous (fun x => (hasDerivAt_tvHalfDeriv b x).differentiableAt)

theorem continuous_tvHalfSecond (b : ℝ) : Continuous (tvHalfSecond b) := by
  have hs : Continuous tvHalfSlope := Differentiable.continuous (fun x => (hasDerivAt_tvHalfSlope x).differentiableAt)
  exact (((continuous_const.add (hs.div_const 2)).pow 2).sub
    ((continuous_const.sub (hs.pow 2)).div_const 4)).mul (continuous_tvHalfProfile b)

theorem tvHalfProfile_bound (b : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    tvHalfProfile b x ≤ 2*Real.exp (-(b+1/2)*x) := by
  rw [tvHalfProfile]
  apply (div_le_iff₀ (Real.cosh_pos _)).mpr
  have hc : Real.exp (x/2) ≤ 2*Real.cosh (x/2) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(x/2))]
  calc
    Real.exp (-b*x) = Real.exp (-(b+1/2)*x)*Real.exp (x/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(b+1/2)*x)*(2*Real.cosh (x/2)) :=
      mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
    _ = _ := by ring

theorem abs_tvHalfDeriv_le (b x : ℝ) :
    |tvHalfDeriv b x| ≤ (|b|+1/2)*tvHalfProfile b x := by
  rw [tvHalfDeriv, abs_mul, abs_of_pos (tvHalfProfile_pos b x)]
  apply mul_le_mul_of_nonneg_right _ (tvHalfProfile_pos b x).le
  calc
    |-b-tvHalfSlope x/2| ≤ |-b|+|tvHalfSlope x/2| := abs_sub _ _
    _ ≤ |b|+1/2 := by
      rw [abs_neg, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith [abs_tvHalfSlope_le_one x]

theorem abs_tvHalfSecond_le (b x : ℝ) :
    |tvHalfSecond b x| ≤ ((|b|+1/2)^2+1/4)*tvHalfProfile b x := by
  rw [tvHalfSecond, abs_mul, abs_of_pos (tvHalfProfile_pos b x)]
  apply mul_le_mul_of_nonneg_right _ (tvHalfProfile_pos b x).le
  have hs : tvHalfSlope x^2 ≤ 1 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (abs_tvHalfSlope_le_one x)
    nlinarith
  have hb : |b+tvHalfSlope x/2| ≤ |b|+1/2 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [abs_tvHalfSlope_le_one x]
  calc
    _ ≤ |(b+tvHalfSlope x/2)^2|+|(1-tvHalfSlope x^2)/4| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity : 0 ≤ (1-tvHalfSlope x^2)/4)]
      nlinarith [sq_abs (b+tvHalfSlope x/2), abs_nonneg (b+tvHalfSlope x/2), abs_nonneg b,
        sq_nonneg (tvHalfSlope x)]

theorem abs_tvHalfDeriv_bound (b : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    |tvHalfDeriv b x| ≤ (|b|+1/2)*(2*Real.exp (-(b+1/2)*x)) :=
  (abs_tvHalfDeriv_le b x).trans
    (mul_le_mul_of_nonneg_left (tvHalfProfile_bound b hx) (by positivity))

theorem abs_tvHalfSecond_bound (b : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    |tvHalfSecond b x| ≤ ((|b|+1/2)^2+1/4)*(2*Real.exp (-(b+1/2)*x)) :=
  (abs_tvHalfSecond_le b x).trans
    (mul_le_mul_of_nonneg_left (tvHalfProfile_bound b hx) (by positivity))

end UnitDistance.NumberFieldAnalysis
