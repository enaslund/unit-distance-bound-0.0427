module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section
set_option backward.privateInPublic true


/-! Half-line integration by parts with an oscillatory complex exponential. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Complex
open scoped Topology
namespace UnitDistance.NumberFieldAnalysis

def tvOscillation (t x : ℝ) : ℂ := Complex.exp ((t:ℂ)*Complex.I*(x:ℂ))
def tvHalfFourier (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0, f x*tvOscillation t x

@[simp] theorem norm_tvOscillation (t x : ℝ) : ‖tvOscillation t x‖ = 1 := by
  simp [tvOscillation, Complex.norm_exp]
@[simp] theorem tvOscillation_zero (t : ℝ) : tvOscillation t 0 = 1 := by
  simp [tvOscillation]

theorem hasDerivAt_tvOscillation (t x : ℝ) :
    HasDerivAt (tvOscillation t) ((t:ℂ)*Complex.I*tvOscillation t x) x := by
  convert! ((hasDerivAt_id x).ofReal_comp.const_mul ((t:ℂ)*Complex.I)).cexp using 1
  simp only [tvOscillation, id_eq, Complex.ofReal_one, mul_one]
  ring

theorem continuous_tvOscillation (t : ℝ) : Continuous (tvOscillation t) :=
  Differentiable.continuous (fun x => (hasDerivAt_tvOscillation t x).differentiableAt)

theorem tv_integrable_mul_oscillation {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ioi 0)) (t : ℝ) :
    IntegrableOn (fun x => f x*tvOscillation t x) (Ioi 0) := by
  apply hf.norm.mono'
    (hf.aestronglyMeasurable.mul (continuous_tvOscillation t).aestronglyMeasurable)
  exact Eventually.of_forall (fun x => by simp)

theorem tv_tendsto_mul_oscillation {f : ℝ → ℂ}
    (hf : Tendsto f atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun x => f x*tvOscillation t x) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun x => show ‖f x*tvOscillation t x‖ ≤ ‖f x‖ by simp)
  simpa using hf.norm

theorem tvHalfFourier_ibp {f f' : ℝ → ℂ}
    (hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt f (f' x) x)
    (hf : IntegrableOn f (Ioi 0)) (hf' : IntegrableOn f' (Ioi 0))
    (htend : Tendsto f atTop (𝓝 0)) (t : ℝ) :
    ((t:ℂ)*Complex.I)*tvHalfFourier f t = -f 0-tvHalfFourier f' t := by
  let g : ℝ → ℂ := fun x => f x*tvOscillation t x
  let g' : ℝ → ℂ := fun x =>
    f' x*tvOscillation t x+((t:ℂ)*Complex.I)*(f x*tvOscillation t x)
  have hg : ∀ x ∈ Ici (0:ℝ), HasDerivAt g (g' x) x := by
    intro x hx
    convert! (hderiv x hx).mul (hasDerivAt_tvOscillation t x) using 1
    dsimp [g']
    ring
  have hi : IntegrableOn g' (Ioi 0) :=
    (tv_integrable_mul_oscillation hf' t).add ((tv_integrable_mul_oscillation hf t).const_mul _)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hg hi (tv_tendsto_mul_oscillation htend t)
  dsimp [g'] at h
  rw [integral_add (tv_integrable_mul_oscillation hf' t)
    ((tv_integrable_mul_oscillation hf t).const_mul _), integral_const_mul] at h
  simp only [g, tvOscillation_zero, mul_one, zero_sub] at h
  dsimp [tvHalfFourier]
  linear_combination h

theorem tvHalfFourier_twice {f f' f'' : ℝ → ℂ}
    (hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt f (f' x) x)
    (hderiv' : ∀ x ∈ Ici (0:ℝ), HasDerivAt f' (f'' x) x)
    (hf : IntegrableOn f (Ioi 0)) (hf' : IntegrableOn f' (Ioi 0))
    (hf'' : IntegrableOn f'' (Ioi 0))
    (htend : Tendsto f atTop (𝓝 0)) (htend' : Tendsto f' atTop (𝓝 0)) (t : ℝ) :
    ((t:ℂ)*Complex.I)^2*tvHalfFourier f t =
      -((t:ℂ)*Complex.I)*f 0+f' 0+tvHalfFourier f'' t := by
  have h₁ := tvHalfFourier_ibp hderiv hf hf' htend t
  have h₂ := tvHalfFourier_ibp hderiv' hf' hf'' htend' t
  linear_combination ((t:ℂ)*Complex.I)*h₁-h₂

theorem norm_tvHalfFourier_le (f : ℝ → ℂ) (t : ℝ) :
    ‖tvHalfFourier f t‖ ≤ ∫ x : ℝ in Ioi 0, ‖f x‖ := by
  simpa only [tvHalfFourier, norm_mul, norm_tvOscillation, mul_one] using
    norm_integral_le_integral_norm (fun x => f x*tvOscillation t x)

end UnitDistance.NumberFieldAnalysis
