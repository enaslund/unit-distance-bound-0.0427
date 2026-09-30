module

public import UnitDistance.TsfasmanVladutDecay
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section
set_option backward.privateInPublic true


/-! The half-scaled actual kernel has the same quadratic Fourier decay. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Complex
open scoped Topology
namespace UnitDistance.NumberFieldAnalysis

theorem tv_half_scaled_fourier (F : ℝ → ℂ) (t : ℝ) :
    (∫ x : ℝ, F (x/2)/2*Complex.exp (((t*x:ℝ):ℂ)*I)) =
      ∫ x : ℝ, F x*Complex.exp ((((2*t)*x:ℝ):ℂ)*I) := by
  have he : ∀ x : ℝ, F (x/2)/2*Complex.exp (((t*x:ℝ):ℂ)*I) =
      (F (x/2)*Complex.exp ((((2*t)*(x/2):ℝ):ℂ)*I))/2 := by
    intro x
    rw [show (2*t)*(x/2) = t*x by ring]
    ring
  simp_rw [he]
  rw [integral_div]
  have h := Measure.integral_comp_div (fun x : ℝ => F x*Complex.exp ((((2*t)*x:ℝ):ℂ)*I)) 2
  rw [h]
  norm_num [Complex.real_smul]

theorem tvKernel_half_quadratic_fourier_decay {e : ℝ} (he : 0 < e) :
    ∃ C γ₀ : ℝ, 1 ≤ γ₀ ∧ ∀ t : ℝ, γ₀ ≤ |t| →
      ‖∫ x : ℝ, (tvKernel e (x/2)/2)*Complex.exp (((t*x:ℝ):ℂ)*I)‖ ≤ C/t^2 := by
  obtain ⟨C, γ₀, hγ, hφ⟩ := tvKernel_quadratic_fourier_decay he
  refine ⟨C/4, γ₀, hγ, ?_⟩
  intro t ht
  rw [tv_half_scaled_fourier]
  have ht' : γ₀ ≤ |2*t| := by rw [abs_mul]; norm_num; linarith
  have h := hφ (2*t) ht'
  convert h using 1
  ring

end UnitDistance.NumberFieldAnalysis
