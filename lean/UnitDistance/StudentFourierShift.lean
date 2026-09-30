module

public import UnitDistance.StudentFourierSlices

@[expose] public section
set_option backward.privateInPublic true


/-! Four successive justified coordinate shifts of the actual Fourier integral. -/

open MeasureTheory

namespace UnitDistance.Witness

theorem studentFourIntegral_shift (y ξ : Fin 4 → ℝ) (hy : studentFourTube y) :
    (∫ x, studentFourIntegrand 0 ξ x) =
      (Real.exp ((2*Real.pi/Real.sqrt a)*(∑ i, ξ i*y i)):ℂ)*
        (∫ x, studentFourIntegrand y ξ x) := by
  let y₁ := Function.update y 0 0
  let y₂ := Function.update y₁ 1 0
  let y₃ := Function.update y₂ 2 0
  let y₄ := Function.update y₃ 3 0
  have hy₁ : studentFourTube y₁ := studentFourTube_update_zero hy 0
  have hy₂ : studentFourTube y₂ := studentFourTube_update_zero hy₁ 1
  have hy₃ : studentFourTube y₃ := studentFourTube_update_zero hy₂ 2
  have hzero : y₄ = 0 := by
    funext i
    fin_cases i <;> simp [y₄, y₃, y₂, y₁, Function.update]
  have h₀ := studentFourIntegral_coordinate_shift y ξ 0 hy
  have h₁ := studentFourIntegral_coordinate_shift y₁ ξ 1 hy₁
  have h₂ := studentFourIntegral_coordinate_shift y₂ ξ 2 hy₂
  have h₃ := studentFourIntegral_coordinate_shift y₃ ξ 3 hy₃
  have he₁ : y₁ 1 = y 1 := by simp [y₁]
  have he₂ : y₂ 2 = y 2 := by simp [y₂, y₁]
  have he₃ : y₃ 3 = y 3 := by simp [y₃, y₂, y₁]
  rw [he₁] at h₁
  rw [he₂] at h₂
  rw [he₃, show Function.update y₃ 3 0 = 0 from hzero] at h₃
  let E (i : Fin 4) : ℂ := (Real.exp (2*Real.pi*(ξ i/Real.sqrt a)*y i):ℂ)
  have hE : E 3*E 2*E 1*E 0 =
      (Real.exp ((2*Real.pi/Real.sqrt a)*(∑ i, ξ i*y i)):ℂ) := by
    simp only [E, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    simp only [Fin.sum_univ_succ, Fin.isValue, Fin.reduceSucc, Fin.sum_univ_zero, add_zero]
    ring
  calc
    _ = (E 3*E 2*E 1*E 0)*(∫ x, studentFourIntegrand y ξ x) := by
      rw [h₃, h₂, h₁, h₀]
      dsimp only [E]
      ring
    _ = _ := by rw [hE]

end UnitDistance.Witness
