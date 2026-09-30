module

public import UnitDistance.StudentComplexPerturbation

@[expose] public section
set_option backward.privateInPublic true


/-! Exact finite complex perturbation bounds for bicubic Bernstein patches. -/

open scoped BigOperators

namespace UnitDistance.BernsteinTube

theorem patch_perturbation_le (B : ℕ → ℕ → ℂ) (E : ℕ → ℕ → ℝ)
    {ω : ℝ} (hω : 0 ≤ ω) (t u h k : ℂ) (hh : ‖h‖ ≤ ω) (hk : ‖k‖ ≤ ω)
    (hE0 : ∀ r ∈ Finset.range 4, ∀ s ∈ Finset.range 4, 0 ≤ E r s)
    (hE : ∀ r ∈ Finset.range 4, ∀ s ∈ Finset.range 4,
      ‖taylorCoefficient B r s t u‖ ≤ E r s) :
    ‖patch B (t+h) (u+k) - patch B t u‖ ≤
      ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4,
        if r+s=0 then 0 else E r s*ω^(r+s) := by
  rw [patch_sub]
  calc
    _ ≤ ∑ r ∈ Finset.range 4,
        ‖∑ s ∈ Finset.range 4, if r+s=0 then 0 else taylorCoefficient B r s t u*h^r*k^s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4,
        ‖if r+s=0 then (0:ℂ) else taylorCoefficient B r s t u*h^r*k^s‖ := by
      apply Finset.sum_le_sum
      intro r hr
      exact norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      split_ifs with hrs
      · simp
      · rw [norm_mul, norm_mul, norm_pow, norm_pow]
        calc
          _ ≤ E r s*ω^r*ω^s := by
            gcongr
            · exact mul_nonneg (hE0 r hr s hs) (pow_nonneg hω r)
            · exact hE0 r hr s hs
            · exact hE r hr s hs
          _ = _ := by rw [pow_add]; ring

/-- The perturbation bound is proved directly from the finite mixed
coefficient differences and the real Bernstein partition of unity. -/
theorem mixed_difference_perturbation_le (B : ℕ → ℕ → ℂ) (D : ℕ → ℕ → ℝ)
    {ω t u : ℝ} (hω : 0 ≤ ω) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h k : ℂ) (hh : ‖h‖ ≤ ω) (hk : ‖k‖ ≤ ω)
    (hD0 : ∀ r ∈ Finset.range 4, ∀ s ∈ Finset.range 4, 0 ≤ D r s)
    (hD : ∀ r ∈ Finset.range 4, ∀ s ∈ Finset.range 4,
      ∀ i ∈ Finset.range (4-r), ∀ j ∈ Finset.range (4-s), ‖difference B r s i j‖ ≤ D r s) :
    ‖patch B ((t:ℂ)+h) ((u:ℂ)+k) - patch B (t:ℂ) (u:ℂ)‖ ≤
      ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4,
        if r+s=0 then 0 else (Nat.choose 3 r : ℝ)*(Nat.choose 3 s : ℝ)*D r s*ω^(r+s) := by
  apply patch_perturbation_le B (fun r s => (Nat.choose 3 r : ℝ)*(Nat.choose 3 s : ℝ)*D r s)
    hω (t:ℂ) (u:ℂ) h k hh hk
  · intro r hr s hs
    exact mul_nonneg (by positivity) (hD0 r hr s hs)
  · intro r hr s hs
    exact taylorCoefficient_norm_le B (by simp only [Finset.mem_range] at hr; omega)
      (by simp only [Finset.mem_range] at hs; omega)
      ht0 ht1 hu0 hu1 (hD r hr s hs)

end UnitDistance.BernsteinTube
