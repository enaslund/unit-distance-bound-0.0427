module

public import UnitDistance.LocalEnergy
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option backward.privateInPublic true


/-! # The displacement operator and the order of integration

This module connects the evaluated shell energy to the manuscript's literal
`∫ g(z) T g(z)` definition. All Fubini and finite-support requirements are proved.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace UnitDistance.Local.BallSystem

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
variable {μ : Measure G} {Q : ℝ} (B : BallSystem G μ Q)
variable {U : Type*} [MeasurableSpace U] (S : B.ReciprocalSteps U)
    (ν : Measure U) [IsProbabilityMeasure ν]

/-- The literal local displacement operator of the paper. -/
def displacementOperator (g : G × G → ℝ) (x : G × G) : ℝ :=
  ∑' n : ℤ, ∫ u, g (x + S.step n u) ∂ν

theorem energy_eq_operator_integral [SFinite μ] (g : G × G → ℝ)
    (N : Finset ℤ)
    (hzero : ∀ n ∉ N, ∀ u x, g x * g (x + S.step n u) = 0)
    (hint : ∀ n, Integrable (fun xu : (G × G) × U =>
      g xu.1 * g (xu.1 + S.step n xu.2)) ((μ.prod μ).prod ν)) :
    B.profileEnergy S ν g = ∫ x, g x * B.displacementOperator S ν g x ∂μ.prod μ := by
  classical
  unfold profileEnergy displacementOperator
  simp_rw [← tsum_mul_left, ← integral_const_mul]
  have hz (n : ℤ) (hn : n ∉ N) (x : G × G) :
      (∫ u, g x * g (x + S.step n u) ∂ν) = 0 := by
    simp_rw [hzero n hn]
    simp
  simp_rw [tsum_eq_sum (s := N) (fun n hn => hz n hn _)]
  rw [integral_finsetSum N (fun n _ => (hint n).integral_prod_left)]
  rw [tsum_eq_sum (s := N)]
  · apply Finset.sum_congr rfl
    intro n hn
    exact (integral_integral_swap (hint n)).symm
  · intro n hn
    simp_rw [hzero n hn]
    simp

theorem shellProfile_measurable (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    Measurable (B.shellProfile k I w) := by
  apply Finset.measurable_sum
  intro ij hij
  exact measurable_const.indicator (B.shellCell_measurable k ij)

theorem shellProfile_norm_le (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (x : G × G) : ‖B.shellProfile k I w x‖ ≤ ∑ ij ∈ I, |w ij| := by
  classical
  unfold shellProfile
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij hij
  by_cases hx : x ∈ B.shellCell k ij <;> simp [Set.indicator, hx]

theorem shellProfile_support (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (Lx Ly : ℕ) (hI : ∀ ij ∈ I, ij.1 ≤ Lx ∧ ij.2 ≤ Ly)
    {x : G × G} (hx : B.shellProfile k I w x ≠ 0) :
    x ∈ (B.ball Lx : Set G) ×ˢ (B.ball (k + (Ly : ℤ)) : Set G) := by
  classical
  have hex : ∃ ij ∈ I, x ∈ B.shellCell k ij := by
    by_contra h
    push Not at h
    exact hx (B.shellProfile_eq_zero k I w h)
  obtain ⟨ij, hij, hx⟩ := hex
  have hi := hI ij hij
  exact ⟨B.mono (by omega) (B.shell_subset 0 ij.1 hx.1),
    B.mono (by omega) (B.shell_subset k ij.2 hx.2)⟩

omit [MeasurableSpace U] in
theorem shellProfile_overlap_zero (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (Lx Ly : ℕ) (hI : ∀ ij ∈ I, ij.1 ≤ Lx ∧ ij.2 ≤ Ly)
    (n : ℤ) (hn : n ∉ Finset.Icc (-(Lx : ℤ)) (k + (Ly : ℤ))) (u : U) (x : G × G) :
    B.shellProfile k I w x * B.shellProfile k I w (x + S.step n u) = 0 := by
  by_contra h
  obtain ⟨hx, hy⟩ := mul_ne_zero_iff.mp h
  have hx := B.shellProfile_support k I w Lx Ly hI hx
  have hy := B.shellProfile_support k I w Lx Ly hI hy
  have hsx : (S.step n u).1 ∈ B.ball Lx := by
    have := (B.ball Lx).sub_mem hy.1 hx.1
    simpa using this
  have hsy : (S.step n u).2 ∈ B.ball (k + (Ly : ℤ)) := by
    have := (B.ball (k + (Ly : ℤ))).sub_mem hy.2 hx.2
    simpa using this
  apply hn
  exact Finset.mem_Icc.mpr ⟨(S.fst_mem n u _).mp hsx, (S.snd_mem n u _).mp hsy⟩

theorem shellProfile_joint_integrable [MeasurableAdd₂ G] [SFinite μ]
    (hQ : 0 < Q) (hs : ∀ n, Measurable (S.step n))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (Lx Ly : ℕ) (hI : ∀ ij ∈ I, ij.1 ≤ Lx ∧ ij.2 ≤ Ly) (n : ℤ) :
    Integrable (fun xu : (G × G) × U =>
      B.shellProfile k I w xu.1 * B.shellProfile k I w (xu.1 + S.step n xu.2))
      ((μ.prod μ).prod ν) := by
  classical
  let M : ℝ := ∑ ij ∈ I, |w ij|
  let R : Set (G × G) := (B.ball Lx : Set G) ×ˢ (B.ball (k + (Ly : ℤ)) : Set G)
  have hRm : MeasurableSet R := (B.measurable _).prod (B.measurable _)
  have hRf : (μ.prod μ) R ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (B.ball_measure_ne_top hQ _) (B.ball_measure_ne_top hQ _)
  have hdom : Integrable ((R ×ˢ (Set.univ : Set U)).indicator (fun _ => M * M))
      ((μ.prod μ).prod ν) := by
    apply (integrable_indicator_iff (hRm.prod MeasurableSet.univ)).mpr
    apply integrableOn_const
    · simpa only [Measure.prod_prod, measure_univ, mul_one] using hRf
    · finiteness
  apply hdom.mono'
  · have hshift : Measurable (fun xu : (G × G) × U => xu.1 + S.step n xu.2) :=
      (measurable_fst.fst.add ((hs n).fst.comp measurable_snd)).prodMk
        (measurable_fst.snd.add ((hs n).snd.comp measurable_snd))
    exact ((B.shellProfile_measurable k I w).comp measurable_fst |>.mul
      ((B.shellProfile_measurable k I w).comp hshift)).aestronglyMeasurable
  · filter_upwards [] with xu
    by_cases hx : xu.1 ∈ R
    · simp only [Set.indicator_of_mem (show xu ∈ R ×ˢ (Set.univ : Set U) from ⟨hx, Set.mem_univ _⟩),
        norm_mul]
      exact mul_le_mul (B.shellProfile_norm_le k I w xu.1)
        (B.shellProfile_norm_le k I w _) (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    · have hz : B.shellProfile k I w xu.1 = 0 := by
        by_contra hz
        exact hx (B.shellProfile_support k I w Lx Ly hI hz)
      simp [hz, Set.indicator, hx]

/-- For arbitrary finite shell profiles the order in the manuscript is exactly
the order evaluated in `shellProfile_energy`. -/
theorem shellProfile_energy_operator [MeasurableAdd₂ G] [SFinite μ]
    (hQ : 0 < Q) (hs : ∀ n, Measurable (S.step n))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    B.profileEnergy S ν (B.shellProfile k I w) =
      ∫ x, B.shellProfile k I w x *
        B.displacementOperator S ν (B.shellProfile k I w) x ∂μ.prod μ := by
  have hI : ∀ ij ∈ I, ij.1 ≤ I.sup Prod.fst ∧ ij.2 ≤ I.sup Prod.snd :=
    fun ij hij => ⟨Finset.le_sup hij, Finset.le_sup hij⟩
  apply B.energy_eq_operator_integral S ν _
    (Finset.Icc (-((I.sup Prod.fst : ℕ) : ℤ)) (k + ((I.sup Prod.snd : ℕ) : ℤ)))
  · exact B.shellProfile_overlap_zero S k I w _ _ hI
  · exact B.shellProfile_joint_integrable S ν hQ hs k I w _ _ hI

/-- Exact `Z(g) = Q^k wᵀKw` for the literal operator `T` in the paper. -/
theorem shellProfile_operator_eq [MeasurableAdd₂ G] [SFinite μ] [μ.IsAddRightInvariant]
    (hQ : 0 < Q) (hs : ∀ n, Measurable (S.step n))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    (∫ x, B.shellProfile k I w x *
      B.displacementOperator S ν (B.shellProfile k I w) x ∂μ.prod μ) =
      Q ^ k * ∑ ij ∈ I, ∑ rt ∈ I,
        w ij * shellKernel Q k ij.1 ij.2 rt.1 rt.2 * w rt := by
  rw [← B.shellProfile_energy_operator S ν hQ hs]
  exact B.shellProfile_energy S ν hQ k I w

/-- The exact weighted local functional `Z(g) / A(g)^(1+δ)`, with
`p = 2/(1+δ)` and the manuscript's literal displacement operator. -/
def weightedFunctional (δ : ℝ) (g : G × G → ℝ) : ℝ :=
  (∫ x, g x * B.displacementOperator S ν g x ∂μ.prod μ) /
    (∫ x, g x ^ (2 / (1 + δ)) ∂μ.prod μ) ^ (1 + δ)

theorem shellProfile_functional [MeasurableAdd₂ G] [SFinite μ] [μ.IsAddRightInvariant]
    (hQ : 0 < Q) (hs : ∀ n, Measurable (S.step n))
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    B.weightedFunctional S ν δ (B.shellProfile k I w) =
      (Q ^ k * ∑ ij ∈ I, ∑ rt ∈ I,
        w ij * shellKernel Q k ij.1 ij.2 rt.1 rt.2 * w rt) /
      (Q ^ k * ∑ ij ∈ I, shellMass Q ij.1 * shellMass Q ij.2 *
        w ij ^ (2 / (1 + δ))) ^ (1 + δ) := by
  unfold weightedFunctional
  rw [B.shellProfile_operator_eq S ν hQ hs,
    B.shellProfile_moment hQ k I w (div_ne_zero (by norm_num) (by linarith))]

end UnitDistance.Local.BallSystem
