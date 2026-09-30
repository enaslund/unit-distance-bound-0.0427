module

public import UnitDistance.LocalProfiles

@[expose] public section
set_option backward.privateInPublic true


/-! # The shell energy as an actual iterated Haar integral -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace UnitDistance.Local

section DifferenceIntegration

variable {X : Type*} [MeasurableSpace X] {ρ : Measure X}

theorem integrable_fourDiff (f : ℕ → ℕ → ℕ → ℕ → X → ℝ)
    (hf : ∀ i j r t, Integrable (f i j r t) ρ) (i j r t : ℕ) :
    Integrable (fun x => fourDiff (fun i j r t => f i j r t x) i j r t) ρ := by
  cases i <;> cases j <;> cases r <;> cases t <;>
    simp only [fourDiff, mixedDiff, backDiff] <;> fun_prop

theorem integral_fourDiff (f : ℕ → ℕ → ℕ → ℕ → X → ℝ)
    (hf : ∀ i j r t, Integrable (f i j r t) ρ) (i j r t : ℕ) :
    (∫ x, fourDiff (fun i j r t => f i j r t x) i j r t ∂ρ) =
      fourDiff (fun i j r t => ∫ x, f i j r t x ∂ρ) i j r t := by
  cases i <;> cases j <;> cases r <;> cases t <;>
    simp (disch := fun_prop) only [fourDiff, mixedDiff, backDiff, integral_sub]

theorem summable_backDiff {N : Type*} (f : ℕ → N → ℝ)
    (hf : ∀ i, Summable (f i)) (i : ℕ) :
    Summable (fun n => backDiff (fun i => f i n) i) := by
  cases i with
  | zero => exact hf 0
  | succ i => exact (hf (i + 1)).sub (hf i)

theorem tsum_backDiff {N : Type*} (f : ℕ → N → ℝ)
    (hf : ∀ i, Summable (f i)) (i : ℕ) :
    (∑' n, backDiff (fun i => f i n) i) = backDiff (fun i => ∑' n, f i n) i := by
  cases i with
  | zero => rfl
  | succ i => exact (hf (i + 1)).tsum_sub (hf i)

theorem summable_fourDiff {N : Type*} (f : ℕ → ℕ → ℕ → ℕ → N → ℝ)
    (hf : ∀ i j r t, Summable (f i j r t)) (i j r t : ℕ) :
    Summable (fun n => fourDiff (fun i j r t => f i j r t n) i j r t) := by
  unfold fourDiff mixedDiff
  apply summable_backDiff
  intro i
  apply summable_backDiff
  intro r
  apply summable_backDiff
  intro j
  exact summable_backDiff _ (hf i j r) _

theorem tsum_fourDiff {N : Type*} (f : ℕ → ℕ → ℕ → ℕ → N → ℝ)
    (hf : ∀ i j r t, Summable (f i j r t)) (i j r t : ℕ) :
    (∑' n, fourDiff (fun i j r t => f i j r t n) i j r t) =
      fourDiff (fun i j r t => ∑' n, f i j r t n) i j r t := by
  unfold fourDiff mixedDiff
  simp_rw [tsum_backDiff _ (fun i => summable_backDiff _ (fun r =>
    summable_backDiff _ (fun j => summable_backDiff _ (hf i j r) _) _) _)]
  simp_rw [tsum_backDiff _ (fun r => summable_backDiff _ (fun j =>
    summable_backDiff _ (hf _ j r) _) _)]
  simp_rw [tsum_backDiff _ (fun j => summable_backDiff _ (hf _ j _) _)]
  simp_rw [tsum_backDiff _ (hf _ _ _)]

end DifferenceIntegration

theorem fourDiff_separated (a b c d : ℕ → ℝ) (i j r t : ℕ) :
    fourDiff (fun i j r t => a i * b j * (c r * d t)) i j r t =
      backDiff a i * backDiff b j * (backDiff c r * backDiff d t) := by
  cases i <;> cases j <;> cases r <;> cases t <;>
    simp only [fourDiff, mixedDiff, backDiff] <;> ring

namespace BallSystem

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
variable {μ : Measure G} {Q : ℝ} (B : BallSystem G μ Q)

omit [MeasurableAdd G] in
theorem shell_indicator_backDiff (k : ℤ) (i : ℕ) (x : G) :
    (B.shell k i).indicator (fun _ => (1 : ℝ)) x =
      backDiff (fun i => (B.ball (k + (i : ℕ)) : Set G).indicator (fun _ => (1 : ℝ)) x) i := by
  classical
  cases i with
  | zero => simp [shell, backDiff]
  | succ i =>
    simp only [shell, backDiff, Set.indicator, Set.mem_sdiff]
    have hsub := B.mono (show k + (i : ℤ) ≤ k + (i + 1 : ℕ) by omega)
    split_ifs <;> simp_all
    exact ‹x ∉ B.ball _› (hsub ‹x ∈ B.ball _›)

omit [MeasurableAdd G] in
theorem rectangle_indicator_product (a b : ℤ) (x : G × G) :
    B.rectangle a b x =
      (B.ball a : Set G).indicator (fun _ => (1 : ℝ)) x.1 *
      (B.ball b : Set G).indicator (fun _ => (1 : ℝ)) x.2 := by
  classical
  simp only [rectangle, Set.indicator, Set.mem_prod]
  split_ifs <;> simp_all

omit [MeasurableAdd G] in
theorem shellCell_indicator_product (k : ℕ) (ij : ℕ × ℕ) (x : G × G) :
    (B.shellCell k ij).indicator (fun _ => (1 : ℝ)) x =
      (B.shell 0 ij.1).indicator (fun _ => (1 : ℝ)) x.1 *
      (B.shell k ij.2).indicator (fun _ => (1 : ℝ)) x.2 := by
  classical
  simp only [shellCell, Set.indicator, Set.mem_prod]
  split_ifs <;> simp_all

omit [MeasurableAdd G] in
theorem shell_overlap_fourDiff (k i j r t : ℕ) (z x : G × G) :
    (B.shellCell k (i,j)).indicator (fun _ => (1 : ℝ)) x *
      (B.shellCell k (r,t)).indicator (fun _ => (1 : ℝ)) (x + z) =
      fourDiff (fun i j r t => B.rectangle i (k + (j : ℤ)) x *
        B.rectangle r (k + (t : ℤ)) (x + z)) i j r t := by
  simp_rw [B.shellCell_indicator_product, B.shell_indicator_backDiff,
    B.rectangle_indicator_product, zero_add]
  exact (fourDiff_separated _ _ _ _ i j r t).symm

theorem rectangle_overlap_integrable [SFinite μ] (hQ : 0 < Q)
    (a b c e : ℤ) (z : G × G) :
    Integrable (fun x => B.rectangle a b x * B.rectangle c e (x + z)) (μ.prod μ) := by
  simp_rw [B.rectangle_overlap_integrand]
  apply (integrable_indicator_iff
    ((B.ballOverlap_measurable a c z.1).prod (B.ballOverlap_measurable b e z.2))).mpr
  refine integrableOn_const ?_
  apply measure_ne_top_of_subset
    (show B.ballOverlap a c z.1 ×ˢ B.ballOverlap b e z.2 ⊆
      (B.ball a : Set G) ×ˢ (B.ball b : Set G) from fun x hx => ⟨hx.1.1, hx.2.1⟩)
  rw [Measure.prod_prod]
  exact ENNReal.mul_ne_top (B.ball_measure_ne_top hQ _) (B.ball_measure_ne_top hQ _)

theorem shell_overlap_integrable [SFinite μ] (hQ : 0 < Q)
    (k i j r t : ℕ) (z : G × G) :
    Integrable (fun x => (B.shellCell k (i,j)).indicator (fun _ => (1 : ℝ)) x *
      (B.shellCell k (r,t)).indicator (fun _ => (1 : ℝ)) (x + z)) (μ.prod μ) := by
  simp_rw [B.shell_overlap_fourDiff]
  exact integrable_fourDiff _ (fun _ _ _ _ => B.rectangle_overlap_integrable hQ _ _ _ _ z) _ _ _ _

variable {U : Type*} [MeasurableSpace U] (S : B.ReciprocalSteps U)
    (ν : Measure U) [IsProbabilityMeasure ν]

theorem rectangle_inner_integrable [SFinite μ] [μ.IsAddRightInvariant]
    (a b c e n : ℤ) :
    Integrable (fun u => ∫ x, B.rectangle a b x *
      B.rectangle c e (x + S.step n u) ∂μ.prod μ) ν := by
  classical
  convert integrable_const (μ := ν)
    (if -max a c ≤ n ∧ n ≤ max b e then Q ^ min a c * Q ^ min b e else 0) using 1
  funext u
  simp only [B.rectangle_overlap, S.fst_mem, S.snd_mem]

theorem rectangle_average_summable [SFinite μ] [μ.IsAddRightInvariant]
    (a b c e : ℤ) :
    Summable (fun n : ℤ => ∫ u, ∫ x, B.rectangle a b x *
      B.rectangle c e (x + S.step n u) ∂μ.prod μ ∂ν) := by
  simp_rw [B.rectangle_unit_average S ν]
  apply summable_of_ne_finset_zero (s := Finset.Icc (-max a c) (max b e))
  intro n hn
  simp [hn]

theorem shell_overlap_integral [SFinite μ] (hQ : 0 < Q)
    (k i j r t : ℕ) (z : G × G) :
    (∫ x, (B.shellCell k (i,j)).indicator (fun _ => (1 : ℝ)) x *
      (B.shellCell k (r,t)).indicator (fun _ => (1 : ℝ)) (x + z) ∂μ.prod μ) =
      fourDiff (fun i j r t => ∫ x, B.rectangle i (k + (j : ℤ)) x *
        B.rectangle r (k + (t : ℤ)) (x + z) ∂μ.prod μ) i j r t := by
  simp_rw [B.shell_overlap_fourDiff]
  exact integral_fourDiff _ (fun _ _ _ _ => B.rectangle_overlap_integrable hQ _ _ _ _ z) _ _ _ _

/-- The shell energy is defined by actual additive and unit Haar integrals. -/
def shellGram (k i j r t : ℕ) : ℝ :=
  ∑' n : ℤ, ∫ u, ∫ x,
    (B.shellCell k (i,j)).indicator (fun _ => (1 : ℝ)) x *
      (B.shellCell k (r,t)).indicator (fun _ => (1 : ℝ)) (x + S.step n u)
    ∂μ.prod μ ∂ν

theorem shellGram_fourDiff [SFinite μ] [μ.IsAddRightInvariant] (hQ : 0 < Q)
    (k i j r t : ℕ) :
    B.shellGram S ν k i j r t =
      fourDiff (fun i j r t => B.rectangleGram S ν i (k + (j : ℤ)) r (k + (t : ℤ)))
        i j r t := by
  unfold shellGram
  simp_rw [B.shell_overlap_integral hQ]
  simp_rw [integral_fourDiff _ (fun _ _ _ _ => B.rectangle_inner_integrable S ν _ _ _ _ _)]
  exact tsum_fourDiff _ (fun _ _ _ _ => B.rectangle_average_summable S ν _ _ _ _) _ _ _ _

theorem rectangleGram_nat [SFinite μ] [μ.IsAddRightInvariant]
    (k i j r t : ℕ) :
    B.rectangleGram S ν i (k + (j : ℤ)) r (k + (t : ℤ)) =
      rectangleShellGram Q k i j r t := by
  rw [B.rectangleGram_eq]
  have hmin : min ((k : ℤ) + (j : ℤ)) ((k : ℤ) + (t : ℤ)) =
      ((k + min j t : ℕ) : ℤ) := by omega
  have hmax : max (i : ℤ) r + max ((k : ℤ) + (j : ℤ)) ((k : ℤ) + (t : ℤ)) + 1 =
      ((max i r + k + max j t + 1 : ℕ) : ℤ) := by omega
  have hn : (max (i : ℤ) r + max ((k : ℤ) + (j : ℤ)) ((k : ℤ) + (t : ℤ)) + 1).toNat =
      max i r + k + max j t + 1 := by omega
  rw [hn, hmin]
  have hm : min (i : ℤ) r = ((min i r : ℕ) : ℤ) := by omega
  rw [hm]
  norm_cast
  simp only [pow_add, Nat.cast_add, Nat.cast_one, rectangleShellGram, minKernel]
  ring

/-- The manuscript's complete shell overlap formula, now for actual Haar
integrals of actual shell indicators. -/
theorem shellGram_eq [SFinite μ] [μ.IsAddRightInvariant] (hQ : 0 < Q)
    (k i j r t : ℕ) :
    B.shellGram S ν k i j r t = Q ^ k * shellKernel Q k i j r t := by
  rw [B.shellGram_fourDiff S ν hQ]
  simp_rw [B.rectangleGram_nat S ν]
  exact fourDiff_rectangleShellGram Q k i j r t

theorem shell_inner_integrable [SFinite μ] [μ.IsAddRightInvariant] (hQ : 0 < Q)
    (k i j r t : ℕ) (n : ℤ) :
    Integrable (fun u => ∫ x,
      (B.shellCell k (i,j)).indicator (fun _ => (1 : ℝ)) x *
      (B.shellCell k (r,t)).indicator (fun _ => (1 : ℝ)) (x + S.step n u) ∂μ.prod μ) ν := by
  simp_rw [B.shell_overlap_integral hQ]
  exact integrable_fourDiff _ (fun _ _ _ _ => B.rectangle_inner_integrable S ν _ _ _ _ n) _ _ _ _

theorem shell_average_summable [SFinite μ] [μ.IsAddRightInvariant] (hQ : 0 < Q)
    (k i j r t : ℕ) :
    Summable (fun n : ℤ => ∫ u, ∫ x,
      (B.shellCell k (i,j)).indicator (fun _ => (1 : ℝ)) x *
      (B.shellCell k (r,t)).indicator (fun _ => (1 : ℝ)) (x + S.step n u) ∂μ.prod μ ∂ν) := by
  simp_rw [B.shell_overlap_integral hQ]
  simp_rw [integral_fourDiff _ (fun _ _ _ _ => B.rectangle_inner_integrable S ν _ _ _ _ _)]
  exact summable_fourDiff _ (fun _ _ _ _ => B.rectangle_average_summable S ν _ _ _ _) _ _ _ _

omit [MeasurableAdd G] in
theorem shellProfile_mul (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (x y : G × G) :
    B.shellProfile k I w x * B.shellProfile k I w y =
      ∑ v ∈ I ×ˢ I, (w v.1 * w v.2) *
        ((B.shellCell k v.1).indicator (fun _ => (1 : ℝ)) x *
          (B.shellCell k v.2).indicator (fun _ => (1 : ℝ)) y) := by
  classical
  rw [shellProfile, shellProfile, Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro rt hrt
  simp only [Set.indicator]
  split_ifs <;> ring

/-- The weighted overlap energy in Tonelli order, with normalized unit average. -/
def profileEnergy (g : G × G → ℝ) : ℝ :=
  ∑' n : ℤ, ∫ u, ∫ x, g x * g (x + S.step n u) ∂μ.prod μ ∂ν

/-- Exact weighted local `Z(g)` formula. Both sides are defined independently:
the left is the Haar integral, and the right is the explicit finite shell matrix. -/
theorem shellProfile_energy [SFinite μ] [μ.IsAddRightInvariant] (hQ : 0 < Q)
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    B.profileEnergy S ν (B.shellProfile k I w) =
      Q ^ k * ∑ ij ∈ I, ∑ rt ∈ I,
        w ij * shellKernel Q k ij.1 ij.2 rt.1 rt.2 * w rt := by
  unfold profileEnergy
  simp_rw [B.shellProfile_mul k I w]
  simp_rw [integral_finsetSum (I ×ˢ I) (fun v _ =>
    (B.shell_overlap_integrable hQ k v.1.1 v.1.2 v.2.1 v.2.2 _).const_mul (w v.1 * w v.2))]
  simp_rw [integral_const_mul]
  simp_rw [integral_finsetSum (I ×ˢ I) (fun v _ =>
    (B.shell_inner_integrable S ν hQ k v.1.1 v.1.2 v.2.1 v.2.2 _).const_mul (w v.1 * w v.2))]
  simp_rw [integral_const_mul]
  rw [Summable.tsum_finsetSum (fun v _ =>
    (B.shell_average_summable S ν hQ k v.1.1 v.1.2 v.2.1 v.2.2).mul_left (w v.1 * w v.2))]
  simp_rw [tsum_mul_left]
  change (∑ v ∈ I ×ˢ I, (w v.1 * w v.2) * B.shellGram S ν k _ _ _ _) = _
  simp_rw [B.shellGram_eq S ν hQ]
  rw [Finset.sum_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rt hrt
  ring

end BallSystem
end UnitDistance.Local
