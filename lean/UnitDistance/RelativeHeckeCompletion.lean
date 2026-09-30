/-
The proof of `completedDedekindEntire_one_sub` is adapted from AINTLIB,
Copyright (c) 2026 Chris Birkbeck, under the Apache 2.0 license preserved at
`third-party/aintlib/LICENSE`. Other bridges are local additions.
-/
module

public import UnitDistance.Upstream.AINTLIB.CompletedZeta.Existence
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Topology.Algebra.Module.Cardinality
public import UnitDistance.RelativeHeckeGamma

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual meromorphic relative completion

The imported theta--Mellin construction supplies ordinary completed Dedekind
zeta functions. Their pole-cleared quotient has the functional equation and
has the expected positive value at one. These conclusions do not assert
that the relative quotient is entire: cancellation of nontrivial denominator
zeros is a separate Hecke theorem and is not an assumption hidden here.
-/

noncomputable section
open Filter Topology NumberField NumberField.InfinitePlace DedekindResidue
open scoped Real ComplexOrder

namespace UnitDistance.NumberFieldAnalysis

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

/-- The ordinary completion factor on the positive real axis. -/
def dedekindCompletionPrefactorReal (s : ℝ) : ℝ :=
  (|discr K| : ℝ) ^ (s/2) *
    ((Real.pi ^ (-(s/2)) * Real.Gamma (s/2)) ^ nrRealPlaces K *
      (2 * (2*Real.pi) ^ (-s) * Real.Gamma s) ^ nrComplexPlaces K)

theorem completedZetaPrefactor_ofReal (s : ℝ) :
    completedZetaPrefactor K (s : ℂ) =
      (dedekindCompletionPrefactorReal K s : ℂ) := by
  unfold completedZetaPrefactor gammaFactor dedekindCompletionPrefactorReal
  rw [show (s : ℂ)/2 = ((s/2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), Gammaℝ_ofReal, Gammaℂ_ofReal]
  push_cast
  rfl

theorem dedekindCompletionPrefactorReal_pos {s : ℝ} (hs : 0 < s) :
    0 < dedekindCompletionPrefactorReal K s := by
  have hD : (0 : ℝ) < |(discr K : ℝ)| := by
    exact_mod_cast abs_pos.mpr (discr_ne_zero K)
  have hG := Real.Gamma_pos_of_pos hs
  have hGh := Real.Gamma_pos_of_pos (half_pos hs)
  unfold dedekindCompletionPrefactorReal
  exact mul_pos (Real.rpow_pos_of_pos hD _)
    (mul_pos (pow_pos (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) hGh) _)
      (pow_pos (mul_pos (mul_pos two_pos
        (Real.rpow_pos_of_pos (by positivity : (0:ℝ)<2*Real.pi) _)) hG) _))

theorem continuousAt_dedekindCompletionPrefactorReal {s : ℝ} (hs : 0 < s) :
    ContinuousAt (dedekindCompletionPrefactorReal K) s := by
  have hD : (|discr K| : ℝ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)
  have hG : ContinuousAt Real.Gamma s :=
    (Real.differentiableAt_Gamma (fun n => by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith)).continuousAt
  have hGh : ContinuousAt (fun x : ℝ => Real.Gamma (x/2)) s := by
    exact ContinuousAt.comp (f := fun x : ℝ => x/2) (x := s)
      (Real.differentiableAt_Gamma (fun n => by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith)).continuousAt (by fun_prop)
  have hDp : ContinuousAt (fun x : ℝ => (|discr K| : ℝ) ^ (x/2)) s :=
    ContinuousAt.comp (f := fun x : ℝ => x/2) (x := s)
      (Real.continuous_const_rpow hD).continuousAt (continuousAt_id.div_const 2)
  have hPp : ContinuousAt (fun x : ℝ => Real.pi ^ (-(x/2))) s :=
    ContinuousAt.comp (f := fun x : ℝ => -(x/2)) (x := s)
      (Real.continuous_const_rpow Real.pi_ne_zero).continuousAt
      (continuousAt_id.div_const 2).neg
  have hTp : ContinuousAt (fun x : ℝ => (2*Real.pi) ^ (-x)) s :=
    ContinuousAt.comp (f := fun x : ℝ => -x) (x := s)
      (Real.continuous_const_rpow (mul_ne_zero two_ne_zero Real.pi_ne_zero)).continuousAt
      continuousAt_id.neg
  exact hDp.mul ((hPp.mul hGh).pow _ |>.mul
    ((continuousAt_const.mul hTp).mul hG |>.pow _))

/-- Functional equation after removing the two ordinary poles. This short
continuity argument is adapted from AINTLIB's `AnalyticControl.lean`; the
large strip-growth development is not needed for this identity. -/
theorem completedDedekindEntire_one_sub (s : ℂ) :
    completedDedekindZetaEntire K (1-s) = completedDedekindZetaEntire K s := by
  have hcont₁ : Continuous (fun z : ℂ => completedDedekindZetaEntire K (1-z)) :=
    ((differentiable_completedDedekindZetaEntire K).comp
      ((differentiable_const (1:ℂ)).sub differentiable_id)).continuous
  have hcont₂ := (differentiable_completedDedekindZetaEntire K).continuous
  have hdense : Dense ({(0:ℂ), 1}ᶜ : Set ℂ) :=
    Set.Countable.dense_compl ℝ (Set.toFinite ({(0:ℂ), 1} : Set ℂ)).countable
  refine congrFun (Continuous.ext_on hdense hcont₁ hcont₂ ?_) s
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
  obtain ⟨hz₀, hz₁⟩ := hz
  have h₀ : (1:ℂ)-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz₁)
  have h₁ : (1:ℂ)-z ≠ 1 := by
    intro h
    apply hz₀
    linear_combination -h
  change completedDedekindZetaEntire K (1-z) = completedDedekindZetaEntire K z
  rw [completedDedekindZetaEntire_eq K h₀ h₁,
    completedDedekindZetaEntire_eq K hz₀ hz₁, completedDedekindZeta_one_sub K z]
  ring

/-- The analytic value of the pole-cleared completion at one is the
ordinary gamma prefactor times Mathlib's actual class-number residue. -/
theorem completedDedekindEntire_one :
    completedDedekindZetaEntire K 1 =
      ((dedekindCompletionPrefactorReal K 1 * dedekindZeta_residue K : ℝ) : ℂ) := by
  have h₁ : Tendsto (fun s : ℝ => completedDedekindZetaEntire K (s:ℂ))
      (𝓝[>] 1) (𝓝 (completedDedekindZetaEntire K 1)) := by
    have hc : Continuous (fun s : ℝ => completedDedekindZetaEntire K (s:ℂ)) :=
      (differentiable_completedDedekindZetaEntire K).continuous.comp Complex.continuous_ofReal
    simpa only [Complex.ofReal_one] using
      ((hc.continuousAt (x := (1:ℝ))).tendsto.mono_left nhdsWithin_le_nhds)
  have hp : Tendsto (fun s : ℝ => (dedekindCompletionPrefactorReal K s : ℂ))
      (𝓝[>] 1) (𝓝 (dedekindCompletionPrefactorReal K 1 : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_dedekindCompletionPrefactorReal K (by norm_num : (0:ℝ)<1))).tendsto
        |>.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun s : ℝ => (s:ℂ)) (𝓝[>] 1) (𝓝 (1:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h₂ := (hs.mul hp).mul (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  simp only [one_mul, ← Complex.ofReal_mul] at h₂
  apply tendsto_nhds_unique h₁
  apply h₂.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs₀ : (s:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hs))
  have hs₁ : (s:ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hs)
  rw [completedDedekindZetaEntire_eq K hs₀ hs₁,
    completedDedekindZeta_real K hs, completedZetaPrefactor_ofReal]
  push_cast
  ring

theorem completedDedekindEntire_one_ne_zero :
    completedDedekindZetaEntire K 1 ≠ 0 := by
  rw [completedDedekindEntire_one]
  exact Complex.ofReal_ne_zero.mpr (mul_ne_zero
    (dedekindCompletionPrefactorReal_pos K (by norm_num : (0:ℝ)<1)).ne'
    (dedekindZeta_residue_ne_zero K))

/-- The quotient uses entire ordinary completions, so its value at one is
well defined and is not the quotient of totalized pole values. -/
def completedRelativeQuotient (s : ℂ) : ℂ :=
  completedDedekindZetaEntire K s / completedDedekindZetaEntire F s

theorem completedRelativeQuotient_one_sub (s : ℂ) :
    completedRelativeQuotient K F (1-s) = completedRelativeQuotient K F s := by
  simp only [completedRelativeQuotient, completedDedekindEntire_one_sub]

theorem meromorphic_completedRelativeQuotient :
    Meromorphic (completedRelativeQuotient K F) := by
  intro s
  exact ((differentiable_completedDedekindZetaEntire K).analyticAt s).meromorphicAt.div
    ((differentiable_completedDedekindZetaEntire F).analyticAt s).meromorphicAt

theorem analyticAt_completedRelativeQuotient_one :
    AnalyticAt ℂ (completedRelativeQuotient K F) 1 :=
  ((differentiable_completedDedekindZetaEntire K).analyticAt 1).div
    ((differentiable_completedDedekindZetaEntire F).analyticAt 1)
    (completedDedekindEntire_one_ne_zero F)

theorem completedRelativeQuotient_one :
    completedRelativeQuotient K F 1 =
      ((dedekindCompletionPrefactorReal K 1 / dedekindCompletionPrefactorReal F 1 *
        relativeResidue K F : ℝ) : ℂ) := by
  rw [completedRelativeQuotient, completedDedekindEntire_one, completedDedekindEntire_one]
  simp only [relativeResidue, Complex.ofReal_mul, Complex.ofReal_div]
  ring

theorem completedRelativeQuotient_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRelativeQuotient K F s =
      completedZetaPrefactor K s / completedZetaPrefactor F s * relativeZeta K F s := by
  have hs₀ : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have hs₁ : s ≠ 1 := by intro h; simp [h] at hs
  rw [completedRelativeQuotient, completedDedekindZetaEntire_eq K hs₀ hs₁,
    completedDedekindZetaEntire_eq F hs₀ hs₁,
    completedDedekindZeta_eq_of_one_lt_re K hs,
    completedDedekindZeta_eq_of_one_lt_re F hs,
    mul_div_mul_left _ _ (mul_ne_zero hs₀ (sub_ne_zero.mpr hs₁))]
  unfold relativeZeta
  ring

end UnitDistance.NumberFieldAnalysis
