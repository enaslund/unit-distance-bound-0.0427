module

public import UnitDistance.LocalOverlapIntegrability
public import UnitDistance.LocalShellEnergy
public import UnitDistance.GeometryEndpointExchange

@[expose] public section
set_option backward.privateInPublic true


/-!
# Normalization and moments of the actual local overlap law

The supported exponential density equals the actual shell-profile product.
Its normalization is the proved local operator energy. The finite coefficient
bound supplies both endpoint second moments and a uniform variance bound;
reflection and translation give equality of their means and variances.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace UnitDistance.Local.BallSystem

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  {μ : Measure G} [SFinite μ] {Q : ℝ} (B : BallSystem G μ Q)
  {U : Type*} [MeasurableSpace U] (S : B.ReciprocalSteps U)
  (ν : Measure U) [IsProbabilityMeasure ν]

def shellOverlapBase (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    Measure ((ℤ × U) × (G × G)) :=
  supportedOverlapMeasure (Measure.count.prod ν) (μ.prod μ)
    (fun d => S.step d.1 d.2) (Function.support (B.shellProfile k I w))

def shellOverlapLaw (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    Measure ((ℤ × U) × (G × G)) :=
  overlapLaw (B.shellOverlapBase S ν k I w)
    (firstEnergy (B.shellEnergy k I w))
    (secondEnergy (B.shellEnergy k I w) (fun d => S.step d.1 d.2))
    (B.profileEnergy S ν (B.shellProfile k I w))

theorem shellOverlap_support_measurable (hs : ∀ n, Measurable (S.step n))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    MeasurableSet {z : (ℤ × U) × (G × G) |
      z.2 ∈ Function.support (B.shellProfile k I w) ∧
      z.2 + S.step z.1.1 z.1.2 ∈ Function.support (B.shellProfile k I w)} :=
  ((measurableSet_support (B.shellProfile_measurable k I w)).preimage measurable_snd).inter
    ((measurableSet_support (B.shellProfile_measurable k I w)).preimage
      (measurable_snd.add ((B.reciprocalSteps_measurable S hs).comp measurable_fst)))

theorem shellOverlap_indicator_exp (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (hw : ∀ ij ∈ I, 0 ≤ w ij) :
    ({z : (ℤ × U) × (G × G) |
      z.2 ∈ Function.support (B.shellProfile k I w) ∧
      z.2 + S.step z.1.1 z.1.2 ∈ Function.support (B.shellProfile k I w)}).indicator
      (fun z => Real.exp (-(firstEnergy (B.shellEnergy k I w) z +
        secondEnergy (B.shellEnergy k I w) (fun d => S.step d.1 d.2) z))) =
      B.shellOverlapWeight S k I w := by
  funext z
  by_cases hz : z.2 ∈ Function.support (B.shellProfile k I w) ∧
      z.2 + S.step z.1.1 z.1.2 ∈ Function.support (B.shellProfile k I w)
  · simp only [Set.indicator, Set.mem_setOf_eq, hz.1, hz.2, and_self, ite_true]
    simp only [firstEnergy, secondEnergy, neg_add, Real.exp_add, shellOverlapWeight]
    have h₁ := B.shellEnergy_weight k I w hw 1 hz.1
    have h₂ := B.shellEnergy_weight k I w hw 1 hz.2
    simpa only [neg_mul, one_mul, Real.rpow_one] using congrArg₂ (· * ·) h₁ h₂
  · simp only [Set.indicator, Set.mem_setOf_eq, hz, ↓reduceIte]
    unfold shellOverlapWeight
    symm
    by_cases hx : B.shellProfile k I w z.2 = 0
    · exact mul_eq_zero.mpr (Or.inl hx)
    · have hy : B.shellProfile k I w (z.2 + S.step z.1.1 z.1.2) = 0 := by
        by_contra hy
        exact hz ⟨hx, hy⟩
      exact mul_eq_zero.mpr (Or.inr hy)

theorem shellOverlap_exp_integrable (hQ : 0 < Q)
    (hs : ∀ n, Measurable (S.step n))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (hw : ∀ ij ∈ I, 0 ≤ w ij) :
    Integrable (fun z => Real.exp (-(firstEnergy (B.shellEnergy k I w) z +
      secondEnergy (B.shellEnergy k I w) (fun d => S.step d.1 d.2) z)))
      (B.shellOverlapBase S ν k I w) := by
  change IntegrableOn _ _ _
  rw [← integrable_indicator_iff (B.shellOverlap_support_measurable S hs k I w),
    B.shellOverlap_indicator_exp S k I w hw]
  exact B.shellOverlapWeight_integrable S ν hQ hs k I w

theorem shellOverlap_exp_integral (hQ : 0 < Q)
    (hs : ∀ n, Measurable (S.step n))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (hw : ∀ ij ∈ I, 0 ≤ w ij) :
    (∫ z, Real.exp (-(firstEnergy (B.shellEnergy k I w) z +
      secondEnergy (B.shellEnergy k I w) (fun d => S.step d.1 d.2) z))
      ∂B.shellOverlapBase S ν k I w) = B.profileEnergy S ν (B.shellProfile k I w) := by
  change (∫ z in _, _ ∂_) = _
  rw [← integral_indicator (B.shellOverlap_support_measurable S hs k I w),
    B.shellOverlap_indicator_exp S k I w hw]
  exact B.shellOverlapWeight_integral S ν hQ hs k I w

theorem shellOverlapLaw_probability (hQ : 0 < Q)
    (hs : ∀ n, Measurable (S.step n))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (hw : ∀ ij ∈ I, 0 ≤ w ij)
    (hZ : 0 < B.profileEnergy S ν (B.shellProfile k I w)) :
    IsProbabilityMeasure (B.shellOverlapLaw S ν k I w) :=
  overlapLaw_probability _ _ _ hZ (B.shellOverlap_exp_integrable S ν hQ hs k I w hw)
    (B.shellOverlap_exp_integral S ν hQ hs k I w hw)

theorem shellOverlapLaw_endpoint_moments [MeasurableNeg G]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (hQ : 0 < Q) (hs : ∀ n, Measurable (S.step n))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (hw : ∀ ij ∈ I, 0 ≤ w ij)
    (hZ : 0 < B.profileEnergy S ν (B.shellProfile k I w)) :
    MemLp (firstEnergy (B.shellEnergy k I w)) 2 (B.shellOverlapLaw S ν k I w) ∧
    MemLp (secondEnergy (B.shellEnergy k I w) (fun d => S.step d.1 d.2)) 2
      (B.shellOverlapLaw S ν k I w) ∧
    (∫ z, secondEnergy (B.shellEnergy k I w) (fun d => S.step d.1 d.2) z
      ∂B.shellOverlapLaw S ν k I w) =
      (∫ z, firstEnergy (B.shellEnergy k I w) z ∂B.shellOverlapLaw S ν k I w) ∧
    variance (firstEnergy (B.shellEnergy k I w)) (B.shellOverlapLaw S ν k I w) ≤
      (shellEnergyBound I w)^2 ∧
    variance (secondEnergy (B.shellEnergy k I w) (fun d => S.step d.1 d.2))
      (B.shellOverlapLaw S ν k I w) ≤ (shellEnergyBound I w)^2 := by
  letI := B.shellOverlapLaw_probability S ν hQ hs k I w hw hZ
  have hX : MemLp (firstEnergy (B.shellEnergy k I w)) 2 (B.shellOverlapLaw S ν k I w) :=
    B.shellEnergy_comp_memLp _ Prod.snd measurable_snd k I w 2
  have hsupp : ∀ x, -x ∈ Function.support (B.shellProfile k I w) ↔
      x ∈ Function.support (B.shellProfile k I w) := by
    intro x
    change B.shellProfile k I w (-x.1, -x.2) ≠ 0 ↔ B.shellProfile k I w x ≠ 0
    rw [B.shellProfile_invariant Neg.neg Neg.neg (by intros; simp) (by intros; simp) k I w x]
  obtain ⟨hY, hmean, hvar⟩ := even_supported_endpoint_moments (Measure.count.prod ν)
    (μ.prod μ) (fun d => S.step d.1 d.2) (B.reciprocalSteps_measurable S hs)
    _ (measurableSet_support (B.shellProfile_measurable k I w)) hsupp (B.shellEnergy k I w)
    (B.shellEnergy_neg k I w) _ hX
  have hv : variance (firstEnergy (B.shellEnergy k I w)) (B.shellOverlapLaw S ν k I w) ≤
      (shellEnergyBound I w)^2 :=
    B.shellEnergy_comp_variance_le _ Prod.snd measurable_snd k I w
  exact ⟨hX, hY, hmean, hv, hvar.trans_le hv⟩

end UnitDistance.Local.BallSystem
