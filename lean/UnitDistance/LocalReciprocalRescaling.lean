module

public import UnitDistance.LocalOneDimensionalProfiles
public import UnitDistance.LocalUnitInvariance

@[expose] public section
set_option backward.privateInPublic true


/-! # Exact reciprocal uniformizer rescaling of local Haar and shell profiles -/

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace UnitDistance.Local.ValuedHaar
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance rescalingMeasurableSpace : MeasurableSpace K := borel K
local instance rescalingBorelSpace : BorelSpace K := ⟨rfl⟩

def uniformizerMul (a : ℤ) : K ≃ₜ+ K :=
  ContinuousAddEquiv.mulLeft (Units.mk0 (uniformizer K ^ a) (zpow_ne_zero _ (uniformizer_ne_zero K)))

theorem uniformizerMul_mem_ball (a b : ℤ) (x : K) :
    uniformizerMul K a x ∈ ball K b ↔ x ∈ ball K (b+a) := by
  change intValuation K (uniformizer K ^ a*x) ≤ WithZero.exp b ↔
    intValuation K x ≤ WithZero.exp (b+a)
  rw [map_mul, intValuation_uniformizer_zpow]
  calc
    _ ↔ WithZero.exp a * (WithZero.exp (-a)*intValuation K x) ≤ WithZero.exp a*WithZero.exp b :=
      (mul_le_mul_iff_right₀ (show 0 < WithZero.exp a from WithZero.zero_lt_coe _)).symm
    _ ↔ _ := by
      rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul,
        ← WithZero.exp_add, add_comm a b]

theorem uniformizerMul_preimage_ball (a b : ℤ) :
    uniformizerMul K a ⁻¹' (ball K b : Set K) = ball K (b+a) := by
  ext x
  exact uniformizerMul_mem_ball K a b x

/-- The exact Jacobian of multiplication by a uniformizer power. -/
theorem uniformizerMul_map (a : ℤ) :
    (normalizedHaar K).map (uniformizerMul K a) =
      ENNReal.ofReal ((residueCard K : ℝ)^a) • normalizedHaar K := by
  let e := uniformizerMul K a
  haveI : ((normalizedHaar K).map e).IsAddHaarMeasure := inferInstance
  have hm : (normalizedHaar K).map e (unitBall K) = ENNReal.ofReal ((residueCard K : ℝ)^a) := by
    have he : Measurable (e : K → K) := e.continuous_toFun.measurable
    change ((normalizedHaar K).map e) (ball K 0 : Set K) = _
    rw [Measure.map_apply he (ball_measurable K 0), uniformizerMul_preimage_ball, zero_add]
    exact (ENNReal.ofReal_toReal (ball_compact K a).measure_lt_top.ne).symm.trans
      (congrArg ENNReal.ofReal (normalizedHaar_ball K a))
  rw [Measure.addHaarMeasure_unique ((normalizedHaar K).map e) (unitBall K), hm]
  rfl

def reciprocalRescaling (a : ℤ) : (K × K) ≃+ (K × K) :=
  (uniformizerMul K a).toAddEquiv.prodCongr (uniformizerMul K (-a)).toAddEquiv

theorem reciprocalRescaling_step (a n : ℤ) (u : ValuationOneUnits K) :
    reciprocalRescaling K a ((reciprocalSteps K).step n u) = (reciprocalSteps K).step (n+a) u := by
  apply Prod.ext
  · change uniformizer K ^ a * (uniformizer K ^ n * (u : K)) =
      uniformizer K ^ (n+a) * (u : K)
    rw [← mul_assoc, ← zpow_add₀ (uniformizer_ne_zero K), add_comm a n]
  · change uniformizer K ^ (-a) * (uniformizer K ^ (-n) * (u : K)⁻¹) =
      uniformizer K ^ (-(n+a)) * (u : K)⁻¹
    rw [← mul_assoc, ← zpow_add₀ (uniformizer_ne_zero K)]
    congr 2
    abel

/-- Opposite uniformizer exponents have exactly cancelling Haar Jacobians. -/
theorem reciprocalRescaling_measurePreserving (a : ℤ) :
    MeasurePreserving (reciprocalRescaling K a)
      ((normalizedHaar K).prod (normalizedHaar K))
      ((normalizedHaar K).prod (normalizedHaar K)) := by
  have h₁ : Measurable (uniformizerMul K a : K → K) := (uniformizerMul K a).continuous_toFun.measurable
  have h₂ : Measurable (uniformizerMul K (-a) : K → K) := (uniformizerMul K (-a)).continuous_toFun.measurable
  refine ⟨h₁.prodMap h₂, ?_⟩
  change ((normalizedHaar K).prod (normalizedHaar K)).map
    (Prod.map (uniformizerMul K a) (uniformizerMul K (-a))) = _
  rw [← Measure.map_prod_map _ _ h₁ h₂, uniformizerMul_map, uniformizerMul_map,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hq : (residueCard K : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_one.trans (residueCard_gt_one K)).ne'
  rw [← ENNReal.ofReal_mul (zpow_nonneg (Nat.cast_nonneg _) _),
    ← zpow_add₀ hq, add_neg_cancel, zpow_zero, ENNReal.ofReal_one, one_smul]

theorem shellFactor_uniformizerMul (a k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ) (x : K) :
    (ballSystem K).shellFactor k I w (uniformizerMul K a x) =
      (ballSystem K).shellFactor (k+a) I w x := by
  have hs (i : ℕ) : uniformizerMul K a x ∈ (ballSystem K).shell k i ↔
      x ∈ (ballSystem K).shell (k+a) i := by
    cases i with
    | zero => exact uniformizerMul_mem_ball K a k x
    | succ i =>
      change (uniformizerMul K a x ∈ ball K (k+(i+1:ℕ)) ∧
        uniformizerMul K a x ∉ ball K (k+(i:ℕ))) ↔
        (x ∈ ball K (k+a+(i+1:ℕ)) ∧ x ∉ ball K (k+a+(i:ℕ)))
      rw [uniformizerMul_mem_ball, uniformizerMul_mem_ball]
      congr 2 <;> abel
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Set.indicator, hs]

end UnitDistance.Local.ValuedHaar
