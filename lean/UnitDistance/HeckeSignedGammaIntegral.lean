module

public import UnitDistance.HeckeSignedWeights

@[expose] public section
set_option backward.privateInPublic true


/-!
# Shifted archimedean integral of the signed Hecke kernel

The Mellin integral of each odd real-place factor shifts the corresponding
Gamma argument by one half. The change-of-variables proof follows the
ordinary Gaussian computation in AINTLIB's `MellinAgreement.lean` (Chris
Birkbeck, Apache-2.0, pin and license in `third-party/aintlib`).
-/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Real Classical ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis

variable (K : Type*) [Field K] [NumberField K]

/-- Any positive vector of place exponents has the product Gamma integral under the
actual Hecke logarithmic change of coordinates. -/
theorem lintegral_heckeLog_gamma_product (a : InfinitePlace K → ℝ) (ha : ∀ w, 0 < a w) :
    ∫⁻ p : ℝ × logSpace K, ENNReal.ofReal (Real.exp
      ((∑ w : InfinitePlace K, a w * (heckeLogCLE K p) w)
        - Real.pi * ∑ w : InfinitePlace K, Real.exp ((heckeLogCLE K p) w))) =
      (heckeJacobian K : ℝ≥0∞) * ENNReal.ofReal
        (∏ w : InfinitePlace K, Real.pi ^ (-(a w)) * Real.Gamma (a w)) := by
  let G : (InfinitePlace K → ℝ) → ℝ≥0∞ := fun l =>
    ENNReal.ofReal (∏ w : InfinitePlace K, Real.exp (a w * l w - Real.pi * Real.exp (l w)))
  have hpt (p : ℝ × logSpace K) :
      ENNReal.ofReal (Real.exp ((∑ w : InfinitePlace K, a w * (heckeLogCLE K p) w)
        - Real.pi * ∑ w : InfinitePlace K, Real.exp ((heckeLogCLE K p) w))) =
        G (heckeLogCLE K p) := by
    unfold G
    rw [← Real.exp_sum]
    congr 2
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp_rw [hpt]
  have hGmeas : Measurable G := by
    unfold G
    refine ENNReal.measurable_ofReal.comp ?_
    refine Finset.measurable_prod _ (fun w _ => ?_)
    exact Real.measurable_exp.comp (((measurable_pi_apply w).const_mul _).sub
      ((Real.measurable_exp.comp (measurable_pi_apply w)).const_mul _))
  rw [← lintegral_map hGmeas (heckeLogCLE K).continuous.measurable,
    map_heckeLogCLE_volume, lintegral_smul_measure]
  change (heckeJacobian K : ℝ≥0∞) * ∫⁻ l, G l = _
  congr 1
  have hint (w : InfinitePlace K) :
      Integrable (fun l : ℝ => Real.exp (a w * l - Real.pi * Real.exp l)) :=
    integrable_exp_mul_sub_pi_exp (ha w)
  have hprod_int : Integrable (fun l : InfinitePlace K → ℝ =>
      ∏ w : InfinitePlace K, Real.exp (a w * l w - Real.pi * Real.exp (l w))) :=
    MeasureTheory.Integrable.fintype_prod (f := fun w x =>
      Real.exp (a w * x - Real.pi * Real.exp x)) hint
  unfold G
  rw [← ofReal_integral_eq_lintegral_ofReal hprod_int
    (Filter.Eventually.of_forall (fun l => Finset.prod_nonneg
      (fun w _ => (Real.exp_pos _).le)))]
  congr 1
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod (f := fun w x =>
    Real.exp (a w * x - Real.pi * Real.exp x))]
  exact Finset.prod_congr rfl (fun w _ => integral_exp_mul_sub_pi_exp (ha w))

/-- Real places contribute the extra half exponent from the normalized odd kernel. -/
def heckeRealHalfShift (w : InfinitePlace K) : ℝ := if IsReal w then 1/2 else 0

omit [NumberField K] in
theorem heckeRealHalfShift_nonneg (w : InfinitePlace K) : 0 ≤ heckeRealHalfShift K w := by
  unfold heckeRealHalfShift
  split_ifs <;> norm_num

theorem heckeSignedAmplitude_exp_one (τ : ℝ) (u : logSpace K) :
    heckeSignedAmplitude K (heckeWeights K (Real.exp τ) u) (embeddingCoords K 1) =
      Real.exp (∑ w : InfinitePlace K, heckeRealHalfShift K w * (heckeLogCLE K (τ, u)) w) := by
  rw [heckeSignedAmplitude_embedding]
  simp only [map_one, mul_one]
  simp_rw [heckeWeights_exp, Real.sqrt_eq_rpow, ← Real.exp_mul]
  rw [← Real.exp_sum]
  congr 1
  rw [← Fintype.sum_subtype_add_sum_subtype IsReal
    (fun w : InfinitePlace K => heckeRealHalfShift K w * (heckeLogCLE K (τ, u)) w)]
  have hr (w : {w : InfinitePlace K // IsReal w}) : heckeRealHalfShift K w = 1/2 := by
    simp only [heckeRealHalfShift, if_pos w.property]
  have hc (w : {w : InfinitePlace K // ¬IsReal w}) : heckeRealHalfShift K w = 0 := by
    simp only [heckeRealHalfShift, if_neg w.property]
  simp_rw [hr, hc]
  simp [mul_comm]

theorem heckeSignedTerm_exp_one (τ : ℝ) (u : logSpace K) :
    heckeSignedTerm K (Real.exp τ) u (embeddingCoords K 1) =
      Real.exp ((∑ w : InfinitePlace K, heckeRealHalfShift K w * (heckeLogCLE K (τ, u)) w)
        - Real.pi * ∑ w : InfinitePlace K, Real.exp ((heckeLogCLE K (τ, u)) w)) := by
  rw [heckeSignedTerm, heckeSignedAmplitude_exp_one, gaussTerm_exp_eq, ← Real.exp_add]
  congr 1
  ring

/-- The signed Gaussian at the unit element is positive on the positive ray. -/
theorem heckeSignedTerm_one_pos {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    0 < heckeSignedTerm K t u (embeddingCoords K 1) := by
  rw [← Real.exp_log ht, heckeSignedTerm_exp_one]
  exact Real.exp_pos _

/-- Shifted universal Mellin constant for the actual signed Gaussian. -/
theorem lintegral_signedM0_eq {σ : ℝ} (hσ : 0 < σ) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (σ - 1)) *
      ∫⁻ u : logSpace K, ENNReal.ofReal (heckeSignedTerm K t u (embeddingCoords K 1))) =
      (heckeJacobian K : ℝ≥0∞) * ENNReal.ofReal (∏ w : InfinitePlace K,
        Real.pi ^ (-((mult w : ℝ) * σ + heckeRealHalfShift K w)) *
          Real.Gamma ((mult w : ℝ) * σ + heckeRealHalfShift K w)) := by
  have himg := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ)
    MeasurableSet.univ (f := Real.exp) (f' := Real.exp)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t => ENNReal.ofReal (t ^ (σ - 1)) *
      ∫⁻ u : logSpace K, ENNReal.ofReal (heckeSignedTerm K t u (embeddingCoords K 1)))
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at himg
  rw [himg]
  have hexponent (p : ℝ × logSpace K) :
      σ * p.1 + ∑ w : InfinitePlace K, heckeRealHalfShift K w * (heckeLogCLE K p) w =
      ∑ w : InfinitePlace K, ((mult w : ℝ) * σ + heckeRealHalfShift K w) *
        (heckeLogCLE K p) w := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, ← sum_mult_heckeLogCLE K p, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun w _ => by ring)
  have hstep (τ : ℝ) :
      ENNReal.ofReal (|Real.exp τ|) * (ENNReal.ofReal ((Real.exp τ) ^ (σ - 1)) *
        ∫⁻ u : logSpace K, ENNReal.ofReal
          (heckeSignedTerm K (Real.exp τ) u (embeddingCoords K 1))) =
        ∫⁻ u : logSpace K, ENNReal.ofReal (Real.exp
          ((∑ w : InfinitePlace K, ((mult w : ℝ) * σ + heckeRealHalfShift K w) *
            (heckeLogCLE K (τ, u)) w)
            - Real.pi * ∑ w : InfinitePlace K, Real.exp ((heckeLogCLE K (τ, u)) w))) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (Real.exp_pos _)]
    have hscal : Real.exp τ * (Real.exp τ) ^ (σ - 1) = Real.exp (σ * τ) := by
      rw [show (Real.exp τ) ^ (σ - 1) = Real.exp (τ * (σ - 1)) from (Real.exp_mul τ _).symm,
        ← Real.exp_add]
      congr 1
      ring
    rw [hscal, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun u => ?_)
    rw [heckeSignedTerm_exp_one, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    rw [← hexponent (τ, u)]
    dsimp only []
    ring
  rw [lintegral_congr hstep]
  let a : InfinitePlace K → ℝ := fun w => (mult w : ℝ) * σ + heckeRealHalfShift K w
  have hmeas : Measurable (fun p : ℝ × logSpace K => ENNReal.ofReal (Real.exp
      ((∑ w : InfinitePlace K, a w * (heckeLogCLE K p) w)
        - Real.pi * ∑ w : InfinitePlace K, Real.exp ((heckeLogCLE K p) w)))) := by
    refine (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp ?_)).measurable
    refine (continuous_finsetSum _ (fun w _ =>
      (((continuous_apply w).comp (heckeLogCLE K).continuous).const_mul _))).sub ?_
    exact (continuous_finsetSum _ (fun w _ => Real.continuous_exp.comp
      ((continuous_apply w).comp (heckeLogCLE K).continuous))).const_mul _
  rw [← lintegral_prod _ hmeas.aemeasurable]
  apply lintegral_heckeLog_gamma_product K a
  intro w
  have hm : (0 : ℝ) < mult w := by exact_mod_cast mult_pos (w := w)
  exact add_pos_of_pos_of_nonneg (mul_pos hm hσ) (heckeRealHalfShift_nonneg K w)

end UnitDistance.NumberFieldAnalysis
