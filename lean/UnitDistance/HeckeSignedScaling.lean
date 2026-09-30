module

public import UnitDistance.HeckeSignedWeights

@[expose] public section
set_option backward.privateInPublic true


/-! Scaling of the literal signed Gaussian under multiplication by a nonzero
number-field element. The unsigned Gaussian change of variables follows the
Hecke coordinates of Chris Birkbeck's AINTLIB (Apache-2.0, 2026); the signed
amplitude and its norm-character factor are proved here. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Real Classical
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- The signed term is jointly continuous, including the zero radial value. -/
theorem continuous_heckeSignedTerm (x : EuclideanSpace ℝ (index K)) :
    Continuous (fun q : ℝ × logSpace K => heckeSignedTerm K q.1 q.2 x) := by
  have hw : ∀ w : InfinitePlace K,
      Continuous (fun q : ℝ × logSpace K => heckeWeights K q.1 q.2 w) := by
    intro w
    unfold heckeWeights
    exact ((Real.continuous_rpow_const (by positivity : 0 ≤ (1:ℝ)/(Module.finrank ℚ K))).comp
      continuous_fst).mul (Real.continuous_exp.comp
        (((continuous_fullLog K w).comp continuous_snd).const_mul 2 |>.div_const _))
  unfold heckeSignedTerm heckeSignedAmplitude gaussTerm
  apply Continuous.mul
  · exact continuous_finsetProd _ (fun w _ => (Real.continuous_sqrt.comp (hw w.1)).mul continuous_const)
  · apply Real.continuous_exp.comp
    apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro i _
    apply Continuous.mul _ continuous_const
    rcases i with w | ⟨w,j⟩ <;> exact hw _

theorem measurable_lintegral_heckeSignedTerm (x : EuclideanSpace ℝ (index K)) :
    Measurable (fun t : ℝ => ∫⁻ u : logSpace K, ENNReal.ofReal (heckeSignedTerm K t u x)) :=
  (ENNReal.continuous_ofReal.comp (continuous_heckeSignedTerm K x)).measurable.lintegral_prod_right'

theorem measurable_lintegral_abs_heckeSignedTerm (x : EuclideanSpace ℝ (index K)) :
    Measurable (fun t : ℝ => ∫⁻ u : logSpace K, ENNReal.ofReal |heckeSignedTerm K t u x|) :=
  (ENNReal.continuous_ofReal.comp (continuous_heckeSignedTerm K x).abs).measurable.lintegral_prod_right'

theorem heckeSignedAmplitude_norm_scaled {y : K} (hy : y ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) (u : logSpace K) :
    heckeSignedAmplitude K (heckeWeights K t u) (embeddingCoords K y) =
      signedArchCharacter K y * heckeSignedAmplitude K
        (heckeWeights K (((|Algebra.norm ℚ y| : ℚ) : ℝ)^2*t) (u+xShift K y))
        (embeddingCoords K 1) := by
  rw [heckeSignedAmplitude_embedding, heckeSignedAmplitude_embedding,
    signedArchCharacter, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro w _
  rw [map_one, mul_one, ← sq_mul_heckeWeights K hy ht]
  have habs : w.1 y = |embedding_of_isReal w.2 y| := by
    rw [← norm_embedding_of_isReal w.2, Real.norm_eq_abs]
  rw [habs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_abs]
  rw [← mul_assoc, sign_mul_abs]
  ring

theorem gaussTerm_norm_scaled {y : K} (hy : y ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) (u : logSpace K) :
    gaussTerm K t u (embeddingCoords K y) =
      gaussTerm K (((|Algebra.norm ℚ y| : ℚ) : ℝ)^2*t) (u+xShift K y)
        (embeddingCoords K 1) := by
  rw [gaussTerm, gaussTerm]
  refine congrArg (fun r => Real.exp (-π*r)) ?_
  rw [sum_placeWeights_embeddingCoords_sq, sum_placeWeights_embeddingCoords_sq]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_one, one_pow, mul_one, ← sq_mul_heckeWeights K hy ht]
  ring

theorem heckeSignedTerm_norm_scaled {y : K} (hy : y ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) (u : logSpace K) :
    heckeSignedTerm K t u (embeddingCoords K y) =
      signedArchCharacter K y * heckeSignedTerm K
        (((|Algebra.norm ℚ y| : ℚ) : ℝ)^2*t) (u+xShift K y) (embeddingCoords K 1) := by
  unfold heckeSignedTerm
  rw [heckeSignedAmplitude_norm_scaled K hy ht, gaussTerm_norm_scaled K hy ht, mul_assoc]

theorem heckeSignedTerm_one_nonneg {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    0 ≤ heckeSignedTerm K t u (embeddingCoords K 1) := by
  unfold heckeSignedTerm
  apply mul_nonneg
  · rw [heckeSignedAmplitude_embedding]
    apply Finset.prod_nonneg
    intro w _
    simp only [map_one, mul_one]
    exact Real.sqrt_nonneg _
  · exact (gaussTerm_pos K t u _).le

theorem abs_signedArchCharacter {y : K} (hy : y ≠ 0) :
    |signedArchCharacter K y| = 1 := by
  rw [signedArchCharacter_eq_sign_norm K hy]
  have hn : Algebra.norm ℚ y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  rcases lt_or_gt_of_ne hn with hn | hn
  · rw [sign_neg hn]
    norm_num
  · rw [sign_pos hn]
    norm_num

theorem abs_heckeSignedTerm_norm_scaled {y : K} (hy : y ≠ 0)
    {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    |heckeSignedTerm K t u (embeddingCoords K y)| =
      heckeSignedTerm K (((|Algebra.norm ℚ y| : ℚ) : ℝ)^2*t)
        (u+xShift K y) (embeddingCoords K 1) := by
  rw [heckeSignedTerm_norm_scaled K hy ht.le, abs_mul, abs_signedArchCharacter K hy, one_mul]
  apply abs_of_nonneg
  apply heckeSignedTerm_one_nonneg
  apply mul_pos _ ht
  exact sq_pos_of_ne_zero (by exact_mod_cast (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hy)))

theorem lintegral_abs_heckeSignedTerm_eq_norm_scaled {y : K} (hy : y ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ u : logSpace K, ENNReal.ofReal |heckeSignedTerm K t u (embeddingCoords K y)| =
      ∫⁻ u : logSpace K, ENNReal.ofReal (heckeSignedTerm K
        (((|Algebra.norm ℚ y| : ℚ) : ℝ)^2*t) u (embeddingCoords K 1)) := by
  simp_rw [abs_heckeSignedTerm_norm_scaled K hy ht]
  exact lintegral_add_right_eq_self
    (fun u : logSpace K => ENNReal.ofReal (heckeSignedTerm K
      (((|Algebra.norm ℚ y| : ℚ) : ℝ)^2*t) u (embeddingCoords K 1))) (xShift K y)

end UnitDistance.NumberFieldAnalysis
