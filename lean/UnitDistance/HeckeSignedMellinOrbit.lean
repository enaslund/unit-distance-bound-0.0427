module

public import UnitDistance.HeckeSignedOddSupport
public import UnitDistance.HeckeSignedGammaIntegral

@[expose] public section
set_option backward.privateInPublic true


/-! Actual Mellin evaluation of one odd-norm unit orbit, with a free real
multiplier. Positive and negative parts therefore share the same Gamma mass. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Real Classical nonZeroDivisors NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- The shifted Gamma mass, before class and discriminant normalization. -/
def heckeSignedGammaMass (σ : ℝ) : ℝ≥0∞ :=
  (heckeJacobian K : ℝ≥0∞) * ENNReal.ofReal
    (∏ w : InfinitePlace K, Real.pi ^ (-((mult w : ℝ)*σ+heckeRealHalfShift K w)) *
      Real.Gamma ((mult w : ℝ)*σ+heckeRealHalfShift K w))

theorem heckeSignedGammaMass_ne_top (σ : ℝ) : heckeSignedGammaMass K σ ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top

theorem intNorm_cone_pos (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    0 < intNorm (idealSetMap K J a) := by
  have hn : 0 < |Algebra.norm ℚ (conePreimage K J a)| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr (conePreimage_ne_zero K J a))
  have hr : (0 : ℝ) < (intNorm (idealSetMap K J a) : ℝ) := by
    rw [← abs_norm_conePreimage]
    exact_mod_cast hn
  exact_mod_cast hr

theorem lintegral_heckeOddSignedTerm_cone (r : K) (hr : r^2=7)
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) (delta : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ u : logSpace K, ENNReal.ofReal
      (delta*heckeOddSignedTerm K t u (embeddingCoords K (conePreimage K J a)))) =
      ENNReal.ofReal (delta*chiFourReal (intNorm (idealSetMap K J a))) *
        ∫⁻ u : logSpace K, ENNReal.ofReal (heckeSignedTerm K
          ((intNorm (idealSetMap K J a) : ℝ)^2*t) u (embeddingCoords K 1)) := by
  have hn : (0:ℝ) < (intNorm (idealSetMap K J a) : ℝ)^2 := by
    exact sq_pos_of_pos (by exact_mod_cast intNorm_cone_pos K J a)
  have hpt (u : logSpace K) :
      ENNReal.ofReal (delta*heckeOddSignedTerm K t u (embeddingCoords K (conePreimage K J a))) =
        ENNReal.ofReal (delta*chiFourReal (intNorm (idealSetMap K J a))) *
          ENNReal.ofReal (heckeSignedTerm K ((intNorm (idealSetMap K J a) : ℝ)^2*t)
            (u+xShift K (conePreimage K J a)) (embeddingCoords K 1)) := by
    rw [heckeOddSignedTerm_cone_norm_scaled K r hr J a ht, ← mul_assoc]
    rw [mul_comm (delta*_), ENNReal.ofReal_mul
      (heckeSignedTerm_one_nonneg K (mul_pos hn ht) _), mul_comm]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact lintegral_add_right_eq_self
    (fun u : logSpace K => ENNReal.ofReal (heckeSignedTerm K
      ((intNorm (idealSetMap K J a) : ℝ)^2*t) u (embeddingCoords K 1))) _

/-- Literal positive/negative Mellin orbit evaluation. No sign, character,
unit-covariance or norm-scaling hypothesis remains. -/
theorem lintegral_mellin_heckeOddSignedTerm_cone (r : K) (hr : r^2=7)
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) (delta : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(σ-1)) *
      ∫⁻ u : logSpace K, ENNReal.ofReal
        (delta*heckeOddSignedTerm K t u (embeddingCoords K (conePreimage K J a)))) =
      ENNReal.ofReal (delta*chiFourReal (intNorm (idealSetMap K J a))) *
        ENNReal.ofReal (((intNorm (idealSetMap K J a) : ℝ)^2)^(-σ)) *
          heckeSignedGammaMass K σ := by
  have hn : (0:ℝ) < (intNorm (idealSetMap K J a) : ℝ)^2 := by
    exact sq_pos_of_pos (by exact_mod_cast intNorm_cone_pos K J a)
  have hpt (t : ℝ) (ht : t ∈ Set.Ioi (0:ℝ)) :
      ENNReal.ofReal (t^(σ-1)) *
        (∫⁻ u : logSpace K, ENNReal.ofReal
          (delta*heckeOddSignedTerm K t u (embeddingCoords K (conePreimage K J a)))) =
      ENNReal.ofReal (delta*chiFourReal (intNorm (idealSetMap K J a))) *
        (ENNReal.ofReal (t^(σ-1))*
          ∫⁻ u : logSpace K, ENNReal.ofReal (heckeSignedTerm K
            ((intNorm (idealSetMap K J a) : ℝ)^2*t) u (embeddingCoords K 1))) := by
    rw [lintegral_heckeOddSignedTerm_cone K r hr J a delta ht]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_Ioi_mellin_scale hn σ _
      (measurable_lintegral_heckeSignedTerm K (embeddingCoords K 1)).aemeasurable,
    lintegral_signedM0_eq K hσ]
  exact (mul_assoc _ _ _).symm

end UnitDistance.NumberFieldAnalysis
