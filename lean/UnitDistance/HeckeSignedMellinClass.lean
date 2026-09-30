module

public import UnitDistance.HeckeSignedMellinFinite

@[expose] public section
set_option backward.privateInPublic true


/-! Class normalization of the signed Mellin integral. A literal odd integral
representative supplies both the radial norm scale and its cancelling character. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Real Classical nonZeroDivisors NNReal ENNReal
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- Actual radial normalization of one integral ideal representative. -/
def heckeOddClassScale (J : (Ideal (𝓞 K))⁰) : ℝ :=
  ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)^2)⁻¹*heckeBeta K

theorem heckeOddClassScale_pos (J : (Ideal (𝓞 K))⁰) : 0 < heckeOddClassScale K J := by
  have hN : (0:ℝ) < Ideal.absNorm (J : Ideal (𝓞 K)) :=
    Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors J)
  have hB := heckeBeta_pos K
  unfold heckeOddClassScale
  positivity

/-- Positive/negative mass for the normalized class contribution. -/
def heckeOddSignedClassMass (J : (Ideal (𝓞 K))⁰) (delta t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((torsionOrder K : ℝ)⁻¹) *
    heckeOddSignedLatticeMass K J (delta*chiFourReal (Ideal.absNorm (J : Ideal (𝓞 K))))
      (heckeOddClassScale K J*t)

/-- The norm, torsion and representative character cancel exactly. -/
theorem lintegral_mellin_heckeOddSignedClassMass (r : K) (hr : r^2=7)
    (J : (Ideal (𝓞 K))⁰) (hJ : Odd (Ideal.absNorm (J : Ideal (𝓞 K))))
    (delta : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedClassMass K J delta t) =
      ENNReal.ofReal ((heckeBeta K)^(-σ))*heckeSignedGammaMass K σ *
        ∑' b : {b : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 b = (ClassGroup.mk0 J)⁻¹},
          ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))) *
            ENNReal.ofReal ((((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))^2)^(-σ)) := by
  have hshape (t : ℝ) :
      ENNReal.ofReal (t^(σ-1))*heckeOddSignedClassMass K J delta t =
        ENNReal.ofReal ((torsionOrder K : ℝ)⁻¹) * (ENNReal.ofReal (t^(σ-1))*
          heckeOddSignedLatticeMass K J (delta*chiFourReal (Ideal.absNorm (J : Ideal (𝓞 K))))
            (heckeOddClassScale K J*t)) := by
    unfold heckeOddSignedClassMass
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi (fun t _ => hshape t),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_Ioi_mellin_scale (heckeOddClassScale_pos K J) σ _
      (measurable_heckeOddSignedLatticeMass K J _).aemeasurable,
    lintegral_mellin_heckeOddSignedLatticeMass K r hr J _ hσ,
    tsum_principal_dvd_chiFour K J hJ delta σ]
  have hN : (0:ℝ) < (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)^2 :=
    sq_pos_of_pos (Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors J))
  have hscale : (heckeOddClassScale K J)^(-σ) =
      ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)^2)^σ * (heckeBeta K)^(-σ) := by
    rw [heckeOddClassScale, Real.mul_rpow (by positivity) (heckeBeta_pos K).le,
      Real.inv_rpow hN.le, ← Real.rpow_neg hN.le, neg_neg]
  have hwcancel : ENNReal.ofReal ((torsionOrder K : ℝ)⁻¹)*(torsionOrder K : ℝ≥0∞) = 1 := by
    rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr (torsionOrder_pos K)), ENNReal.ofReal_natCast]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast (torsionOrder_pos K).ne') (ENNReal.natCast_ne_top _)
  have hnCancel : ENNReal.ofReal (((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)^2)^σ) *
      ENNReal.ofReal (((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)^2)^(-σ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]
    simp
  rw [hscale, ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _)]
  calc
    _ = (ENNReal.ofReal ((torsionOrder K : ℝ)⁻¹)*(torsionOrder K : ℝ≥0∞)) *
      (ENNReal.ofReal (((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)^2)^σ) *
        ENNReal.ofReal (((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)^2)^(-σ))) *
      (ENNReal.ofReal ((heckeBeta K)^(-σ))*heckeSignedGammaMass K σ *
        ∑' b : {b : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 b = (ClassGroup.mk0 J)⁻¹},
          ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))) *
            ENNReal.ofReal ((((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))^2)^(-σ))) := by ring
    _ = _ := by rw [hwcancel, hnCancel, one_mul, one_mul]

end UnitDistance.NumberFieldAnalysis
