module

public import UnitDistance.HeckeSignedSeries
public import UnitDistance.HeckeSignedIdealRegroup

@[expose] public section
set_option backward.privateInPublic true


/-! Cancellation of the character of an actual odd-norm ideal-class representative.
The principal-ideal bijection is literal multiplication by that representative. -/
noncomputable section
open NumberField DedekindResidue
open scoped Real Classical nonZeroDivisors NNReal ENNReal
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- The representative's character cancels because its norm is odd. -/
theorem tsum_principal_dvd_chiFour (J : (Ideal (𝓞 K))⁰)
    (hJ : Odd (Ideal.absNorm (J : Ideal (𝓞 K)))) (delta σ : ℝ) :
    (∑' I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
        ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))},
      ENNReal.ofReal ((delta*chiFourReal (Ideal.absNorm (J : Ideal (𝓞 K)))) *
        chiFourReal (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))) *
      ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))^2)^(-σ))) =
      ENNReal.ofReal (((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)^2)^(-σ)) *
        ∑' b : {b : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 b = (ClassGroup.mk0 J)⁻¹},
          ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))) *
            ENNReal.ofReal ((((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))^2)^(-σ)) := by
  rw [← Equiv.tsum_eq (principalDvdEquiv K J) (fun I =>
    ENNReal.ofReal ((delta*chiFourReal (Ideal.absNorm (J : Ideal (𝓞 K)))) *
      chiFourReal (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))) *
    ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))^2)^(-σ))),
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  have hN : Ideal.absNorm ((((principalDvdEquiv K J b) : (Ideal (𝓞 K))⁰)) : Ideal (𝓞 K)) =
      Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))*Ideal.absNorm (J : Ideal (𝓞 K)) := by
    change Ideal.absNorm (((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))*(J : Ideal (𝓞 K))) = _
    exact map_mul _ _ _
  rw [hN]
  have hchi : (delta*chiFourReal (Ideal.absNorm (J : Ideal (𝓞 K)))) *
      chiFourReal (Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))*
        Ideal.absNorm (J : Ideal (𝓞 K))) =
        delta*chiFourReal (Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) := by
    rw [chiFourReal_mul]
    calc
      _ = delta*chiFourReal (Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) *
        chiFourReal (Ideal.absNorm (J : Ideal (𝓞 K)))^2 := by ring
      _ = _ := by rw [chiFourReal_sq_of_odd hJ, mul_one]
  rw [hchi, Nat.cast_mul, mul_pow, Real.mul_rpow (by positivity) (by positivity),
    ENNReal.ofReal_mul (Real.rpow_nonneg (sq_nonneg
      (Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) (-σ))]
  ring

/-- Every subfamily of the actual positive character norm weights has finite mass. -/
theorem tsum_subtype_positive_chiFourIdealWeight_ne_top
    (P : (Ideal (𝓞 K))⁰ → Prop) (delta : ℝ) {σ : ℝ} (hσ : 1 < 2*σ) :
    (∑' I : {I : (Ideal (𝓞 K))⁰ // P I},
      ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))) *
        ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))^2)^(-σ))) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (tsum_positive_chiFourIdealWeight_ne_top K delta hσ)
  exact ENNReal.tsum_comp_le_tsum_of_injective
    (f := (Subtype.val : {I : (Ideal (𝓞 K))⁰ // P I} → (Ideal (𝓞 K))⁰))
    Subtype.val_injective
    (fun I : (Ideal (𝓞 K))⁰ =>
      ENNReal.ofReal (delta * chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K)))) *
        ENNReal.ofReal ((((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ)))

end UnitDistance.NumberFieldAnalysis
