module

public import UnitDistance.HeckeSignedMellinClass
public import UnitDistance.ClassGroupCoprime

@[expose] public section
set_option backward.privateInPublic true


/-! Actual odd ideal-class representatives and the complete character-weighted
Mellin mass. No existence or oddness of class representatives is assumed. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Real Classical nonZeroDivisors NNReal ENNReal
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- An actual odd representative of the inverse class; principal division then
lands in the class itself. -/
def heckeOddClassRep (C : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  (UnitDistance.ClassGroupCoprime.exists_odd_norm_rep K C⁻¹).choose

theorem heckeOddClassRep_class (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk0 (heckeOddClassRep K C) = C⁻¹ :=
  (UnitDistance.ClassGroupCoprime.exists_odd_norm_rep K C⁻¹).choose_spec.1

theorem heckeOddClassRep_odd (C : ClassGroup (𝓞 K)) :
    Odd (Ideal.absNorm (heckeOddClassRep K C : Ideal (𝓞 K))) :=
  (UnitDistance.ClassGroupCoprime.exists_odd_norm_rep K C⁻¹).choose_spec.2

theorem measurable_heckeOddSignedClassMass (J : (Ideal (𝓞 K))⁰) (delta : ℝ) :
    Measurable (heckeOddSignedClassMass K J delta) := by
  apply Measurable.const_mul
  exact (measurable_heckeOddSignedLatticeMass K J _).comp (measurable_const_mul _)

/-- The sum of the positive (or negative) component masses of all actual classes. -/
def heckeOddSignedTotalMass (delta t : ℝ) : ℝ≥0∞ :=
  ∑ C : ClassGroup (𝓞 K), heckeOddSignedClassMass K (heckeOddClassRep K C) delta t

/-- Exact full ideal-norm character mass after summing all actual classes. -/
theorem lintegral_mellin_heckeOddSignedTotalMass (r : K) (hr : r^2=7)
    (delta : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedTotalMass K delta t) =
      ENNReal.ofReal ((heckeBeta K)^(-σ))*heckeSignedGammaMass K σ *
        ∑' I : (Ideal (𝓞 K))⁰,
          ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K)))) *
            ENNReal.ofReal (((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^2)^(-σ)) := by
  have hp : AEMeasurable (fun t : ℝ => ENNReal.ofReal (t^(σ-1)))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply (ENNReal.continuous_ofReal.comp_continuousOn (show ContinuousOn
      (fun t : ℝ => t^(σ-1)) (Set.Ioi (0:ℝ)) from ?_)).aemeasurable measurableSet_Ioi
    exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx))).continuousWithinAt
  simp_rw [heckeOddSignedTotalMass, Finset.mul_sum]
  rw [lintegral_finsetSum' (f := fun (C : ClassGroup (𝓞 K)) (t : ℝ) =>
    ENNReal.ofReal (t^(σ-1))*heckeOddSignedClassMass K (heckeOddClassRep K C) delta t)
    _ (fun C _ => hp.mul (measurable_heckeOddSignedClassMass K _ delta).aemeasurable)]
  have hC (C : ClassGroup (𝓞 K)) :
      (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(σ-1))*
        heckeOddSignedClassMass K (heckeOddClassRep K C) delta t) =
      ENNReal.ofReal ((heckeBeta K)^(-σ))*heckeSignedGammaMass K σ *
        ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C},
          ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))) *
            ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))^2)^(-σ)) := by
    rw [lintegral_mellin_heckeOddSignedClassMass K r hr (heckeOddClassRep K C)
      (heckeOddClassRep_odd K C) delta hσ]
    congr 1
    have hpred (I : (Ideal (𝓞 K))⁰) :
        (ClassGroup.mk0 I = (ClassGroup.mk0 (heckeOddClassRep K C))⁻¹) ↔
          (ClassGroup.mk0 I = C) := by rw [heckeOddClassRep_class, inv_inv]
    exact Equiv.tsum_eq (Equiv.subtypeEquivRight hpred)
      (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} =>
        ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))) *
          ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))^2)^(-σ)))
  rw [Finset.sum_congr rfl (fun C _ => hC C), ← Finset.mul_sum]
  congr 1
  have hfiber : (∑' C : ClassGroup (𝓞 K),
      ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C},
        ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))) *
          ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))^2)^(-σ))) =
        ∑' I : (Ideal (𝓞 K))⁰,
          ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K)))) *
            ENNReal.ofReal (((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^2)^(-σ)) := by
    rw [← ENNReal.tsum_sigma' (f := fun p : Σ C : ClassGroup (𝓞 K),
        {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} =>
      ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm ((p.2 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))) *
        ENNReal.ofReal ((((Ideal.absNorm ((p.2 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))^2)^(-σ)))]
    exact Equiv.tsum_eq (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I))
      (fun I : (Ideal (𝓞 K))⁰ => ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm (I : Ideal (𝓞 K)))) *
        ENNReal.ofReal (((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)^2)^(-σ)))
  simpa only [tsum_fintype] using hfiber

/-- The full signed component masses are finite on the classical convergence half-plane. -/
theorem lintegral_mellin_heckeOddSignedTotalMass_ne_top (r : K) (hr : r^2=7)
    (delta : ℝ) {σ : ℝ} (hσ : 1 < 2*σ) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedTotalMass K delta t) ≠ ⊤ := by
  rw [lintegral_mellin_heckeOddSignedTotalMass K r hr delta (by linarith)]
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (heckeSignedGammaMass_ne_top K σ))
    (tsum_positive_chiFourIdealWeight_ne_top K delta hσ)

end UnitDistance.NumberFieldAnalysis
