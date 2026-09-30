module

public import UnitDistance.HeckeSignedMellinOrbit
public import UnitDistance.HeckeSignedUnfolding
public import UnitDistance.HeckeSignedIdealRegroup

@[expose] public section
set_option backward.privateInPublic true


/-! Exact lower Mellin integrals of the positive and negative signed lattice
parts. Arithmetic unit orbits are fully unfolded into ordinary principal ideals. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Real Classical nonZeroDivisors NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- Nonnegative mass of one chosen sign of the actual odd-norm theta series. -/
def heckeOddSignedLatticeMass (J : (Ideal (𝓞 K))⁰) (delta t : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
    ∑' v : idealZLattice K (FractionalIdeal.mk0 K J),
      ENNReal.ofReal (delta*heckeOddSignedTerm K t u (v : EuclideanSpace ℝ (index K)))

theorem heckeOddSignedLatticeMass_eq_cone (r : K) (hr : r^2=7)
    (J : (Ideal (𝓞 K))⁰) (delta t : ℝ) :
    heckeOddSignedLatticeMass K J delta t =
      ∑' a : idealSet K J, ∫⁻ u : logSpace K,
        ENNReal.ofReal (delta*heckeOddSignedTerm K t u
          (embeddingCoords K (conePreimage K J a))) := by
  let f : logSpace K → EuclideanSpace ℝ (index K) → ℝ≥0∞ :=
    fun u x => ENNReal.ofReal (delta*heckeOddSignedTerm K t u x)
  have hzero (u : logSpace K) : f u 0 = 0 := by simp [f]
  have hite (u : logSpace K) (v : idealZLattice K (FractionalIdeal.mk0 K J)) :
      (if v = 0 then 0 else f u v) = f u v := by
    split_ifs with hv
    · subst v
      exact (hzero u).symm
    · rfl
  have h := lintegral_box_unit_covariant K J f (fun x => ?_) (fun u epsilon y => ?_)
  · simpa only [hite, f, heckeOddSignedLatticeMass] using h
  · exact (ENNReal.continuous_ofReal.comp (((continuous_heckeOddSignedTerm K x).comp
      (continuous_const.prodMk continuous_id)).const_mul delta)).aemeasurable
  · dsimp [f]
    rw [heckeOddSignedTerm_unit_mul K r hr]

/-- Exact positive/negative Mellin mass over the actual principal ideals.
The multiplier `delta` may select either sign or scale it by a class character. -/
theorem lintegral_mellin_heckeOddSignedLatticeMass (r : K) (hr : r^2=7)
    (J : (Ideal (𝓞 K))⁰) (delta : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(σ-1)) *
      heckeOddSignedLatticeMass K J delta t) =
      heckeSignedGammaMass K σ * (torsionOrder K) *
        ∑' I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
          ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))},
          ENNReal.ofReal (delta*chiFourReal (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))) *
            ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))^2)^(-σ)) := by
  have hm (x : EuclideanSpace ℝ (index K)) : Measurable
      (fun t : ℝ => ∫⁻ u : logSpace K, ENNReal.ofReal (delta*heckeOddSignedTerm K t u x)) :=
    (ENNReal.continuous_ofReal.comp ((continuous_heckeOddSignedTerm K x).const_mul delta)).measurable.lintegral_prod_right'
  have hp : AEMeasurable (fun t : ℝ => ENNReal.ofReal (t^(σ-1)))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply (ENNReal.continuous_ofReal.comp_continuousOn (show ContinuousOn
      (fun t : ℝ => t^(σ-1)) (Set.Ioi (0:ℝ)) from ?_)).aemeasurable measurableSet_Ioi
    exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx))).continuousWithinAt
  have hshape : ∀ t : ℝ, ENNReal.ofReal (t^(σ-1))*heckeOddSignedLatticeMass K J delta t =
      ∑' a : idealSet K J, ENNReal.ofReal (t^(σ-1))*
        ∫⁻ u : logSpace K, ENNReal.ofReal
          (delta*heckeOddSignedTerm K t u (embeddingCoords K (conePreimage K J a))) := by
    intro t
    rw [heckeOddSignedLatticeMass_eq_cone K r hr, ← ENNReal.tsum_mul_left]
  rw [setLIntegral_congr_fun measurableSet_Ioi (fun t _ => hshape t)]
  rw [lintegral_tsum (f := fun (a : idealSet K J) (t : ℝ) =>
    ENNReal.ofReal (t^(σ-1)) * ∫⁻ u : logSpace K, ENNReal.ofReal
      (delta*heckeOddSignedTerm K t u (embeddingCoords K (conePreimage K J a))))
    (fun a => hp.mul (hm _).aemeasurable)]
  simp_rw [lintegral_mellin_heckeOddSignedTerm_cone K r hr J _ delta hσ]
  rw [ENNReal.tsum_mul_right, tsum_idealSet_norm_weight K J
    (fun n => ENNReal.ofReal (delta*chiFourReal n)*ENNReal.ofReal (((n:ℝ)^2)^(-σ)))]
  ring

end UnitDistance.NumberFieldAnalysis
