module

public import UnitDistance.HeckeSignedScaling

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual unit-orbit unfolding for signed Hecke kernels

The generic lower-integral unfolding adapts Chris Birkbeck's 2026 AINTLIB
MellinAgreement argument (Apache-2.0, commit a302aeacd86053f9d5f991fbbf664e1cc1051d08).
It retains the actual ideal lattice, Dirichlet unit basis and cone bijection.
The kernel is allowed to be any nonnegative measurable unit-covariant weight.
-/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding.fundamentalCone
open scoped BigOperators Real Classical nonZeroDivisors NNReal ENNReal
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- Tonelli unfolding applies separately to absolute, positive and negative
parts of a signed kernel. All orbit and box data are the actual arithmetic ones. -/
theorem lintegral_box_unit_covariant (J : (Ideal (𝓞 K))⁰)
    (f : logSpace K → EuclideanSpace ℝ (index K) → ℝ≥0∞)
    (hf : ∀ x, AEMeasurable (fun u => f u x)
      (volume.restrict (ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ))))
    (hunit : ∀ (u : logSpace K) (epsilon : (𝓞 K)ˣ) (y : K),
      f u (embeddingCoords K (algebraMap (𝓞 K) K (epsilon : 𝓞 K)*y)) =
      f (u+logEmbedding K (Additive.ofMul epsilon)) (embeddingCoords K y)) :
    (∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
      ∑' v : idealZLattice K (FractionalIdeal.mk0 K J),
        if v = 0 then 0 else f u (v : EuclideanSpace ℝ (index K))) =
      ∑' a : idealSet K J, ∫⁻ u : logSpace K,
        f u (embeddingCoords K (conePreimage K J a)) := by
  let G : EuclideanSpace ℝ (index K) → ℝ≥0∞ := fun x =>
    ∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ), f u x
  have hG : G = fun x =>
    ∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ), f u x := rfl
  -- Tonelli, followed by the actual unit-orbit bijection.
  rw [lintegral_tsum (fun v => ?_)]
  swap
  · by_cases hv : v = 0
    · simp only [if_pos hv]
      exact aemeasurable_const
    · simp only [if_neg hv]
      exact hf _
  -- Step 3: the per-v box integral is `ite (v = 0) 0 (G ↑v)`
  have hstep3 : ∀ v : idealZLattice K (FractionalIdeal.mk0 K J),
      (∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
        if v = 0 then 0
        else f u (v : EuclideanSpace ℝ (index K)))
        = if v = 0 then 0 else G (v : EuclideanSpace ℝ (index K)) := by
    intro v
    by_cases hv : v = 0
    · rw [if_pos hv]
      rw [setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _)
        (fun u _ => if_pos hv), lintegral_zero]
    · rw [if_neg hv, hG]
      exact setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _)
        (fun u _ => if_neg hv)
  rw [tsum_congr hstep3]
  -- Step 4: cone reindex (on the G-valued family)
  rw [tsum_ite_eq_tsum_coneUnfold_ennreal K J G]
  -- Step 5+6: per-point shift, then split the product sum
  rw [ENNReal.tsum_prod']
  refine tsum_congr (fun a => ?_)
  have hstep5 : ∀ n : Fin (rank K) → ℤ,
      G ((euclidMixedEquiv K).symm
        ((∏ j, fundSystem K j ^ (n j)) • ((a : mixedSpace K))))
        = ∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
            f (u + logEmbedding K
              (Additive.ofMul (∏ j, fundSystem K j ^ (n j))))
              (embeddingCoords K (conePreimage K J a)) := by
    intro n
    rw [hG]
    refine setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _)
      (fun u _ => ?_)
    rw [← mixedEmbedding_conePreimage K J a]
    rw [unitSMul_smul, ← map_mul, euclidMixedEquiv_symm_mixedEmbedding]
    exact hunit _ _ _
  rw [tsum_congr hstep5]
  -- Step 7: re-tile to the whole log-space
  rw [lintegral_eq_tsum_box_shift K (fun u =>
    f u (embeddingCoords K (conePreimage K J a)))]

end UnitDistance.NumberFieldAnalysis
