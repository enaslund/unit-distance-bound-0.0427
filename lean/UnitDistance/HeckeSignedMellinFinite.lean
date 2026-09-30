module

public import UnitDistance.HeckeSignedMellinLattice
public import UnitDistance.HeckeSignedClassRegroup

@[expose] public section
set_option backward.privateInPublic true


/-! Finiteness and measurability of the actual signed Mellin masses. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Real Classical nonZeroDivisors NNReal ENNReal
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

theorem measurable_heckeOddSignedLatticeMass (J : (Ideal (𝓞 K))⁰) (delta : ℝ) :
    Measurable (heckeOddSignedLatticeMass K J delta) := by
  have hf : Measurable (fun q : ℝ × logSpace K =>
      ∑' v : idealZLattice K (FractionalIdeal.mk0 K J),
        ENNReal.ofReal (delta*heckeOddSignedTerm K q.1 q.2 (v : EuclideanSpace ℝ (index K)))) := by
    apply Measurable.tsum
    intro v
    exact (ENNReal.continuous_ofReal.comp ((continuous_heckeOddSignedTerm K v).const_mul delta)).measurable
  exact hf.lintegral_prod_right'

/-- All signed parts of the actual lattice Mellin mass are finite on 2σ>1. -/
theorem lintegral_mellin_heckeOddSignedLatticeMass_ne_top (r : K) (hr : r^2=7)
    (J : (Ideal (𝓞 K))⁰) (delta : ℝ) {σ : ℝ} (hσ : 1 < 2*σ) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(σ-1)) *
      heckeOddSignedLatticeMass K J delta t) ≠ ⊤ := by
  rw [lintegral_mellin_heckeOddSignedLatticeMass K r hr J delta (by linarith)]
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (heckeSignedGammaMass_ne_top K σ) (ENNReal.natCast_ne_top _))
    (tsum_subtype_positive_chiFourIdealWeight_ne_top K _ delta hσ)

end UnitDistance.NumberFieldAnalysis
