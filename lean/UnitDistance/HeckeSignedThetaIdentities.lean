module

public import UnitDistance.HeckeSignedBochner
public import UnitDistance.HeckeDyadicInclusionExclusion
public import UnitDistance.HeckeFiniteMellin

@[expose] public section
set_option backward.privateInPublic true


/-! Actual unit periodicity, independence of the fundamental box, and the
integrated finite dyadic inclusion–exclusion identity. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Real Classical nonZeroDivisors ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis
open UnitDistance.OddNormDyadic
variable (K : Type*) [Field K] [NumberField K]

theorem continuous_heckeParityTheta_heckeWeights (p : index K → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ (index K))) [DiscreteTopology L] [IsZLattice ℝ L]
    {t : ℝ} (ht : 0 < t) :
    Continuous (fun u : logSpace K => heckeParityTheta p L (placeWeights K (heckeWeights K t u))) := by
  rw [continuous_iff_continuousAt]
  intro u
  have ha : ∀ i, 0 < placeWeights K (heckeWeights K t u) i := by
    rintro (w | ⟨w,j⟩) <;> exact heckeWeights_pos K ht u w
  have hw : Continuous (fun u : logSpace K => placeWeights K (heckeWeights K t u)) := by
    apply continuous_pi
    rintro (w | ⟨w,j⟩) <;> exact continuous_heckeWeights_log K t w
  exact (continuousAt_heckeParityTheta p L ha).comp (x := u) hw.continuousAt

theorem integrableOn_heckeParityTheta_heckeWeights (p : index K → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ (index K))) [DiscreteTopology L] [IsZLattice ℝ L]
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : logSpace K => heckeParityTheta p L (placeWeights K (heckeWeights K t u)))
      (heckeUnitBox K) := by
  obtain ⟨R, hR, hbox⟩ := exists_box_coord_bound K
  let m : ℝ := Real.exp (-(2*(Fintype.card (InfinitePlace K))*R)) * t^((1:ℝ)/Module.finrank ℚ K)
  have hm : 0 < m := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht _)
  let C : ℝ := ∑' v : L, Real.exp (-Real.pi * ∑ i, (m/2)*((v : EuclideanSpace ℝ (index K)) i)^2)
  have hC : IntegrableOn (fun _ : logSpace K => C) (heckeUnitBox K) :=
    integrableOn_const (heckeUnitBox_measure_ne_top K)
  apply hC.mono' (continuous_heckeParityTheta_heckeWeights K p L ht).aestronglyMeasurable
  apply (ae_restrict_iff' (measurableSet_heckeUnitBox K)).mpr
  apply Filter.Eventually.of_forall
  intro u hu
  apply norm_heckeParityTheta_le_gaussian p L hm
  rintro (w | ⟨w,j⟩) <;> exact le_heckeWeights_of_bounded K hR (hbox u hu) ht.le w

/-- Actual unit multiplication permutes the filtered signed lattice sum. -/
theorem heckeOddSignedTheta_periodic_unit (r : K) (hr : r^2=7)
    (J : (Ideal (𝓞 K))⁰) (t : ℝ) (u : logSpace K) (epsilon : (𝓞 K)ˣ) :
    heckeOddSignedTheta K J t (u+logEmbedding K (Additive.ofMul epsilon)) =
      heckeOddSignedTheta K J t u := by
  unfold heckeOddSignedTheta
  conv_rhs => rw [← Equiv.tsum_eq (unitMulLatticeEquiv K (FractionalIdeal.mk0 K J) epsilon)]
  apply tsum_congr
  intro v
  obtain ⟨a, ha, hva⟩ := (mem_idealZLattice K (FractionalIdeal.mk0 K J) _).mp v.property
  have hcoe : ((unitMulLatticeEquiv K (FractionalIdeal.mk0 K J) epsilon v :
      idealZLattice K (FractionalIdeal.mk0 K J)) : EuclideanSpace ℝ (index K)) =
      embeddingCoords K (algebraMap (𝓞 K) K (epsilon : 𝓞 K)*a) := by
    change mulCoords K _ (v : EuclideanSpace ℝ (index K)) = _
    rw [← hva, mulCoords_embeddingCoords]
  rw [hcoe, ← hva, heckeOddSignedTerm_unit_mul K r hr]

theorem heckeOddSignedTheta_periodic (r : K) (hr : r^2=7)
    (J : (Ideal (𝓞 K))⁰) (t : ℝ) :
    ∀ l ∈ unitLattice K, ∀ u, heckeOddSignedTheta K J t (l+u) = heckeOddSignedTheta K J t u := by
  intro l hl u
  obtain ⟨b, hb, heq⟩ := Submodule.mem_map.mp hl
  rw [add_comm, ← heq]
  exact heckeOddSignedTheta_periodic_unit K r hr J t u (Additive.toMul b)

/-- Bochner version of the actual unit-box basis-independence theorem. -/
theorem setIntegral_unitBox_swap_complex (f : logSpace K → ℂ)
    (hf : ∀ l ∈ unitLattice K, ∀ u, f (l+u)=f u) :
    (∫ u in heckeUnitBox K, f u) =
      ∫ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ), f u := by
  have h1 := ZSpan.isAddFundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ) volume
  have h2 := ZSpan.isAddFundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ) volume
  rw [(Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis_span ℝ] at h1
  rw [(basisUnitLattice K).ofZLatticeBasis_span ℝ] at h2
  haveI : VAddInvariantMeasure (unitLattice K) (logSpace K) volume :=
    inferInstanceAs (VAddInvariantMeasure (unitLattice K).toAddSubgroup (logSpace K) volume)
  refine h1.setIntegral_eq h2 (f := f) (fun l u => ?_)
  rw [Submodule.vadd_def, vadd_eq_add]
  exact hf (l : logSpace K) l.property u

/-- The actual signed averaged theta is a finite combination of the actual parity
averages whose entire Mellin transforms have already been constructed. -/
theorem heckeOddSignedG_eq_finiteParityUnitAverage
    (r : K) (hr : r^2=7) (J : (Ideal (𝓞 K))⁰)
    (hJ : Odd (Ideal.absNorm (J : Ideal (𝓞 K)))) {t : ℝ} (ht : 0 < t) :
    (heckeOddSignedG K J t : ℂ) = finiteHeckeParityUnitAverage K (heckeRealParity K)
      (Finset.univ : Finset (DyadicPrime K)).powerset
      (fun S => idealZLattice K (FractionalIdeal.mk0 K (dyadicSubideal K J S)))
      (fun S => ((torsionOrder K : ℝ)⁻¹ : ℂ)*(-1:ℂ)^S.card) (fun _ => 1) t := by
  have hbox := setIntegral_unitBox_swap_complex K (fun u => (heckeOddSignedTheta K J t u : ℂ))
    (fun l hl u => congrArg Complex.ofReal (heckeOddSignedTheta_periodic K r hr J t l hl u))
  have hpoint (u : logSpace K) : (heckeOddSignedTheta K J t u : ℂ) =
      ∑ S ∈ (Finset.univ : Finset (DyadicPrime K)).powerset,
        (-1:ℂ)^S.card * heckeParityTheta (heckeRealParity K)
          (idealZLattice K (FractionalIdeal.mk0 K (dyadicSubideal K J S)))
          (placeWeights K (heckeWeights K t u)) := by
    rw [heckeOddSignedTheta, Complex.ofReal_tsum]
    exact heckeOddSignedTerm_tsum_inclusionExclusion K J hJ ht u
  unfold heckeOddSignedG
  rw [Complex.ofReal_mul, ← integral_complex_ofReal, ← hbox]
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun S _ =>
    (integrableOn_heckeParityTheta_heckeWeights K (heckeRealParity K)
      (idealZLattice K (FractionalIdeal.mk0 K (dyadicSubideal K J S))) ht).const_mul ((-1:ℂ)^S.card))]
  simp_rw [integral_const_mul]
  simp only [finiteHeckeParityUnitAverage, heckeParityUnitAverage, one_mul, Finset.mul_sum, mul_assoc, Complex.ofReal_inv]

end UnitDistance.NumberFieldAnalysis
