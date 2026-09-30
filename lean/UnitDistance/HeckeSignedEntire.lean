module

public import UnitDistance.HeckeSignedThetaIdentities
public import UnitDistance.HeckeSignedMellinAgreement

@[expose] public section
set_option backward.privateInPublic true


/-! Entire continuation of the actual imprimitive sign-character completion.
The same actual class theta whose Mellin integral is the norm-character series
is a finite dyadic combination of parity lattice theta functions. -/
noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units DedekindResidue MeasureTheory
open NumberField.mixedEmbedding
open scoped Real Classical nonZeroDivisors Topology
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis
open UnitDistance.OddNormDyadic
variable (K : Type*) [Field K] [NumberField K]

abbrev HeckeSignedDyadicIndex := ClassGroup (𝓞 K) × Finset (DyadicPrime K)

def heckeSignedDyadicIndices : Finset (HeckeSignedDyadicIndex K) :=
  Finset.univ ×ˢ (Finset.univ : Finset (DyadicPrime K)).powerset

def heckeSignedDyadicLattice (i : HeckeSignedDyadicIndex K) :
    Submodule ℤ (EuclideanSpace ℝ (index K)) :=
  idealZLattice K (FractionalIdeal.mk0 K (dyadicSubideal K (heckeOddClassRep K i.1) i.2))

instance (i : HeckeSignedDyadicIndex K) : DiscreteTopology (heckeSignedDyadicLattice K i) :=
  inferInstanceAs (DiscreteTopology (idealZLattice K
    (FractionalIdeal.mk0 K (dyadicSubideal K (heckeOddClassRep K i.1) i.2))))

instance (i : HeckeSignedDyadicIndex K) : IsZLattice ℝ (heckeSignedDyadicLattice K i) :=
  inferInstanceAs (IsZLattice ℝ (idealZLattice K
    (FractionalIdeal.mk0 K (dyadicSubideal K (heckeOddClassRep K i.1) i.2))))

def heckeSignedDyadicCoefficient (i : HeckeSignedDyadicIndex K) : ℂ :=
  (chiFourReal (Ideal.absNorm (heckeOddClassRep K i.1 : Ideal (𝓞 K))) : ℂ) *
    ((torsionOrder K : ℝ)⁻¹ : ℂ) * (-1:ℂ)^i.2.card

def heckeSignedDyadicScale (i : HeckeSignedDyadicIndex K) : ℝ :=
  heckeOddClassScale K (heckeOddClassRep K i.1)

theorem heckeSignedDyadicScale_pos (i : HeckeSignedDyadicIndex K) :
    0 < heckeSignedDyadicScale K i := heckeOddClassScale_pos K _

/-- Equality of the actual complete signed theta with a finite scaled parity-theta sum. -/
theorem heckeOddSignedTotalG_eq_finiteParityUnitAverage
    (r : K) (hr : r^2=7) {t : ℝ} (ht : 0 < t) :
    (heckeOddSignedTotalG K t : ℂ) =
      finiteHeckeParityUnitAverage K (heckeRealParity K) (heckeSignedDyadicIndices K)
        (heckeSignedDyadicLattice K) (heckeSignedDyadicCoefficient K) (heckeSignedDyadicScale K) t := by
  unfold heckeOddSignedTotalG finiteHeckeParityUnitAverage heckeSignedDyadicIndices
  rw [Complex.ofReal_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro C hC
  rw [heckeOddSignedClassG, Complex.ofReal_mul,
    heckeOddSignedG_eq_finiteParityUnitAverage K r hr (heckeOddClassRep K C)
      (heckeOddClassRep_odd K C) (mul_pos (heckeOddClassScale_pos K _) ht)]
  simp only [finiteHeckeParityUnitAverage, one_mul, Finset.mul_sum,
    heckeSignedDyadicLattice, heckeSignedDyadicCoefficient, heckeSignedDyadicScale]
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem heckeRealParity_has_odd (hreal : 0 < nrRealPlaces K) :
    ∃ i, heckeRealParity K i = true := by
  obtain ⟨w⟩ : Nonempty {w : InfinitePlace K // IsReal w} := Fintype.card_pos_iff.mp hreal
  exact ⟨Sum.inl w, rfl⟩

theorem mellin_heckeOddSignedTotalG_eq_finite
    (r : K) (hr : r^2=7) :
    mellin (fun t => (heckeOddSignedTotalG K t : ℂ)) =
      mellin (finiteHeckeParityUnitAverage K (heckeRealParity K) (heckeSignedDyadicIndices K)
        (heckeSignedDyadicLattice K) (heckeSignedDyadicCoefficient K) (heckeSignedDyadicScale K)) := by
  funext s
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [heckeOddSignedTotalG_eq_finiteParityUnitAverage K r hr ht]

/-- The actual imprimitive signed theta has an entire Mellin transform. -/
theorem differentiable_mellin_heckeOddSignedTotalG
    (r : K) (hr : r^2=7) (hreal : 0 < nrRealPlaces K) :
    Differentiable ℂ (mellin (fun t => (heckeOddSignedTotalG K t : ℂ))) := by
  rw [mellin_heckeOddSignedTotalG_eq_finite K r hr]
  exact differentiable_mellin_finiteHeckeParityUnitAverage K (heckeRealParity K)
    (heckeRealParity_has_odd K hreal) (heckeSignedDyadicIndices K)
    (heckeSignedDyadicLattice K) (heckeSignedDyadicCoefficient K) (heckeSignedDyadicScale K)
    (fun i _ => heckeSignedDyadicScale_pos K i)

/-- Entire continuation of the actual sign-character completion, with no supplied
analytic continuation or theta-admissibility hypothesis. -/
theorem differentiable_heckeSignedCompletion
    (r : K) (hr : r^2=7) (hreal : 0 < nrRealPlaces K) :
    Differentiable ℂ (heckeSignedCompletion K) := by
  unfold heckeSignedCompletion
  exact ((differentiable_mellin_heckeOddSignedTotalG K r hr hreal).comp
    (differentiable_id.div_const (2 : ℂ))).const_mul _

end UnitDistance.NumberFieldAnalysis
