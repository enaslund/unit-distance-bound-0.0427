module

public import UnitDistance.SigmaCutInfinite

@[expose] public section
set_option backward.privateInPublic true


/-! Actual arithmetic quotient and finite conjugacy detector for extracting
number fields from the proved infinite twenty-seven-word cut. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP.SigmaCut

abbrev CubicRange := cubicDetector.toMonoidHom.range
instance cubicRangeFintype : Fintype CubicRange := Fintype.ofFinite _

def cubicRangeMap : Source →ₜ* CubicRange where
  toMonoidHom := cubicDetector.toMonoidHom.rangeRestrict
  continuous_toFun := cubicDetector.continuous_toFun.subtype_mk _

/-- The finite detector is the actual image of the cubic Magnus map. -/
def cubic : ActualQuotient →ₜ* CubicRange :=
  ProCGroups.QuotientGroup.liftₜ (kernel actualExtra) cubicRangeMap (by
    intro g hg
    apply Subtype.ext
    exact (retained_and_cubic actualExtra).2.1 hg)

@[simp] theorem cubic_projection (g : Source) :
    cubic (projection actualExtra g)=cubicRangeMap g := rfl

theorem cubic_surjective : Function.Surjective cubic := by
  rintro ⟨q,g,hg⟩
  refine ⟨projection actualExtra g,?_⟩
  apply Subtype.ext
  exact hg

/-- The actual global Galois group maps onto the detector through the cut. -/
def arithmeticCubic (hgen : ArithmeticPresentation) : SigmaGroup →ₜ* CubicRange :=
  cubic.comp (arithmeticProjection actualExtra hgen)

theorem arithmeticCubic_surjective (hgen : ArithmeticPresentation) :
    Function.Surjective (arithmeticCubic hgen) :=
  cubic_surjective.comp (arithmeticProjection_surjective actualExtra hgen)

@[simp] theorem arithmeticCubic_free (hgen : ArithmeticPresentation) (g : Source) :
    arithmeticCubic hgen (sigmaFreeMap g)=cubicRangeMap g := by
  change cubic (arithmeticProjection actualExtra hgen (sigmaFreeMap g))=_
  rw [arithmeticProjection_free,cubic_projection]

theorem arithmeticCubic_kernel (hgen : ArithmeticPresentation) :
    (arithmeticProjection actualExtra hgen).toMonoidHom.ker ≤
      (arithmeticCubic hgen).toMonoidHom.ker := by
  intro g hg
  change cubic (arithmeticProjection actualExtra hgen g)=1
  rw [show arithmeticProjection actualExtra hgen g=1 from hg,map_one]

theorem arithmeticCubic_conjugacy_index (hgen : ArithmeticPresentation) :
    4096 ≤ (Subgroup.centralizer
      ({arithmeticCubic hgen sigmaComplexConjugation} : Set CubicRange)).index := by
  rw [←sigmaFreeConjugation_image,arithmeticCubic_free]
  exact (retained_and_cubic actualExtra).2.2

theorem arithmeticProjection_retained (hgen : ArithmeticPresentation) (g : SigmaGroup) :
    retained actualExtra (arithmeticProjection actualExtra hgen g)=sigmaRetainedModelMap g := by
  obtain ⟨g,rfl⟩ := sigmaFreeMap_surjective g
  rw [arithmeticProjection_free,retained_projection]
  rfl

/-- The quotient kernel fixes the specified actual embedded retained field. -/
theorem arithmeticProjection_retained_kernel (hgen : ArithmeticPresentation) :
    (arithmeticProjection actualExtra hgen).toMonoidHom.ker ≤
      retainedFieldEmbeddingMaximalSigmaProTwo.fieldRange.fixingSubgroup := by
  intro g hg
  have hm : sigmaRetainedModelMap g=1 := by
    rw [←arithmeticProjection_retained hgen g]
    rw [show arithmeticProjection actualExtra hgen g=1 from hg,map_one]
  have hr : sigmaRetainedRestriction g=1 := by
    apply sigmaRetainedModelEquiv.symm.injective
    exact hm.trans (sigmaRetainedModelEquiv.symm.map_one).symm
  rw [IntermediateField.mem_fixingSubgroup_iff]
  rintro y ⟨x,rfl⟩
  have h := GaloisEmbedding.restriction_commutes
    retainedFieldEmbeddingMaximalSigmaProTwo g x
  change retainedFieldEmbeddingMaximalSigmaProTwo (sigmaRetainedRestriction g x)=_ at h
  rw [hr] at h
  exact h.symm

end UnitDistance.ArithmeticProP.SigmaCut
