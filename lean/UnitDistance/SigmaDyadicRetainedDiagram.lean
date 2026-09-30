module

public import UnitDistance.DyadicArithmeticPresentation
public import UnitDistance.SigmaDyadicFreeMap
public import UnitDistance.RetainedDyadicLifts

@[expose] public section
set_option backward.privateInPublic true


/-! The actual local cut maps injectively to every global quotient that
retains the constructed number field M. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace UnitDistance.SigmaDyadic
open ArithmeticProP ProCGroups ProCGroups.ProC

def retainedLocal : LocalSource →ₜ* RetainedQuadratic.Q :=
  sigmaFreeRetainedMap.comp toSigmaFree

theorem retainedLocal_bases :
    (retainedLocal Dyadic.ArithmeticPresentation.x).base=RetainedQuadratic.binaryVector 7 2 ∧
    (retainedLocal Dyadic.ArithmeticPresentation.y).base=RetainedQuadratic.binaryVector 7 53 ∧
    (retainedLocal Dyadic.ArithmeticPresentation.z).base=RetainedQuadratic.binaryVector 7 89 := by
  simpa only [retainedLocal,ContinuousMonoidHom.coe_comp,Function.comp_apply,Dyadic.ArithmeticPresentation.x,Dyadic.ArithmeticPresentation.y,Dyadic.ArithmeticPresentation.z,map_mul,
    toSigmaFree_generator] using retained_basis_base

def retainedDyadic : Dyadic.D →* RetainedQuadratic.Q :=
  RetainedQuadratic.dyadicMapOfLifts (retainedLocal Dyadic.ArithmeticPresentation.x) (retainedLocal Dyadic.ArithmeticPresentation.y) (retainedLocal Dyadic.ArithmeticPresentation.z)

theorem retainedDyadic_x : retainedDyadic Dyadic.D.x=retainedLocal Dyadic.ArithmeticPresentation.x :=
  RetainedQuadratic.dyadicMapOfLifts_x _ _ _ retainedLocal_bases.1
theorem retainedDyadic_y : retainedDyadic Dyadic.D.y=retainedLocal Dyadic.ArithmeticPresentation.y :=
  RetainedQuadratic.dyadicMapOfLifts_y _ _ _ retainedLocal_bases.2.1
theorem retainedDyadic_z : retainedDyadic Dyadic.D.z=retainedLocal Dyadic.ArithmeticPresentation.z :=
  RetainedQuadratic.dyadicMapOfLifts_z _ _ _ retainedLocal_bases.2.2

theorem retainedDyadic_injective : Function.Injective retainedDyadic :=
  RetainedQuadratic.dyadicMapOfLifts_injective _ _ _

theorem retainedDyadic_comp_model : retainedDyadic.comp Dyadic.ArithmeticPresentation.model.toMonoidHom=
    retainedLocal.toMonoidHom := by
  have hQ : HasPGroupOpenNormalBasis 2 RetainedQuadratic.Q :=
    HasOpenNormalBasisInClass.of_finite_discrete (FiniteGroupClass.pGroup_formation 2).quotientClosed
      ⟨inferInstance,ClassTwo.GroupModel.isTwoGroup RetainedQuadratic.cocycle⟩
  apply (FiniteFreeProTwo.isFree 3).hom_ext hQ
    ((continuous_of_discreteTopology : Continuous retainedDyadic).comp Dyadic.ArithmeticPresentation.model.continuous)
    retainedLocal.continuous
  intro i
  change retainedDyadic (Dyadic.ArithmeticPresentation.model (FiniteFreeProTwo.generator 3 i))=
    retainedLocal (FiniteFreeProTwo.generator 3 i)
  rw [Dyadic.ArithmeticPresentation.model_generator]
  fin_cases i
  · exact retainedDyadic_y
  · exact retainedDyadic_x
  · change retainedDyadic (Dyadic.D.y*Dyadic.D.z)=retainedLocal (FiniteFreeProTwo.generator 3 2)
    rw [map_mul,retainedDyadic_y,retainedDyadic_z]
    have hy : (retainedLocal Dyadic.ArithmeticPresentation.y)^2=1 := by
      rw [←retainedDyadic_y,←map_pow,Dyadic.D.y_sq,map_one]
    rw [show retainedLocal Dyadic.ArithmeticPresentation.z=
      retainedLocal Dyadic.ArithmeticPresentation.y*retainedLocal (FiniteFreeProTwo.generator 3 2) from map_mul _ _ _]
    rw [←mul_assoc,←pow_two,hy,one_mul]

/-- Every actual cut quotient retaining M has an injected local D32.
The only local vanishing conditions are precisely the six displayed cuts;
the seventh relation is the independently proved genuine arithmetic one. -/
theorem exists_injective_dyadic_map
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (q : GlobalSource →ₜ* H)
    (hrel : ∀r∈sigmaRelationKernel,q r=1)
    (hcuts : ∀r∈Dyadic.ArithmeticPresentation.cuts,q (toSigmaFree r)=1)
    (ρ : H →* RetainedQuadratic.Q)
    (hρ : ∀g,ρ (q g)=sigmaFreeRetainedMap g) :
    ∃f : Dyadic.D →ₜ* H,Function.Injective f ∧
      f.comp Dyadic.ArithmeticPresentation.model=q.comp toSigmaFree ∧ ρ.comp f.toMonoidHom=retainedDyadic := by
  obtain ⟨f,hf⟩ := Dyadic.ArithmeticPresentation.factors_through_model (q.comp toSigmaFree) genuineRelation
    genuineRelation_detector (hrel _ genuineRelation_mem_global_kernel) hcuts
  have hdiag : ρ.comp f.toMonoidHom=retainedDyadic := by
    apply MonoidHom.ext
    intro d
    obtain ⟨g,rfl⟩ := Dyadic.ArithmeticPresentation.model_surjective d
    have hfg := congrArg (fun ψ : LocalSource →ₜ* H => ψ g) hf
    change ρ (f (Dyadic.ArithmeticPresentation.model g))=retainedDyadic (Dyadic.ArithmeticPresentation.model g)
    rw [show f (Dyadic.ArithmeticPresentation.model g)=q (toSigmaFree g) from hfg,hρ]
    exact (DFunLike.congr_fun retainedDyadic_comp_model g).symm
  refine ⟨f,?_,hf,hdiag⟩
  intro d e h
  apply retainedDyadic_injective
  rw [←DFunLike.congr_fun hdiag d,←DFunLike.congr_fun hdiag e]
  exact congrArg ρ h

end UnitDistance.SigmaDyadic
