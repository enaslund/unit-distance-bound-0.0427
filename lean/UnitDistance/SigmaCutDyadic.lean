module

public import UnitDistance.SigmaCut
public import UnitDistance.SigmaDyadicRetainedDiagram

@[expose] public section
set_option backward.privateInPublic true


/-! Literal membership of all six local dyadic cuts in the actual global
cut, and the resulting retained order-thirty-two local subgroup. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP.SigmaCut
open ProCGroups ProCGroups.Presentations

@[simp] theorem local_x : SigmaDyadic.toSigmaFree Dyadic.ArithmeticPresentation.x=dyadicX :=
  SigmaDyadic.toSigmaFree_generator 1
@[simp] theorem local_y : SigmaDyadic.toSigmaFree Dyadic.ArithmeticPresentation.y=dyadicY :=
  SigmaDyadic.toSigmaFree_generator 0
@[simp] theorem local_z : SigmaDyadic.toSigmaFree Dyadic.ArithmeticPresentation.z=dyadicZ := by
  simp only [Dyadic.ArithmeticPresentation.z,map_mul,SigmaDyadic.toSigmaFree_generator]
  rfl

theorem quadratic_mem_kernel (s : Fin 5 → Source) (i : Fin 16) : quadratics i∈kernel s :=
  subset_closedNormalClosure _ (Or.inl (Or.inl ⟨i,rfl⟩))
theorem cubic_mem_kernel (s : Fin 5 → Source) : cubical∈kernel s :=
  subset_closedNormalClosure _ (Or.inl (Or.inr rfl))
theorem deep_mem_kernel (s : Fin 5 → Source) (i : Fin 10) : deep s i∈kernel s :=
  subset_closedNormalClosure _ (Or.inr ⟨i,rfl⟩)

/-- All six local cuts are among the literal global twenty-seven words. -/
theorem dyadic_cuts_mem (s : Fin 5 → Source) (r : SigmaDyadic.LocalSource)
    (hr : r∈Dyadic.ArithmeticPresentation.cuts) : SigmaDyadic.toSigmaFree r∈kernel s := by
  obtain ⟨i,hi,rfl⟩ := hr
  change SigmaDyadic.toSigmaFree.toMonoidHom
    (Dyadic.Presentation.literalRelations Dyadic.ArithmeticPresentation.x
      Dyadic.ArithmeticPresentation.y Dyadic.ArithmeticPresentation.z i)∈_
  rw [Dyadic.Presentation.map_literalRelations]
  change Dyadic.Presentation.literalRelations
    (SigmaDyadic.toSigmaFree Dyadic.ArithmeticPresentation.x)
    (SigmaDyadic.toSigmaFree Dyadic.ArithmeticPresentation.y)
    (SigmaDyadic.toSigmaFree Dyadic.ArithmeticPresentation.z) i∈_
  rw [local_x,local_y,local_z]
  fin_cases i
  · exact quadratic_mem_kernel s 11
  · exact False.elim (hi rfl)
  · exact quadratic_mem_kernel s 12
  · exact quadratic_mem_kernel s 13
  · exact cubic_mem_kernel s
  · exact deep_mem_kernel s 0
  · exact deep_mem_kernel s 1

/-- The true global arithmetic relation kernel lies in the cut whenever the
proved six-relator arithmetic presentation is provided. -/
theorem arithmetic_kernel_le (s : Fin 5 → Source)
    (hgen : closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : Source)))=
      (sigmaRelationKernel : Subgroup Source)) :
    (sigmaRelationKernel : Subgroup Source)≤kernel s := by
  rw [←hgen]
  apply closedNormalClosure_le_closed_normal (kernel_closed s)
  rintro r ⟨i,rfl⟩
  exact original_mem_kernel s i

/-- Actual injected D32 after all twenty-seven global cuts. -/
theorem dyadic_map (s : Fin 5 → Source)
    (hgen : closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : Source)))=
      (sigmaRelationKernel : Subgroup Source)) :
    ∃f : Dyadic.D →ₜ* Quotient s,Function.Injective f ∧
      f.comp Dyadic.ArithmeticPresentation.model=(projection s).comp SigmaDyadic.toSigmaFree ∧
      (retained s).toMonoidHom.comp f.toMonoidHom=SigmaDyadic.retainedDyadic := by
  apply SigmaDyadic.exists_injective_dyadic_map (projection s) ?_ ?_
    (retained s).toMonoidHom (retained_projection s)
  · intro r hr
    exact (QuotientGroup.eq_one_iff r).mpr (arithmetic_kernel_le s hgen hr)
  · intro r hr
    exact (QuotientGroup.eq_one_iff _).mpr (dyadic_cuts_mem s r hr)

/-- Actual surjection from the arithmetic Galois group to the cut quotient. -/
def arithmeticProjection (s : Fin 5 → Source)
    (hgen : closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : Source)))=
      (sigmaRelationKernel : Subgroup Source)) : SigmaGroup →ₜ* Quotient s :=
  (ProCGroups.QuotientGroup.liftₜ (sigmaRelationKernel : Subgroup Source) (projection s)
    (fun r hr => (QuotientGroup.eq_one_iff r).mpr (arithmetic_kernel_le s hgen hr))).comp
      ⟨sigmaFreeQuotientEquiv.symm.toMulEquiv.toMonoidHom,sigmaFreeQuotientEquiv.symm.continuous⟩

@[simp] theorem arithmeticProjection_free (s : Fin 5 → Source) (hgen) (r : Source) :
    arithmeticProjection s hgen (sigmaFreeMap r)=projection s r := by
  rw [←sigmaFreeQuotientEquiv_mk r]
  simp only [arithmeticProjection,ContinuousMonoidHom.coe_comp,Function.comp_apply]
  change (QuotientGroup.lift (sigmaRelationKernel : Subgroup Source) (projection s).toMonoidHom
    (fun r hr => (QuotientGroup.eq_one_iff r).mpr (arithmetic_kernel_le s hgen hr)))
      (sigmaFreeQuotientEquiv.symm (sigmaFreeQuotientEquiv _))=projection s r
  rw [sigmaFreeQuotientEquiv.symm_apply_apply]
  rfl

theorem arithmeticProjection_surjective (s : Fin 5 → Source) (hgen) :
    Function.Surjective (arithmeticProjection s hgen) := by
  intro q
  obtain ⟨r,rfl⟩ := projection_surjective s q
  exact ⟨sigmaFreeMap r,arithmeticProjection_free s hgen r⟩

end UnitDistance.ArithmeticProP.SigmaCut
