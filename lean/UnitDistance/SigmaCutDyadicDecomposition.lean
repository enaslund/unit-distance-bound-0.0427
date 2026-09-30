module

public import UnitDistance.SigmaCutDyadic
public import UnitDistance.PadicTwoGlobalMapSurjective

@[expose] public section
set_option backward.privateInPublic true


/-! The full actual dyadic decomposition subgroup has exactly the constructed
D32 image in the arithmetic cut, and in every quotient retaining M. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace UnitDistance.ArithmeticProP.SigmaCut
open ProCGroups.Presentations
open PadicTwoGlobalMap

variable (s : Fin 5 → Source)
  (hgen : closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : Source)))=
    (sigmaRelationKernel : Subgroup Source))

def dyadicMap : Dyadic.D →ₜ* Quotient s := Classical.choose (dyadic_map s hgen)
theorem dyadicMap_injective : Function.Injective (dyadicMap s hgen) :=
  (Classical.choose_spec (dyadic_map s hgen)).1
theorem dyadicMap_commuting : (dyadicMap s hgen).comp Dyadic.ArithmeticPresentation.model=
    (projection s).comp SigmaDyadic.toSigmaFree :=
  (Classical.choose_spec (dyadic_map s hgen)).2.1
theorem dyadicMap_retained : (retained s).toMonoidHom.comp (dyadicMap s hgen).toMonoidHom=
    SigmaDyadic.retainedDyadic :=
  (Classical.choose_spec (dyadic_map s hgen)).2.2

theorem dyadicMap_arithmetic (r : SigmaDyadic.LocalSource) :
    dyadicMap s hgen (Dyadic.ArithmeticPresentation.model r)=
      arithmeticProjection s hgen (toGlobal (SigmaDyadic.localPresentation r)) := by
  have h := congrArg (fun f : SigmaDyadic.LocalSource →ₜ* Quotient s => f r) (dyadicMap_commuting s hgen)
  change dyadicMap s hgen (Dyadic.ArithmeticPresentation.model r)=projection s (SigmaDyadic.toSigmaFree r) at h
  rw [h,←arithmeticProjection_free s hgen,SigmaDyadic.commuting_square_apply]

def dyadicDecompositionMap : PrimeCompletion.AbsoluteDecomposition prime →ₜ* Quotient s :=
  (arithmeticProjection s hgen).comp (SigmaUnramified.decompositionMap prime)

/-- Every element of the fixed absolute decomposition subgroup is represented
by the actual local free presentation, and conversely. -/
theorem dyadic_decomposition_range : (dyadicDecompositionMap s hgen).toMonoidHom.range=
    (dyadicMap s hgen).toMonoidHom.range := by
  apply le_antisymm
  · rintro _ ⟨d,rfl⟩
    obtain ⟨σ,rfl⟩ := decomposition_surjective d
    obtain ⟨r,hr⟩ := SigmaDyadic.localPresentation_surjective (PadicTwoMaximalProTwo.projection σ)
    refine ⟨Dyadic.ArithmeticPresentation.model r,?_⟩
    change dyadicMap s hgen (Dyadic.ArithmeticPresentation.model r)=dyadicDecompositionMap s hgen (decomposition σ)
    rw [dyadicMap_arithmetic,hr,toGlobal_projection]
    rfl
  · rintro _ ⟨d,rfl⟩
    obtain ⟨r,rfl⟩ := Dyadic.ArithmeticPresentation.model_surjective d
    obtain ⟨σ,hσ⟩ := PadicTwoMaximalProTwo.projection_surjective (SigmaDyadic.localPresentation r)
    refine ⟨decomposition σ,?_⟩
    change dyadicDecompositionMap s hgen (decomposition σ)=dyadicMap s hgen (Dyadic.ArithmeticPresentation.model r)
    rw [dyadicMap_arithmetic,←hσ,toGlobal_projection]
    rfl

theorem dyadic_decomposition_card : Nat.card (dyadicDecompositionMap s hgen).toMonoidHom.range=32 := by
  rw [dyadic_decomposition_range]
  have he := MonoidHom.ofInjective (dyadicMap_injective s hgen)
  rw [←Nat.card_congr he.toEquiv,Nat.card_eq_fintype_card,Dyadic.D.card]

variable {H : Type*} [Group H] (q : Quotient s →* H)

theorem dyadic_finite_range :
    (q.comp (dyadicDecompositionMap s hgen).toMonoidHom).range=
      (q.comp (dyadicMap s hgen).toMonoidHom).range := by
  rw [MonoidHom.range_comp,MonoidHom.range_comp,dyadic_decomposition_range]

theorem dyadic_finiteMap_injective (r : H →* RetainedQuadratic.Q)
    (hr : r.comp q=(retained s).toMonoidHom) :
    Function.Injective (q.comp (dyadicMap s hgen).toMonoidHom) := by
  intro x y h
  apply SigmaDyadic.retainedDyadic_injective
  rw [←DFunLike.congr_fun (dyadicMap_retained s hgen) x,
    ←DFunLike.congr_fun (dyadicMap_retained s hgen) y]
  change retained s (dyadicMap s hgen x)=retained s (dyadicMap s hgen y)
  have hc (z : Quotient s) : r (q z)=retained s z := DFunLike.congr_fun hr z
  rw [←hc,←hc]
  exact congrArg r h

/-- Every finite quotient retaining M has exact dyadic decomposition order32. -/
theorem dyadic_finite_decomposition_card (r : H →* RetainedQuadratic.Q)
    (hr : r.comp q=(retained s).toMonoidHom) :
    Nat.card (q.comp (dyadicDecompositionMap s hgen).toMonoidHom).range=32 := by
  rw [dyadic_finite_range]
  have he := MonoidHom.ofInjective (dyadic_finiteMap_injective s hgen q r hr)
  rw [←Nat.card_congr he.toEquiv,Nat.card_eq_fintype_card,Dyadic.D.card]

end UnitDistance.ArithmeticProP.SigmaCut
