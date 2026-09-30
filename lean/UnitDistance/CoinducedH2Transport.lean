module

public import UnitDistance.CoinducedH2Evaluation

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
open CategoryTheory
namespace UnitDistance.ArithmeticProP
variable {R G : Type} [CommRing R] [Group G] (H : Subgroup G) (A : Rep R H)

/-- Actual evaluation remains injective on H² after any explicitly supplied
isomorphism with the coinduced representation. -/
theorem coindModelEvaluationH2_injective
    (W : Rep R G) (e : W ≅ Rep.coind H.subtype A) :
    Function.Injective
      (groupCohomology.map H.subtype
        ((Rep.resFunctor H.subtype).map e.hom ≫ coindEvaluationRepHom H A) 2).hom := by
  have he : Function.Injective
      (groupCohomology.map (MonoidHom.id G) e.hom 2).hom :=
    ((groupCohomology.functor R G 2).mapIso e).toLinearEquiv.injective
  have hc : groupCohomology.map H.subtype
        ((Rep.resFunctor H.subtype).map e.hom ≫ coindEvaluationRepHom H A) 2 =
      groupCohomology.map (MonoidHom.id G) e.hom 2 ≫
        groupCohomology.map H.subtype (coindEvaluationRepHom H A) 2 := by
    exact groupCohomology.map_comp (MonoidHom.id G) H.subtype
      e.hom (coindEvaluationRepHom H A) 2
  rw [hc]
  exact (coindEvaluationH2_injective H A).comp he

end UnitDistance.ArithmeticProP
