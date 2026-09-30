module

public import UnitDistance.ChosenPrimeInertiaMap

@[expose] public section
set_option backward.privateInPublic true

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open NumberField IsDedekindDomain
open scoped ValuativeRel NNReal
namespace UnitDistance.PrimeCompletion
open ArithmeticProP LocalClassFieldTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
attribute [local instance] primeFact baseRationalAlgebra
variable (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
variable (p : Nat.Primes) (j : M →ₐ[ℚ] AlgebraicClosure ℚ)
local instance inertiaCardFinite : Module.Finite (Base p) (chosenLocalField M (place p)) :=
  chosenFinitePlaceLocalizedFiniteDimensional (K:=ℚ) (L:=M) (place p)
local instance inertiaCardGalois : IsGalois (Base p) (chosenLocalField M (place p)) :=
  chosenFinitePlaceLocalizedIsGalois (K:=ℚ) (L:=M) (place p)
variable (f : chosenLocalField M (place p) →ₐ[Base p] SeparableClosure (Base p))

/-- Chosen global inertia has the same finite image size as the genuine local inertia. -/
theorem inertiaRestriction_card_eq_chosenLocal :
    Nat.card (inertiaRestriction p M j).range=
      Nat.card (finiteAbsoluteInertiaImage (Base p) (chosenLocalField M (place p)) f) := by
  let I := (localResidueDegree (Base p)).toMonoidHom.ker
  let a : I →* Gal(SeparableClosure (Base p)/ℚ) :=
    (AlgEquiv.restrictScalarsHom ℚ).comp I.subtype
  have hc := GaloisEmbedding.restriction_image_card_eq
    ((absoluteEmbedding p).comp j) (chosenLocalRationalEmbedding M p f) a
  have hleft : ((GaloisEmbedding.restriction ((absoluteEmbedding p).comp j)).toMonoidHom.comp a).range=
      (inertiaRestriction p M j).range := by
    rw [inertiaRestriction_range]
    change ((localRestriction p M j).comp I.subtype).range=I.map (localRestriction p M j)
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  have hright : ((GaloisEmbedding.restriction (chosenLocalRationalEmbedding M p f)).toMonoidHom.comp a).range=
      (finiteAbsoluteInertiaImage (Base p) (chosenLocalField M (place p)) f).map
        (chosenLocalRestriction M (place p)) := by
    apply le_antisymm
    · rintro _ ⟨σ,rfl⟩
      refine ⟨finiteAbsoluteRestriction (Base p) (chosenLocalField M (place p)) f σ.val,
        ⟨σ.val,σ.property,rfl⟩,?_⟩
      exact DFunLike.congr_fun (chosenLocalRestriction_absolute_commuting M p f) σ.val
    · rintro _ ⟨τ,⟨σ,hσ,hτ⟩,rfl⟩
      refine ⟨⟨σ,hσ⟩,?_⟩
      change (GaloisEmbedding.restriction (chosenLocalRationalEmbedding M p f))
        ((AlgEquiv.restrictScalarsHom ℚ) σ)=chosenLocalRestriction M (place p) τ
      rw [←hτ]
      exact (DFunLike.congr_fun (chosenLocalRestriction_absolute_commuting M p f) σ).symm
  exact (congrArg (fun H : Subgroup Gal(M/ℚ) => Nat.card H) hleft).symm.trans
    (hc.trans ((congrArg (fun H : Subgroup Gal(M/ℚ) => Nat.card H) hright).trans
      (Subgroup.card_map_of_injective
        (K:=finiteAbsoluteInertiaImage (Base p) (chosenLocalField M (place p)) f)
        (chosenLocalRestriction_injective M (place p)))))

end UnitDistance.PrimeCompletion
