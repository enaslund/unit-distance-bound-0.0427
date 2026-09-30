module

public import UnitDistance.ChosenPrimeInertiaCard
public import UnitDistance.LocalInertiaFiniteImage

@[expose] public section
set_option backward.privateInPublic true


/-! The actual absolute inertia image has the size of actual ideal inertia. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open NumberField IsDedekindDomain
open scoped ValuativeRel NNReal
namespace UnitDistance.PrimeCompletion
open ArithmeticProP LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
attribute [local instance] primeFact baseRationalAlgebra
variable (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
variable (p : Nat.Primes) (j : M →ₐ[ℚ] AlgebraicClosure ℚ)

local instance inertiaImageFinite : Module.Finite (Base p) (chosenLocalField M (place p)) :=
  chosenFinitePlaceLocalizedFiniteDimensional (K:=ℚ) (L:=M) (place p)
local instance inertiaImageGalois : IsGalois (Base p) (chosenLocalField M (place p)) :=
  chosenFinitePlaceLocalizedIsGalois (K:=ℚ) (L:=M) (place p)

local instance inertiaImageSeparable : Algebra.IsSeparable (Base p) (chosenLocalField M (place p)) :=
  @IsGalois.to_isSeparable (Base p) _ (chosenLocalField M (place p)) _ _ (inertiaImageGalois M p)

/-- The actual absolute inertia image has exactly the size of actual ideal inertia. -/
theorem inertiaRestriction_card_eq_chosenIdeal :
    Nat.card (inertiaRestriction p M j).range=
      Nat.card ((chosenLocalPrime M (place p)).asIdeal.inertia Gal(M/ℚ)) := by
  let f := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure
    (Base p) (chosenLocalField M (place p))
  have h1 := inertiaRestriction_card_eq_chosenLocal M p j f
  have h2 := congrArg (fun H : Subgroup Gal(chosenLocalField M (place p)/Base p) => Nat.card H)
    (finiteAbsoluteInertiaImage_eq_residueInertia (Base p) (chosenLocalField M (place p)) f)
  have h3 := Subgroup.card_map_of_injective
    (K := (galoisGroupResidueAlgEquivHomOfIsIntegralClosure
      (chosenLocalBase (place p)) (chosenLocalField M (place p))).ker)
    (chosenLocalRestriction_injective M (place p))
  have h4 := congrArg (fun H : Subgroup Gal(M/ℚ) => Nat.card H)
    (chosenLocal_inertia_map M (place p))
  exact h1.trans (h2.trans (h3.symm.trans h4))

end UnitDistance.PrimeCompletion
