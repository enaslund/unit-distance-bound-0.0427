module

public import UnitDistance.SigmaRetainedInertia
public import UnitDistance.SigmaCutDyadicInertia
public import UnitDistance.DyadicIntrinsicBaseInertia
public import UnitDistance.ArithmeticDyadicInertiaCards

@[expose] public section
set_option backward.privateInPublic true


/-! Exact order eight of the actual dyadic inertia image in the retained
field and in every arithmetic cut quotient retaining that field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open ArithmeticDyadic LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra
local instance dyadicCardRationalAlgebra : Algebra RationalBase LocalField :=
  PrimeCompletion.targetAlgebra rationalPrime LocalField
local instance dyadicCardRationalFinite : Module.Finite RationalBase LocalField :=
  PrimeCompletion.targetFinite rationalPrime LocalField
local instance dyadicCardRationalGalois : IsGalois RationalBase LocalField :=
  PrimeCompletion.targetGalois rationalPrime LocalField
local instance dyadicCardNormed : NontriviallyNormedField LocalField := intrinsicNormedField
local instance dyadicCardValuative : ValuativeRel LocalField := intrinsicValuativeRel
local instance dyadicCardLocal : IsNonarchimedeanLocalField LocalField := intrinsicLocalField
local instance dyadicCardQpExtension : Valuation.HasExtension (ValuativeRel.valuation ℚ_[2])
    (ValuativeRel.valuation LocalField) := intrinsicHasExtension
local instance dyadicCardCompatible : (PadicFiniteGalois.target 2 LocalField).valuation.Compatible :=
  PadicFiniteGalois.target_intrinsicCompatible 2 LocalField
local instance dyadicCardBaseExtension : Valuation.HasExtension (ValuativeRel.valuation RationalBase)
    (ValuativeRel.valuation LocalField) := PrimeCompletion.targetHasExtension rationalPrime LocalField
local instance dyadicCardBaseIntegerAlgebra : Algebra 𝒪[RationalBase] LocalField :=
  Algebra.ofSubsemiring (ValuativeRel.valuation RationalBase).integer
local instance dyadicCardBaseIntegral : IsIntegralClosure 𝒪[LocalField] 𝒪[RationalBase] LocalField :=
  localCompleteDVF_integerRing_isIntegralClosure RationalBase LocalField

/-- Actual absolute dyadic inertia has exactly eight images in the retained field. -/
theorem retained_dyadic_inertia_card : Nat.card SigmaCut.retainedDyadicInertiaMap.range=8 := by
  rw [SigmaCut.retainedDyadicInertiaMap,sigmaRetainedModel_inertia_card]
  let f : LocalField →ₐ[RationalBase] SeparableClosure RationalBase := IsSepClosed.lift
  rw [PrimeCompletion.inertiaRestriction_card_eq_baseChange rationalPrime
    ArithmeticRetained.RetainedField sigmaRetainedAbsoluteEmbedding f,
    finiteAbsoluteInertiaImage_eq_residueInertia]
  change Nat.card rationalBaseInertia=8
  rw [rationalBaseInertia_card,actual_residueDegree_inertia_card.2]

namespace SigmaCut
open ProCGroups.Presentations

/-- Exact inertia order eight in every cut quotient still mapping to M. -/
theorem dyadic_finite_inertia_card (s : Fin 5 → Source)
    (hgen : closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : Source)))=
      (sigmaRelationKernel : Subgroup Source))
    {H : Type*} [Group H] (q : Quotient s →* H)
    (r : H →* RetainedQuadratic.Q) (hr : r.comp q=(retained s).toMonoidHom) :
    Nat.card (q.comp (dyadicInertiaMap s hgen)).range=8 := by
  rw [dyadic_finite_inertia_card_eq_retained s hgen q r hr,retained_dyadic_inertia_card]

end SigmaCut
end UnitDistance.ArithmeticProP
