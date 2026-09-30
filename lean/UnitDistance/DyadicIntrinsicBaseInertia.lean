module

public import UnitDistance.ArithmeticDyadicIntrinsic
public import UnitDistance.IntrinsicInertiaBaseChange
public import UnitDistance.RationalPrimeCompletionValuation

@[expose] public section
set_option backward.privateInPublic true


/-! The retained dyadic inertia group is unchanged when Q₂ is identified
with the actual rational norm completion used by absolute decomposition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped ValuativeRel
namespace UnitDistance.ArithmeticDyadic
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra
abbrev rationalPrime : Nat.Primes := ⟨2,Nat.prime_two⟩
abbrev RationalBase := PrimeCompletion.Base rationalPrime
local instance dyadicRationalAlgebra : Algebra RationalBase LocalField :=
  PrimeCompletion.targetAlgebra rationalPrime LocalField
local instance dyadicRationalFinite : Module.Finite RationalBase LocalField :=
  PrimeCompletion.targetFinite rationalPrime LocalField
local instance dyadicRationalGalois : IsGalois RationalBase LocalField :=
  PrimeCompletion.targetGalois rationalPrime LocalField
local instance dyadicBaseNormed : NontriviallyNormedField LocalField := intrinsicNormedField
local instance dyadicBaseValuative : ValuativeRel LocalField := intrinsicValuativeRel
local instance dyadicBaseLocal : IsNonarchimedeanLocalField LocalField := intrinsicLocalField
local instance dyadicBaseQpExtension : Valuation.HasExtension (ValuativeRel.valuation ℚ_[2])
    (ValuativeRel.valuation LocalField) := intrinsicHasExtension
local instance dyadicBaseQpIntegral : IsIntegralClosure 𝒪[LocalField] 𝒪[ℚ_[2]] LocalField := intrinsicIntegralClosure
local instance dyadicBaseCompatible : (PadicFiniteGalois.target 2 LocalField).valuation.Compatible :=
  PadicFiniteGalois.target_intrinsicCompatible 2 LocalField
local instance dyadicBaseExtension : Valuation.HasExtension (ValuativeRel.valuation RationalBase)
    (ValuativeRel.valuation LocalField) := PrimeCompletion.targetHasExtension rationalPrime LocalField
local instance dyadicBaseIntegerAlgebra : Algebra 𝒪[RationalBase] LocalField :=
  Algebra.ofSubsemiring (ValuativeRel.valuation RationalBase).integer
local instance dyadicBaseIntegral : IsIntegralClosure 𝒪[LocalField] 𝒪[RationalBase] LocalField :=
  localCompleteDVF_integerRing_isIntegralClosure RationalBase LocalField

def rationalBaseInertia : Subgroup Gal(LocalField/RationalBase) :=
  (galoisGroupResidueAlgEquivHomOfIsIntegralClosure RationalBase LocalField).ker

theorem rationalBaseInertia_iff (σ : Gal(LocalField/RationalBase)) :
    σ∈rationalBaseInertia ↔ PrimeCompletion.galoisEquiv rationalPrime LocalField σ∈inertia := by
  rw [←intrinsicInertia_eq]
  exact ArithmeticProP.intrinsicInertia_iff_of_same_action RationalBase ℚ_[2] LocalField
    σ (PrimeCompletion.galoisEquiv rationalPrime LocalField σ) (fun _ => rfl)

theorem rationalBaseInertia_map : rationalBaseInertia.map
    (PrimeCompletion.galoisEquiv rationalPrime LocalField).toMonoidHom=inertia := by
  ext σ
  constructor
  · rintro ⟨τ,hτ,rfl⟩
    exact (rationalBaseInertia_iff τ).mp hτ
  · intro hσ
    obtain ⟨τ,rfl⟩ := (PrimeCompletion.galoisEquiv rationalPrime LocalField).surjective σ
    exact ⟨τ,(rationalBaseInertia_iff τ).mpr hσ,rfl⟩

theorem rationalBaseInertia_card : Nat.card rationalBaseInertia=Nat.card inertia := by
  rw [←rationalBaseInertia_map]
  exact (Subgroup.card_map_of_injective (PrimeCompletion.galoisEquiv rationalPrime LocalField).injective).symm

end UnitDistance.ArithmeticDyadic
