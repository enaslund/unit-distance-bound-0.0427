module

public import UnitDistance.TensorBaseChangeH2
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.FiniteGaloisTowerUnitsH2
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionMap

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite-place specialization of restriction/localization, using
the canonical map between adic completions at primes lying over one another. -/
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct
namespace UnitDistance.ArithmeticProP

variable (K F L : Type) [Field K] [NumberField K] [Field F] [NumberField F]
variable [Field L] [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
variable (v : HeightOneSpectrum (𝓞 K))
variable (W : {W : HeightOneSpectrum (𝓞 F) // finitePlaceBelow (K := K) W = v})

local instance : Algebra K (W.1.adicCompletion F) :=
  ((algebraMap F (W.1.adicCompletion F)).comp (algebraMap K F)).toAlgebra
local instance : IsScalarTower K F (W.1.adicCompletion F) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The canonical adic completion map as an algebra homomorphism over K. -/
def finitePlaceCompletionAlgHom :
    v.adicCompletion K →ₐ[K] W.1.adicCompletion F :=
  { finitePlaceAdicCompletionMap K F v W with
    commutes' := fun x => finitePlaceAdicCompletionMap_coe K F v W x }

/-- The concrete field-unit restriction agrees with the public tower map. -/
theorem fieldUnitsRestrictionH2_eq_tower :
    fieldUnitsRestrictionH2 K F L =
      ClassFieldTower.Cohomology.finiteGaloisTowerUnitsH2Restriction K F L := rfl

/-- A field-unit H² class locally zero at a base finite place remains zero
at every specified place above it after restricting to the intermediate field. -/
theorem finiteFieldUnitsTensorRestriction_eq_zero_of_eq_zero
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x = 0) :
    (fieldUnitsTensorH2 F L (W.1.adicCompletion F)).hom
      ((ClassFieldTower.Cohomology.finiteGaloisTowerUnitsH2Restriction K F L).hom x) = 0 := by
  exact fieldUnitsTensorRestriction_eq_zero_of_eq_zero K F L
    (v.adicCompletion K) (W.1.adicCompletion F)
    (finitePlaceCompletionAlgHom K F v W) x hx

end UnitDistance.ArithmeticProP
