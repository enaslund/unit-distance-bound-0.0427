module

public import UnitDistance.FieldUnitsIdeleDetection
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.FiniteFieldUnitsIdelePrimitive
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite-place detection of field-unit H² over a totally complex base.
Finite support and all discarded-block conditions are discharged arithmetically. -/
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.Martinet.Shafarevich

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local instance : MulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L) :=
  RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
local instance (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L/K) (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.adicCompletion K)

/-- Only finitely many chosen finite-place completions ramify. -/
theorem chosenFinitePlaceIsUnramified_of_notMem_ramifiedBaseFinitePlaces
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ ramifiedBaseFinitePlaces (K := K) (L := L)) :
    ChosenFinitePlaceIsUnramified (K := K) (L := L) v := by
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt (K := K) (L := L) v
  by_contra hram
  apply hv
  rw [mem_ramifiedBaseFinitePlaces_iff]
  exact ⟨finitePlaceExtensionCentre (K := K) (L := L) v
      (chosenFinitePlaceExtension (L := L) v),
    finitePlaceExtensionCentre_liesOver (K := K) (L := L) v
      (chosenFinitePlaceExtension (L := L) v), hram⟩

/-- A totally complex base has no ramified infinite-place block. -/
theorem chosenInfinitePlace_isUnramified_of_totallyComplex [IsTotallyComplex K]
    (v : InfinitePlace K) :
    (chosenInfinitePlaceAbove (L := L) v).IsUnramified K :=
  InfinitePlace.isUnramified_iff.mpr (Or.inr (IsTotallyComplex.isComplex _))

/-- Finite tensor localizations detect all actual field-unit H² classes
for a finite Galois p-extension over a totally complex number field. -/
theorem fieldUnitsH2_eq_zero_of_finite_localizations [IsTotallyComplex K]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p Gal(L/K))
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K),
      (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x = 0) : x = 0 := by
  have hcoeff : fieldUnitsIdeleHom K L = finiteFieldUnitsIdeleRepHom K L := by
    ext y
    rfl
  have hI : Function.Injective
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (fieldUnitsIdeleHom K L)).hom := by
    rw [hcoeff]
    exact finiteFieldUnitsIdeleH2Map_injective_of_isPGroup K L hP
  exact fieldUnitsH2_eq_zero_of_idele_injective K L hI
    (ramifiedBaseFinitePlaces (K := K) (L := L))
    (chosenFinitePlaceIsUnramified_of_notMem_ramifiedBaseFinitePlaces K L)
    (chosenInfinitePlace_isUnramified_of_totallyComplex K L) x hx

end UnitDistance.ArithmeticProP
