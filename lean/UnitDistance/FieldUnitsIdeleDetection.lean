module

public import UnitDistance.SupportedIdeleLocalization
public import UnitDistance.TensorBaseChangeH2

@[expose] public section
set_option backward.privateInPublic true


/-! Field-unit/idele/tensor compatibility for finite-local H² detection. -/
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct
namespace UnitDistance.ArithmeticProP

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local instance : MulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L) :=
  RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
local instance (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L/K) (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.adicCompletion K)

/-- Actual principal-idele embedding, with Mathlib's field-unit action. -/
def fieldUnitsIdeleHom : Rep.ofAlgebraAutOnUnits K L ⟶
    Rep.ofMulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L) := by
  apply Rep.ofHom
  refine ⟨(RelativeIdeleGroup.principalIdele K L).toAdditive.toIntLinearMap, ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  exact congrArg Additive.ofMul
    (RelativeIdeleGroup.smul_principalIdele K L g x.toMul).symm

/-- Principal-idele evaluation equals the literal tensor include-right map. -/
theorem fieldUnitsIdeleHom_finite_factor (v : HeightOneSpectrum (𝓞 K)) :
    fieldUnitsIdeleHom K L ≫ ideleFiniteRepHom K L v =
      fieldUnitsTensorRepHom K L (v.adicCompletion K) := by
  ext z
  apply Units.ext
  rfl

/-- Compatibility-only reduction: an injective global idele map and the
actual unramified-block hypotheses yield finite-local field-unit detection. -/
theorem fieldUnitsH2_eq_zero_of_idele_injective
    (hI : Function.Injective
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (fieldUnitsIdeleHom K L)).hom)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₀ →
      ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K,
      (chosenInfinitePlaceAbove (L := L) v).IsUnramified K)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K),
      (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x = 0) : x = 0 := by
  let C := groupCohomology.functor ℤ Gal(L/K) 2
  have hz : (C.map (fieldUnitsIdeleHom K L)).hom x = 0 := by
    apply ideleH2_eq_zero_of_finite_localizations K L S₀ hfin hinf
    intro v
    have hf := congrArg (fun f => (C.map f).hom x)
      (fieldUnitsIdeleHom_finite_factor K L v)
    rw [Functor.map_comp] at hf
    change (ideleFiniteH2 K L v).hom
      ((C.map (fieldUnitsIdeleHom K L)).hom x) =
        (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x at hf
    exact hf.trans (hx v)
  apply hI
  change (C.map (fieldUnitsIdeleHom K L)).hom x =
    (C.map (fieldUnitsIdeleHom K L)).hom 0
  exact hz.trans (map_zero _).symm

end UnitDistance.ArithmeticProP
