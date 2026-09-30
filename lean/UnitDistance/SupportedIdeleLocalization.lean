module

public import UnitDistance.SupportedIdeleCocycles
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.SupportedSPlaceFactorsH2Localization

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite tensor coordinates of supported-idele H² localization. -/
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.Martinet.Shafarevich ClassFieldTower.Cohomology

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local instance : MulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L) :=
  RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
local instance (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction Gal(L/K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := L) S
local instance (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L/K) (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.adicCompletion K)

/-- The upstream supported localization is literally evaluation of the
included idele class at the indicated finite tensor block. -/
theorem supportedIdeleH2_localization_eq
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : groupCohomology (supportedIdeleRep K L S) 2)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) :
    supportedSPlaceH2Localization K L S x v =
      (ideleFiniteH2 K L v.1).hom
        ((groupCohomology.map (MonoidHom.id Gal(L/K))
          (supportedIdeleInclusionRepHom K L S) 2).hom x) := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    simp only [supportedSPlaceH2Localization, sPlaceFactorsH2Localization,
      AddMonoidHom.comp_apply, piMultiplicativeH2Evaluation,
      prodMultiplicativeH2Evaluation, AddMonoidHom.prod_apply,
      LinearMap.toAddMonoidHom_coe, ideleFiniteH2,
      groupCohomology.H2π_comp_map_apply]
    change (groupCohomology.map (MonoidHom.id Gal(L/K)) _ 2).hom
      ((groupCohomology.map (MonoidHom.id Gal(L/K)) _ 2).hom
        ((groupCohomology.map (MonoidHom.id Gal(L/K)) _ 2).hom
          ((groupCohomology.map (MonoidHom.id Gal(L/K)) _ 2).hom
            (groupCohomology.H2π (supportedIdeleRep K L S) c)))) = _
    simp only [groupCohomology.H2π_comp_map_apply]
    congr 1

/-- Finite tensor evaluations detect idele H² once the discarded blocks
are unramified. Finite support is constructed from a cocycle representative. -/
theorem ideleH2_eq_zero_of_finite_localizations
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₀ →
      ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K,
      (chosenInfinitePlaceAbove (L := L) v).IsUnramified K)
    (x : groupCohomology
      (Rep.ofMulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L)) 2)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), (ideleFiniteH2 K L v).hom x = 0) : x = 0 := by
  obtain ⟨S, hS, y, hy⟩ := exists_supportedIdele_H2 K L S₀ x
  have hy0 : y = 0 := by
    apply supportedSPlaceH2Localization_injective K L S
      (fun v hv => hfin v (fun hv₀ => hv (hS hv₀))) hinf
    rw [map_zero]
    funext v
    rw [supportedIdeleH2_localization_eq K L S y v, hy]
    exact hx v.1
  rw [hy0, map_zero] at hy
  exact hy.symm

end UnitDistance.ArithmeticProP
