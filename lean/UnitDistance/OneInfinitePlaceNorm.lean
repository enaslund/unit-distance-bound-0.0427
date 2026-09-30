module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.HasseNormPrinciple

@[expose] public section
set_option backward.privateInPublic true


/-! A cyclic norm over a base with one infinite place is detected by finite
places alone: the actual global Artin product eliminates the last place.
The global reciprocity and cyclic Hasse norm endpoints are actual proved dependencies. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField BigOperators IsMulCommutative
namespace UnitDistance.ArithmeticProP
open GlobalClassFieldTheory.Reciprocity GlobalClassFieldTheory.ClassFieldAxiom

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsAbelianGalois K L]

/-- For a principal idele over a field with a single infinite place, finite
local norm conditions imply the remaining infinite local norm condition. -/
theorem infinite_local_norm_of_finite_local_norms
    [Subsingleton (InfinitePlace K)] (x : Kˣ)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K x) ∈
        chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v)
    (v : InfinitePlace K) :
    IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K x) ∈
      infiniteTensorNormSubgroup (K := K) (L := L) v := by
  have hf : ∀ w : HeightOneSpectrum (𝓞 K),
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) w
        (IdeleGroup.finiteComponent w (IdeleGroup.principalIdele K x)) = 1 := by
    intro w
    change IdeleGroup.finiteComponent w (IdeleGroup.principalIdele K x) ∈
      (chosenFinitePlaceArtinMonoidHom (K := K) (L := L) w).ker
    rw [chosenFinitePlaceArtinMonoidHom_ker]
    exact hfin w
  have hp := chosenLocalArtin_product_principalIdele (K := K) (L := L) x
  rw [finprod_eq_one_of_forall_eq_one hf,mul_one,Fintype.prod_subsingleton _ v] at hp
  rw [← chosenInfinitePlaceArtinMonoidHom_ker]
  exact hp

/-- For a cyclic extension over a base with one infinite place, a field unit
is a global field norm whenever it is a local norm at every finite place. -/
theorem global_norm_of_finite_local_norms
    [Subsingleton (InfinitePlace K)] [IsCyclic Gal(L/K)] (x : Kˣ)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K x) ∈
        chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v) :
    x ∈ globalFieldNormSubgroup K L := by
  rw [hasseNormPrinciple_cyclic K L]
  change IdeleGroup.principalIdele K x ∈
    allPlaceLocalNormCondition (K := K) (L := L)
  refine ⟨Subgroup.mem_iInf.mpr hfin,Subgroup.mem_iInf.mpr ?_⟩
  intro v
  change IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K x) ∈
    infiniteTensorNormSubgroup (K := K) (L := L) v
  exact infinite_local_norm_of_finite_local_norms K L x hfin v

end UnitDistance.ArithmeticProP
