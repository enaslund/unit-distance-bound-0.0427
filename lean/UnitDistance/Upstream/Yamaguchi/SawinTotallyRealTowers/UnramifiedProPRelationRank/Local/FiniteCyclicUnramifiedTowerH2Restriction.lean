/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.FiniteCyclicBaseUnitsH2
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.FiniteGaloisTowerBaseUnitsH2Naturality
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.FiniteGaloisTowerUnitsH2
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.UnramifiedBaseUnitsH2
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ValuativeRel

namespace LocalClassFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ClassFieldTower.Cohomology

/-- A cyclic lower-field H² class becomes zero after inflation to an
unramified relative extension whose degree divides the lower ramification index. -/
theorem finiteCyclicTowerUnitsH2_inflation_restriction_eq_zero
    (K L M N : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field N] [Algebra K N] [ValuativeRel N] [TopologicalSpace N]
    [IsNonarchimedeanLocalField N]
    [Field L] [Field M]
    [Algebra K L] [Algebra L N] [IsScalarTower K L N]
    [Algebra K M] [Algebra M N] [IsScalarTower K M N]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [FiniteDimensional L N] [IsGalois L N]
    [FiniteDimensional K M] [IsGalois K M] [IsCyclic Gal(M/K)]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Valuation.HasExtension (ValuativeRel.valuation L) (ValuativeRel.valuation N)]
    [Module.Finite 𝒪[L] 𝒪[N]] [IsUnramifiedValuedExtension L N]
    (hd : Module.finrank L N ∣ (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K]) :
    finiteGaloisTowerUnitsH2Inflation K M N ≫ finiteGaloisTowerUnitsH2Restriction K L N = 0 := by
  have h := finiteGaloisTowerBaseUnitsH2_inflation_restriction K N L M
  rw [finiteTowerBaseUnitsH2Map_eq_zero_of_finrank_dvd_ramificationIdx K L N hd,
    comp_zero] at h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha⟩ := finiteCyclicBaseUnitsH2Map_surjective K M x
  have hvalue := congrArg (fun f :
      groupCohomology (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) 2 ⟶
        groupCohomology (Rep.ofAlgebraAutOnUnits L N) 2 => f.hom a) h
  change (finiteGaloisTowerUnitsH2Restriction K L N).hom
      ((finiteGaloisTowerUnitsH2Inflation K M N).hom
        ((finiteGaloisBaseUnitsH2Map K M).hom a)) = 0 at hvalue
  change (finiteGaloisTowerUnitsH2Restriction K L N).hom
      ((finiteGaloisTowerUnitsH2Inflation K M N).hom x) = 0
  rw [ha] at hvalue
  exact hvalue

end LocalClassFieldTheory
