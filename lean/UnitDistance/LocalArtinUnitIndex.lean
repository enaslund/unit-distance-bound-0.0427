module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation
public import Mathlib.Data.ZMod.QuotientGroup

@[expose] public section
set_option backward.privateInPublic true


/-! The index of the actual local Artin image of valuation-ring units. -/
noncomputable section
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory

private theorem index_map_kernel_symm_add
    {A B C : Type*} [AddCommGroup A] [AddGroup B] [AddGroup C]
    (f : A →+ B) (g : A →+ C) (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (f.ker.map g).index = (g.ker.map f).index := by
  rw [AddSubgroup.index_map, g.range_eq_top_of_surjective hg, AddSubgroup.index_top, mul_one]
  rw [← AddSubgroup.index_comap_of_surjective _ hf, AddSubgroup.comap_map_eq, sup_comm]

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The actual local Artin image of valuation-ring units has index equal to
the actual residue-field degree, for an arbitrary finite Galois local extension. -/
theorem localArtin_integerUnits_range_index :
    ((localArtinMonoidHom K L).comp (integerUnitsToFieldUnits K)).range.index =
      Module.finrank 𝓀[K] 𝓀[L] := by
  let a := MonoidHom.toAdditive (localArtinMonoidHom K L)
  let v := valuationMap K
  have ha : Function.Surjective a := localArtinMonoidHom_surjective K L
  have hker : a.ker = (MonoidHom.toAdditive (normUnits K L)).range := by
    exact congrArg Subgroup.toAddSubgroup (localArtinMonoidHom_ker K L)
  rw [← Subgroup.index_toAddSubgroup]
  change (a.comp (additiveIntegerUnitsToFieldUnits K)).range.index = _
  rw [AddMonoidHom.range_comp, additiveIntegerUnitsToFieldUnits_range_eq_ker_valuationMap]
  rw [index_map_kernel_symm_add v a (valuationMap_surjective K) ha, hker,
    ← AddMonoidHom.range_comp]
  rw [valuationMap_comp_normUnits_range_eq_zmultiples_of_isGalois K L,
    Int.index_zmultiples, Int.natAbs_natCast]

end UnitDistance.ArithmeticProP
